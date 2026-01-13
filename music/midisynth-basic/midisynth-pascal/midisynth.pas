// =====================================================================
// Midisynth, version 2026-01-13
// =====================================================================
// A very simple synthesizer for MIDI files, written in Pascal. It gene-
// rates the sound for each note using additive synthesis of sine waves
// (fundamental and harmonics) enveloped in an ADSR curve. The audio
// signal is then encoded as PCM and packaged as a WAV file. This pro-
// gram requires no dependencies.
//
// This code was created and ported using Gemini 3, so take everything
// with a grain of salt. There may be subtle bugs that are not notice-
// able, or the specifications may not be followed in detail.
//
// Usage:
//   ./midisynth input.mid output.wav
//
// =====================================================================

program MidiSynth;

uses
   SysUtils, Math;

const
   SAMPLE_RATE = 44100;

type
   TEventType = (evtNoteOn, evtNoteOff, evtSetTempo, evtOther);

   // A raw MIDI event
   TMidiEvent = record
      AbsTick: LongWord;
      EvType: TEventType;
      Channel: Integer;
      Note: Integer;
      Velocity: Integer;
      TempoMicros: Integer;
   end;

   // A processed note
   TNote = record
      StartTime: Double;
      Duration: Double;
      MidiKey: Integer;
      Velocity: Integer;
      Channel: Integer;
   end;

   TMidiEventArray = array of TMidiEvent;
   TNoteArray = array of TNote;

var
   Events: TMidiEventArray;
   EventCount: Integer = 0;
   EventCapacity: Integer = 0;

// =====================================================================
// HELPER: READ FILE (BIG ENDIAN)
// =====================================================================

function ReadBE16(var F: File): Word;
var
   Bytes: array[0..1] of Byte;
begin
   BlockRead(F, Bytes, 2);
   Result := (Bytes[0] shl 8) or Bytes[1];
end;

function ReadBE32(var F: File): LongWord;
var
   Bytes: array[0..3] of Byte;
begin
   BlockRead(F, Bytes, 4);
   Result := (LongWord(Bytes[0]) shl 24) or
      (LongWord(Bytes[1]) shl 16) or
      (LongWord(Bytes[2]) shl 8) or Bytes[3];
end;

function ReadVarLen(var F: File): LongWord;
var
   Value: LongWord;
   C: Byte;
begin
   Value := 0;
   repeat
      BlockRead(F, C, 1);
      Value := (Value shl 7) or (C and $7F);
   until (C and $80) = 0;
   Result := Value;
end;

// =====================================================================
// MIDI EVENT MANAGEMENT
// =====================================================================

procedure AddEvent(E: TMidiEvent);
begin
   if EventCount >= EventCapacity then
   begin
      if EventCapacity = 0 then
         EventCapacity := 1024
      else
         EventCapacity := EventCapacity * 2;
      SetLength(Events, EventCapacity);
   end;
   Events[EventCount] := E;
   Inc(EventCount);
end;

// QuickSort for events by AbsTick
procedure SortEvents(L, R: Integer);
var
   I, J: Integer;
   Pivot: LongWord;
   Temp: TMidiEvent;
begin
   if EventCount = 0 then Exit;
   I := L;
   J := R;
   Pivot := Events[(L + R) div 2].AbsTick;
   repeat
      while Events[I].AbsTick < Pivot do Inc(I);
      while Events[J].AbsTick > Pivot do Dec(J);
      if I <= J then
      begin
         Temp := Events[I];
         Events[I] := Events[J];
         Events[J] := Temp;
         Inc(I);
         Dec(J);
      end;
   until I > J;
   if L < J then SortEvents(L, J);
   if I < R then SortEvents(I, R);
end;

// =====================================================================
// MIDI PARSING
// =====================================================================

procedure ParseMidi(const Filename: String; out Division: Word);
var
   F: File;
   ChunkID: array[0..3] of Char;
   ChunkIDStr: String;
   NumTracks: Word;
   TrackLen, Delta, AbsTick, Skip: LongWord;
   TrackStart, TrackEnd: Int64; // CurrentPos removed
   ByteVal, Status, RunningStatus, MetaType: Byte;
   MetaLen: LongWord;
   T: Integer; // I removed
   NoteVal, Vel: Byte;
   TempoBytes: array[0..2] of Byte;
   Ev: TMidiEvent;
begin
   AssignFile(F, Filename);
   {$I-} Reset(F, 1); {$I+}
   if IOResult <> 0 then
   begin
      WriteLn(StdErr, 'Error: Could not open file.');
      Halt(1);
   end;

   // Header
   BlockRead(F, ChunkID, 4);
   ChunkIDStr := ChunkID;
   if ChunkIDStr <> 'MThd' then
   begin
      WriteLn(StdErr, 'Not a valid MIDI file.');
      CloseFile(F);
      Halt(1);
   end;

   ReadBE32(F); // Header Length skip
   ReadBE16(F); // Format skip
   NumTracks := ReadBE16(F);
   Division := ReadBE16(F);

   if (Division and $8000) <> 0 then
   begin
      WriteLn(StdErr, 'Error: SMPTE timecode is not supported.');
      CloseFile(F);
      Halt(1);
   end;

   WriteLn('MIDI Info: ', NumTracks, ' Tracks, Division ', Division);

   for T := 0 to NumTracks - 1 do
   begin
      BlockRead(F, ChunkID, 4);
      ChunkIDStr := ChunkID;
      while ChunkIDStr <> 'MTrk' do
      begin
         Skip := ReadBE32(F);
         Seek(F, FilePos(F) + Skip);
         BlockRead(F, ChunkID, 4);
         ChunkIDStr := ChunkID;
      end;

      TrackLen := ReadBE32(F);
      TrackStart := FilePos(F);
      TrackEnd := TrackStart + TrackLen;
      AbsTick := 0;
      RunningStatus := 0;

      while FilePos(F) < TrackEnd do
      begin
         Delta := ReadVarLen(F);
         AbsTick := AbsTick + Delta;

         BlockRead(F, ByteVal, 1);
         if ByteVal >= $80 then
         begin
            Status := ByteVal;
            RunningStatus := Status;
         end
         else
         begin
            Status := RunningStatus;
            Seek(F, FilePos(F) - 1); // Rewind 1 byte
         end;

         if Status = $FF then // Meta Event
         begin
            BlockRead(F, MetaType, 1);
            MetaLen := ReadVarLen(F);
            
            if (MetaType = $51) and (MetaLen = 3) then // Set Tempo
            begin
               BlockRead(F, TempoBytes, 3);
               Ev.AbsTick := AbsTick;
               Ev.EvType := evtSetTempo;
               Ev.Channel := 0; Ev.Note := 0; Ev.Velocity := 0;
               Ev.TempoMicros := (TempoBytes[0] shl 16) or
                  (TempoBytes[1] shl 8) or TempoBytes[2];
               AddEvent(Ev);
            end
            else if MetaType = $2F then // End of Track
            begin
               Seek(F, TrackEnd);
               Break;
            end
            else
            begin
               Seek(F, FilePos(F) + MetaLen); // Skip
            end;
         end
         else if (Status = $F0) or (Status = $F7) then // SysEx
         begin
            MetaLen := ReadVarLen(F);
            Seek(F, FilePos(F) + MetaLen);
         end
         else if (Status and $F0) = $90 then // Note On
         begin
            BlockRead(F, NoteVal, 1);
            BlockRead(F, Vel, 1);
            Ev.AbsTick := AbsTick;
            if Vel > 0 then
               Ev.EvType := evtNoteOn
            else
               Ev.EvType := evtNoteOff;
            Ev.Channel := Status and $0F;
            Ev.Note := NoteVal;
            Ev.Velocity := Vel;
            Ev.TempoMicros := 0;
            AddEvent(Ev);
         end
         else if (Status and $F0) = $80 then // Note Off
         begin
            BlockRead(F, NoteVal, 1);
            BlockRead(F, Vel, 1);
            Ev.AbsTick := AbsTick;
            Ev.EvType := evtNoteOff;
            Ev.Channel := Status and $0F;
            Ev.Note := NoteVal;
            Ev.Velocity := Vel;
            Ev.TempoMicros := 0;
            AddEvent(Ev);
         end
         else
         begin
            // Other Channel Messages
            if ((Status and $F0) = $C0) or ((Status and $F0) = $D0) then
               Seek(F, FilePos(F) + 1)
            else
               Seek(F, FilePos(F) + 2);
         end;
      end;
   end;
   CloseFile(F);

   // Sorting
   if EventCount > 1 then
      SortEvents(0, EventCount - 1);
end;

// =====================================================================
// CONVERSION TO NOTES
// =====================================================================

function ConvertEventsToNotes(Division: Word;
   out OutTotalDuration: Double): TNoteArray;
var
   Notes: TNoteArray;
   NoteCount: Integer = 0;
   I, C, N: Integer;
   E: TMidiEvent;
   CurrentTime: Double = 0.0;
   CurrentTick: LongWord = 0;
   MicrosPerBeat: Double = 500000.0;
   DeltaTicks: LongWord;
   SecondsPerTick: Double;
   
   // ActiveNotes[Channel][Pitch] = StartTime (-1.0 = inactive)
   ActiveNotes: array[0..15, 0..127] of Double;
   ActiveVels: array[0..15, 0..127] of Integer;
   
   NewNote: TNote;
begin
   SetLength(Notes, EventCount); // Reserve maximum size
   
   for C := 0 to 15 do
      for N := 0 to 127 do
      begin
         ActiveNotes[C, N] := -1.0;
         ActiveVels[C, N] := 0; // Explicit initialization
      end;

   for I := 0 to EventCount - 1 do
   begin
      E := Events[I];
      DeltaTicks := E.AbsTick - CurrentTick;
      
      if DeltaTicks > 0 then
      begin
         SecondsPerTick := (MicrosPerBeat / 1000000.0) / Division;
         CurrentTime := CurrentTime + DeltaTicks * SecondsPerTick;
         CurrentTick := E.AbsTick;
      end;

      if E.EvType = evtSetTempo then
      begin
         MicrosPerBeat := E.TempoMicros;
      end
      else if E.EvType = evtNoteOn then
      begin
         // Retrigger check
         if ActiveNotes[E.Channel, E.Note] >= 0.0 then
         begin
            NewNote.StartTime := ActiveNotes[E.Channel, E.Note];
            NewNote.Duration := CurrentTime - NewNote.StartTime;
            NewNote.MidiKey := E.Note;
            NewNote.Velocity := ActiveVels[E.Channel, E.Note];
            NewNote.Channel := E.Channel;
            if NewNote.Duration > 0 then
            begin
               Notes[NoteCount] := NewNote;
               Inc(NoteCount);
            end;
         end;
         ActiveNotes[E.Channel, E.Note] := CurrentTime;
         ActiveVels[E.Channel, E.Note] := E.Velocity;
      end
      else if E.EvType = evtNoteOff then
      begin
         if ActiveNotes[E.Channel, E.Note] >= 0.0 then
         begin
            NewNote.StartTime := ActiveNotes[E.Channel, E.Note];
            NewNote.Duration := CurrentTime - NewNote.StartTime;
            NewNote.MidiKey := E.Note;
            NewNote.Velocity := ActiveVels[E.Channel, E.Note];
            NewNote.Channel := E.Channel;
            ActiveNotes[E.Channel, E.Note] := -1.0;
            if NewNote.Duration > 0 then
            begin
               Notes[NoteCount] := NewNote;
               Inc(NoteCount);
            end;
         end;
      end;
   end;

   SetLength(Notes, NoteCount); // Shrink to actual size
   OutTotalDuration := CurrentTime + 1.0;
   Result := Notes;
end;

// =====================================================================
// SYNTHESIS AND WAV WRITING
// =====================================================================

procedure WriteWavHeader(var F: File; TotalSamples: Integer);
type
   TWavHeader = packed record
      RIFF: array[0..3] of Char;
      FileSize: LongWord;
      WAVE: array[0..3] of Char;
      fmt: array[0..3] of Char;
      SubChunk1Size: LongWord;
      AudioFormat: Word;
      NumChannels: Word;
      SampleRate: LongWord;
      ByteRate: LongWord;
      BlockAlign: Word;
      BitsPerSample: Word;
      data: array[0..3] of Char;
      DataChunkSize: LongWord;
   end;
var
   H: TWavHeader;
begin
   H.RIFF := 'RIFF';
   H.DataChunkSize := TotalSamples * 2;
   H.FileSize := 36 + H.DataChunkSize;
   H.WAVE := 'WAVE';
   H.fmt := 'fmt ';
   H.SubChunk1Size := 16;
   H.AudioFormat := 1; // PCM
   H.NumChannels := 1; // Mono
   H.SampleRate := SAMPLE_RATE;
   H.BitsPerSample := 16;
   H.ByteRate := SAMPLE_RATE * 2;
   H.BlockAlign := 2;
   H.data := 'data';

   BlockWrite(F, H, SizeOf(H));
end;

function MidiToFreq(Key: Integer): Double;
begin
   Result := 440.0 * Power(2.0, (Key - 69) / 12.0);
end;

procedure SynthesizeAndWrite(const Filename: String;
   Notes: TNoteArray; TotalDuration: Double);
var
   TotalSamples: NativeInt;
   AudioBuffer: array of Single;
   I, OV: Integer; // J removed
   StartS, LenS, EndS, T: NativeInt;
   NoteData: TNote;
   Freq, Amp, TimeInNote, SampleVal, HFreq, Env, RelPhase: Double;
   IsDrum: Boolean;
   Duration, Attack, Release: Double;
   
   Overtones: array[0..3] of Double = (1.0, 0.5, 0.3, 0.1);
   NumOvertones: Integer = 4;
   
   F: File;
   PCMBuffer: array of SmallInt;
   MaxVal, NormFactor: Single;
   Val32: Integer;
begin
   TotalSamples := Round(TotalDuration * SAMPLE_RATE);
   SetLength(AudioBuffer, TotalSamples);
   // Array is initialized with 0.0 by default in FPC (at SetLength)

   WriteLn('Synthesizing ', Length(Notes), ' notes in ',
      TotalSamples, ' samples...');

   Attack := 0.05;
   Release := 0.1;

   for I := 0 to High(Notes) do
   begin
      NoteData := Notes[I];
      IsDrum := (NoteData.Channel = 9); // Channel 10 is index 9
      
      if IsDrum then 
      begin
         Freq := 100.0;
         Duration := 0.05;
      end
      else
      begin
         Freq := MidiToFreq(NoteData.MidiKey);
         Duration := NoteData.Duration;
      end;

      Amp := (NoteData.Velocity / 127.0) * 0.3;

      StartS := Round(NoteData.StartTime * SAMPLE_RATE);
      LenS := Round((Duration + Release) * SAMPLE_RATE);
      EndS := StartS + LenS;

      if EndS > TotalSamples then LenS := TotalSamples - StartS;

      for T := 0 to LenS - 1 do
      begin
         if (StartS + T) >= TotalSamples then Break;

         TimeInNote := T / SAMPLE_RATE;
         SampleVal := 0.0;

         if IsDrum then
         begin
            SampleVal := Sin(2 * PI * Freq * TimeInNote);
         end
         else
         begin
            for OV := 0 to NumOvertones - 1 do
            begin
               HFreq := Freq * (OV + 1);
               if HFreq < (SAMPLE_RATE / 2) then
                  SampleVal := SampleVal +
                     Overtones[OV] * Sin(2 * PI * HFreq * TimeInNote);
            end;
            SampleVal := SampleVal / 1.9;
         end;

         // Envelope
         Env := 1.0;
         if TimeInNote < Attack then
            Env := TimeInNote / Attack
         else if TimeInNote > Duration then
         begin
            RelPhase := TimeInNote - Duration;
            Env := 1.0 - (RelPhase / Release);
            if Env < 0 then Env := 0;
         end;

         AudioBuffer[StartS + T] := AudioBuffer[StartS + T] +
            (SampleVal * Amp * Env);
      end;
   end;

   // Normalize
   MaxVal := 0.0;
   for I := 0 to TotalSamples - 1 do
   begin
      if Abs(AudioBuffer[I]) > MaxVal then
         MaxVal := Abs(AudioBuffer[I]);
   end;

   NormFactor := 32000.0;
   if MaxVal > 0.0 then NormFactor := 32000.0 / MaxVal;
   if NormFactor > 32000.0 then NormFactor := 32000.0;

   SetLength(PCMBuffer, TotalSamples);
   for I := 0 to TotalSamples - 1 do
   begin
      Val32 := Round(AudioBuffer[I] * NormFactor);
      if Val32 > 32767 then Val32 := 32767;
      if Val32 < -32768 then Val32 := -32768;
      PCMBuffer[I] := SmallInt(Val32);
   end;

   // Writing
   AssignFile(F, Filename);
   Rewrite(F, 1);
   if IOResult <> 0 then
   begin
      WriteLn(StdErr, 'Could not write output file.');
      Halt(1);
   end;

   WriteWavHeader(F, TotalSamples);
   BlockWrite(F, PCMBuffer[0], TotalSamples * SizeOf(SmallInt));
   
   CloseFile(F);
   WriteLn('WAV written to: ', Filename);
end;

// =====================================================================
// MAIN
// =====================================================================

var
   InputFile, OutputFile: String;
   Division: Word;
   Notes: TNoteArray;
   TotalDuration: Double;
begin
   if ParamCount < 2 then
   begin
      WriteLn('Usage: ', ParamStr(0), ' <input.mid> <output.wav>');
      Halt(1);
   end;

   InputFile := ParamStr(1);
   OutputFile := ParamStr(2);

   ParseMidi(InputFile, Division);
   Notes := ConvertEventsToNotes(Division, TotalDuration);

   if Length(Notes) = 0 then
      WriteLn('No notes found!')
   else
      SynthesizeAndWrite(OutputFile, Notes, TotalDuration);
end.

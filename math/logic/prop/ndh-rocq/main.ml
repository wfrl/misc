
open Kernel

type token =
| TIdent of string
| TNum of string
| TDot | TComma | TLParen | TRParen
| TTurnstile | TConj | TDisj | TSubj | TEqui | TNeg
| TFalsum | TVerum | TEOF

(* == Scanner == *)

let scan s =
  let n = String.length s in
  let i = ref 0 in
  let line = ref 1 in
  let tokens = ref [] in
  let emit tok = tokens := (tok, !line) :: !tokens in

  let starts prefix =
    let len = String.length prefix in
    !i + len <= n && String.sub s !i len = prefix
  in

  while !i < n do
    let c = s.[!i] in
    if c = '\n' then (incr line; incr i)
    else if c = ' ' || c = '\t' || c = '\r' then incr i
    else if c = '#' then
      (while !i < n && s.[!i] <> '\n' do incr i done)
    else if starts "(*" then
      (i := !i + 2;
      while !i + 1 < n && not (starts "*)") do
        if s.[!i] = '\n' then incr line;
        incr i
      done;
      if !i + 1 < n then i := !i + 2)
    else if starts "⊢" || starts "|-" then
      (emit TTurnstile; i := !i + (if starts "⊢" then 3 else 2))
    else if starts "∧" || starts "/\\" then
      (emit TConj; i := !i + (if starts "∧" then 3 else 2))
    else if starts "∨" || starts "\\/" then
      (emit TDisj; i := !i + (if starts "∨" then 3 else 2))
    else if starts "→" || starts "->" || starts "⇒" || starts "=>" then
      (emit TSubj; i := !i + (if starts "→" || starts "⇒" then 3 else 2))
    else if starts "↔" || starts "<->" || starts "⇔" || starts "<=>" then
      (emit TEqui; i := !i + (if starts "↔" || starts "⇔" then 3 else 3))
    else if starts "¬" || c = '~' then
      (emit TNeg; i := !i + (if starts "¬" then 2 else 1))
    else if starts "⊥" then
      (emit TFalsum; i := !i + (if starts "⊥" then 3 else 3))
    else if c = '&' then (emit TConj; incr i)
    else if c = '|' then (emit TDisj; incr i)
    else if c = '.' then (emit TDot; incr i)
    else if c = ',' then (emit TComma; incr i)
    else if c = '(' then (emit TLParen; incr i)
    else if c = ')' then (emit TRParen; incr i)
    else if (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c = '_' then
      (let start = !i in
      while !i < n && (let ch = s.[!i] in (ch >= 'a' && ch <= 'z') ||
        (ch >= 'A' && ch <= 'Z') || (ch >= '0' && ch <= '9') || ch = '_')
      do
        incr i
      done;
      let id = String.sub s start (!i - start) in
      match id with
      | "falsum" -> emit TFalsum
      | "false"  -> emit TFalsum
      | "verum"  -> emit TVerum
      | "true"   -> emit TVerum
      | "and"    -> emit TConj
      | "or"     -> emit TDisj
      | "not"    -> emit TNeg
      | _        -> emit (TIdent id))
    else if c >= '0' && c <= '9' then (
      let start = !i in
      while !i < n && s.[!i] >= '0' && s.[!i] <= '9' do incr i done;
      emit (TNum (String.sub s start (!i - start))))
    else
      failwith (Printf.sprintf
        "Lexical error in line %d: unexpected char '%c'" !line c)
  done;
  emit TEOF;
  List.rev !tokens

(* == Parser == *)

type pstate = {toks: (token * int) array; mutable pos: int}

let tok_at st = st.toks.(min st.pos (Array.length st.toks - 1))
let cur st = fst (tok_at st)
let cur_line st = snd (tok_at st)
let advance st = st.pos <- st.pos + 1

let expect tok st =
  if cur st = tok then advance st
  else failwith (Printf.sprintf
    "Syntax error in line %d: unexpected token" (cur_line st))

let rec parse_atom st =
  match cur st with
  | TFalsum -> advance st; Falsum
  | TVerum  -> advance st; Verum
  | TIdent id -> advance st; Svar id
  | TLParen ->
      advance st;
      let f = parse_seq st in
      expect TRParen st;
      f
  | _ -> failwith (Printf.sprintf
      "Syntax error in line %d: expected atom" (cur_line st))

and parse_neg st =
  match cur st with
  | TNeg -> advance st; Neg (parse_neg st)
  | _ -> parse_atom st

and parse_conj st =
  let rec loop acc =
    match cur st with
    | TConj -> advance st; loop (Conj (acc, parse_neg st))
    | _ -> acc
  in loop (parse_neg st)

and parse_disj st =
  let rec loop acc =
    match cur st with
    | TDisj -> advance st; loop (Disj (acc, parse_conj st))
    | _ -> acc
  in loop (parse_conj st)

and parse_subj st =
  let lhs = parse_disj st in
  match cur st with
  | TSubj -> advance st; Subj (lhs, parse_subj st)
  | _ -> lhs

and parse_equi st =
  let lhs = parse_subj st in
  match cur st with
  | TEqui -> advance st; Equi (lhs, parse_subj st)
  | _ -> lhs

and parse_seq st =
  let lhs =
    match cur st with
    | TTurnstile -> Verum
    | _ -> parse_equi st
  in
  match cur st with
  | TTurnstile -> advance st; Seq (lhs, parse_seq st)
  | _ -> lhs

let parse_label st: Kernel.label =
  match cur st with
  | TIdent s | TNum s -> advance st; s
  | _ -> failwith (Printf.sprintf
      "Syntax error in line %d: expected label" (cur_line st))

let parse_context st =
  let rec loop acc =
    match cur st with
    | TIdent _ | TNum _ ->
        let l = parse_label st in
        if cur st = TComma then (advance st; loop (l :: acc))
        else l :: acc
    | TTurnstile -> acc
    | _ -> failwith (Printf.sprintf
        "Syntax error in line %d: expected context" (cur_line st))
  in List.rev (loop [])

let parse_statement st =
  let line = cur_line st in
  let lbl = parse_label st in
  expect TDot st;
  let stmt =
    match cur st with
    | TLParen ->
        advance st;
        let f = parse_seq st in
        expect TRParen st;
        Plain f
    | _ ->
        let hyps = parse_context st in
        expect TTurnstile st;
        let f = parse_seq st in
        Hyps (hyps, f)
  in expect TComma st;
  let rule = parse_label st in
  let rec parse_args acc =
    match cur st with
    | TIdent _ | TNum _ -> parse_args (parse_label st :: acc)
    | TDot -> List.rev acc
    | _ -> failwith (Printf.sprintf
        "Syntax error in line %d: expected argument or '.'" (cur_line st))
  in let args = parse_args [] in
  expect TDot st;
  {s_line = line; s_label = lbl; s_stmt = stmt; s_rule = rule; s_args = args}

let parse_all tokens =
  let st = {toks = Array.of_list tokens; pos = 0} in
  let rec loop acc =
    if cur st = TEOF then List.rev acc
    else loop (parse_statement st :: acc)
  in loop []

(* == Error output and main procedure == *)

let string_of_err = function
| EUnknown l -> Printf.sprintf "unknown rule or label '%s'" l
| ECyclic -> "cyclic deduction"
| ENotRule -> "expected a rule/subjunction"
| EArg (r, i) -> Printf.sprintf "rule '%s': argument %d does not match" r i
| EConcl r -> Printf.sprintf "rule '%s': conclusion does not match" r
| ENoSeq l -> Printf.sprintf "label '%s' in context is not a sequence" l

let () =
  if Array.length Sys.argv < 2 then (
    Printf.eprintf "Usage: %s <proofs.txt>\n" Sys.argv.(0);
    exit 1
  );
  let filename = Sys.argv.(1) in
  let content =
    let ic = open_in filename in
    let len = in_channel_length ic in
    let s = really_input_string ic len in
    close_in ic;
    s
  in
  try
    let tokens = scan content in
    let steps = parse_all tokens in
    match verify steps with
    | Inr _bk -> ()
    | Inl (line, e) ->
        Printf.printf "Logic error in line %d:\n%s\n" line (string_of_err e);
        exit 1
  with Failure msg ->
    Printf.printf "%s\n" msg;
    exit 1

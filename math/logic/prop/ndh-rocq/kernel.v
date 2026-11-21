
(* Verified kernel of the proof checker nd for propositional logic

Main theorem:
  verify sts = inr bk implies that every line of bk is valid with
  respect to the classical semantics (Boolean valuations).

Design idea: The matcher bindf is an unverified guesser.
Its result is checked by the kernel using eqv (certifying).
Only apply/inst, eqv, verify_chain, and the bookkeeping are in
the trusted computing base of the proofs. *)

(* == Table of contents ==
   1. Syntax
   2. Semantics
   3. Substitutions and book
   4. Contexts as sets of conjuncts
   5. eqv: syntactic equality modulo sets of conjuncts in contexts
   6. The matcher (may remain unverified)
   7. Errors, status, and checking of a rule application
   8. Proof steps and checking entire proofs
   9. The axioms (prelude) and their validity
  10. The checker and its soundness theorem
  11. Ensuring conservative extension *)

Require Import List String Bool.
Import ListNotations.
Open Scope string_scope.

Require Import Classical_Prop.

Require Extraction.
Extraction Language OCaml.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.
(* Native OCaml strings. ExtrOcamlString, by contrast,
   maps string to char list. *)
Require Import ExtrOcamlNativeString.

(* Efficient equality test. This is an extraction assumption:
   OCaml (=) on strings corresponds to string_dec. The proofs
   are not affected by this. *)
Extract Inlined Constant string_dec => "(=)".

(* == Syntax == *)

Definition ident := string.
Definition label := string.

(* Type of formulas *)
Inductive Fm: Type :=
| Svar  : ident -> Fm     (* Schema variable *)
| Falsum: Fm              (* False formula *)
| Verum : Fm              (* True formula *)
| Neg   : Fm -> Fm        (* Negation *)
| Conj  : Fm -> Fm -> Fm  (* Conjunction *)
| Disj  : Fm -> Fm -> Fm  (* Disjunction *)
| Subj  : Fm -> Fm -> Fm  (* Subjunction *) 
| Equi  : Fm -> Fm -> Fm  (* Equijunction *)
| Seq   : Fm -> Fm -> Fm. (* Sequent *)

Definition form_dec: forall A B: Fm, {A = B} + {A <> B}.
Proof.
  decide equality.
  apply string_dec.
Defined.

(* == Semantics == *)

(* Classical valuations. *)
Definition Valuation := ident -> bool.

Definition Model := Valuation -> ident -> Prop.

(* Generalized satisfaction: each Svar stands for an arbitrary
   predicate over valuations. This is necessary because lines
   may be instantiated as rules. *)
Fixpoint gsat (M: Model) (v: Valuation) (F: Fm): Prop :=
  match F with
  | Svar x   => M v x
  | Falsum   => False
  | Verum    => True
  | Neg A    => ~ gsat M v A
  | Conj A B => gsat M v A /\ gsat M v B
  | Disj A B => gsat M v A \/ gsat M v B
  | Subj A B => gsat M v A -> gsat M v B
  | Equi A B => (gsat M v A <-> gsat M v B)
  | Seq A B  => forall w, gsat M w A -> gsat M w B
  end.

(* The usual classical semantics:
   Svar x is true in v when v x = true. *)
Definition std: Model := fun v x => v x = true.
Definition sat (v: Valuation) (A: Fm): Prop := gsat std v A.

(* Validity in all generalized models. This is the invariant
   for all entries of the book. *)
Definition gvalid (A: Fm): Prop := forall M v, gsat M v A.

(* == Substitutions and book == *)

Fixpoint lookup (x: string) (s: list (string * Fm)): option Fm :=
  match s with
  | nil => None
  | (y, A) :: s' => if string_dec x y then Some A else lookup x s'
  end.

(* Substitution environment (stores the unifier) *)
Definition senv := list (ident * Fm).

(* Already proven theorems *)
Definition book := list (label * Fm).

Definition look (t: senv) (x: ident): Fm :=
  match lookup x t with Some A => A | None => Svar x end.
Arguments look: simpl never.

Fixpoint inst (t: senv) (F: Fm): Fm :=
  match F with
  | Svar x   => look t x
  | Falsum   => Falsum
  | Verum    => Verum
  | Neg A    => Neg (inst t A)
  | Conj A B => Conj (inst t A) (inst t B)
  | Disj A B => Disj (inst t A) (inst t B)
  | Subj A B => Subj (inst t A) (inst t B)
  | Equi A B => Equi (inst t A) (inst t B)
  | Seq A B  => Seq (inst t A) (inst t B)
  end.

Definition variant (M: Model) (t: senv): Model :=
  fun w x => gsat M w (look t x).
Arguments variant: simpl never.

(* Substitution lemma for the generalized semantics. *)
Lemma gsat_inst (t: senv) (M: Model) (F: Fm):
  forall v, gsat M v (inst t F) <-> gsat (variant M t) v F.
Proof.
  induction F as [x | | | A ihA | A ihA B ihB | A ihA B ihB
  | A ihA B ihB | A ihA B ihB | A ihA B ihB];
    intro v; simpl.
  * apply iff_refl.
  * apply iff_refl.
  * apply iff_refl.
  * specialize (ihA v). tauto.
  * specialize (ihA v). specialize (ihB v). tauto.
  * specialize (ihA v). specialize (ihB v). tauto.
  * specialize (ihA v). specialize (ihB v). tauto.
  * specialize (ihA v). specialize (ihB v). tauto.
  * split; intros h w hw.
    - apply (proj1 (ihB w)). apply h. apply (proj2 (ihA w)). exact hw.
    - apply (proj2 (ihB w)). apply h. apply (proj1 (ihA w)). exact hw.
Qed.

Lemma lookup_cons_eq (x: string) (A: Fm) (s: list (string * Fm)):
  lookup x ((x, A) :: s) = Some A.
Proof.
  simpl. destruct (string_dec x x) as [_ | N].
  * reflexivity.
  * exfalso. apply N. reflexivity.
Qed.

Lemma lookup_cons_neq (x y: string) (A: Fm) (s: list (string * Fm)):
  x <> y -> lookup x ((y, A) :: s) = lookup x s.
Proof.
  intro hn. simpl.
  destruct (string_dec x y) as [heq | _].
  * exfalso. apply hn. exact heq.
  * reflexivity.
Qed.

Lemma lookup_in (s: list (string * Fm)):
  forall (x: string) (A: Fm), lookup x s = Some A -> In (x, A) s.
Proof.
  induction s as [| [y g] s ih]; intros x A; simpl.
  * intro h. discriminate h.
  * destruct (string_dec x y) as [hl | hr].
    - intro h. simpl in h. injection h as h1. subst. left. reflexivity.
    - intro h. simpl in h. right. exact (ih x A h).
Qed.

(* Book invariant: all entries are valid in all models. *)
Definition BookOK (bk: book): Prop :=
  forall (l: label) (A: Fm), lookup l bk = Some A -> gvalid A.

Lemma bookok_cons (bk: book) (l: label) (B: Fm):
  BookOK bk -> gvalid B -> BookOK ((l, B) :: bk).
Proof.
  unfold BookOK. intros hbk hB. intros x A.
  destruct (string_dec x l) as [hl | hr].
  * subst x. rewrite lookup_cons_eq. intro h.
    injection h as h1. subst A. exact hB.
  * assert (heq := lookup_cons_neq x l B bk hr).
    intro h. symmetry in heq.
    assert (h1 := eq_trans heq h).
    exact (hbk x A h1).
Qed.

(* == Contexts as sets of conjuncts == *)

Fixpoint conjs (F: Fm): list Fm :=
  match F with
  | Verum => nil
  | Conj A B => app (conjs A) (conjs B)
  | _ => F :: nil
  end.

Definition mem_b (A: Fm) (l: list Fm): bool :=
  if in_dec form_dec A l then true else false.

Definition incl_b (l1 l2: list Fm): bool :=
  forallb (fun A => mem_b A l2) l1.

(* ACUI equivalence of two antecedents *)
Definition ctx_eqb (A B: Fm): bool :=
  andb (incl_b (conjs A) (conjs B)) (incl_b (conjs B) (conjs A)).

Lemma incl_b_sound (l1 l2: list Fm):
  incl_b l1 l2 = true -> forall x, In x l1 -> In x l2.
Proof.
  intros h x hx. unfold incl_b in h. rewrite forallb_forall in h.
  specialize (h x hx). unfold mem_b in h.
  revert h. destruct (in_dec form_dec x l2) as [hin | hnin].
  * intros _. exact hin.
  * intro h. discriminate h.
Qed.

Fixpoint gsat_all (M: Model) (v: Valuation) (l: list Fm): Prop :=
  match l with
  | nil => True
  | g :: l' => gsat M v g /\ gsat_all M v l'
  end.

Lemma gsat_all_concat (M: Model) (v: Valuation):
  forall (l1 l2: list Fm),
    gsat_all M v (app l1 l2) <-> gsat_all M v l1 /\ gsat_all M v l2.
Proof.
  intro l1. induction l1 as [| g l1 ih]; intro l2; simpl.
  * tauto.
  * specialize (ih l2). tauto.
Qed.

Lemma gsat_all_intro (M: Model) (v: Valuation) (l: list Fm):
  (forall A, In A l -> gsat M v A) -> gsat_all M v l.
Proof.
  induction l as [| B l ih].
  * intro h. simpl. exact I.
  * intro h. simpl. split.
    - apply h. left. reflexivity.
    - apply ih. intros A hA. apply h. right. exact hA.
Qed.

Lemma gsat_all_elim (M: Model) (v: Valuation) (l: list Fm):
  forall (A: Fm), gsat_all M v l -> In A l -> gsat M v A.
Proof.
  induction l as [| B l ih]; intros A h hA.
  * destruct hA.
  * simpl in h. destruct h as (h1, h2).
    destruct hA as [heq | hA].
    - rewrite <- heq. exact h1.
    - exact (ih A h2 hA).
Qed.

Lemma leaf_iff (P: Prop):
  P <-> (P /\ True).
Proof.
  split.
  * intro h. split.
    - exact h.
    - exact I.
  * intros [h _]. exact h.
Qed.

Lemma gsat_conjs (F: Fm):
  forall M v, gsat M v F <-> gsat_all M v (conjs F).
Proof.
  induction F as [x | | | A ihA | A ihA B ihB | A ihA B ihB
  | A ihA B ihB | A ihA B ihB | A ihA B ihB];
    intros M v; simpl.
  * apply leaf_iff.
  * apply leaf_iff.
  * apply iff_refl.
  * apply leaf_iff.
  * assert (he := gsat_all_concat M v (conjs A) (conjs B)).
    specialize (ihA M v). specialize (ihB M v). tauto.
  * apply leaf_iff.
  * apply leaf_iff.
  * apply leaf_iff.
  * apply leaf_iff.
Qed.

Lemma ctx_eqb_sound (A B: Fm):
  ctx_eqb A B = true -> forall M v, gsat M v A <-> gsat M v B.
Proof.
  intros h M v. unfold ctx_eqb in h.
  apply andb_true_iff in h. destruct h as (h1, h2).
  assert (h1a := incl_b_sound (conjs A) (conjs B) h1).
  assert (h2a := incl_b_sound (conjs B) (conjs A) h2).
  assert (heA := gsat_conjs A M v).
  assert (heB := gsat_conjs B M v).
  split; intro hgsat.
  * apply (proj2 heB). apply gsat_all_intro. intros x hx.
    apply (gsat_all_elim M v (conjs A) x (proj1 heA hgsat)).
    exact (h2a x hx).
  * apply (proj2 heA). apply gsat_all_intro. intros x hx.
    apply (gsat_all_elim M v (conjs B) x (proj1 heB hgsat)).
    exact (h1a x hx).
Qed.

(* == eqv: syntactic equality modulo sets of conjuncts in contexts == *)

Fixpoint eqv (A B: Fm): bool :=
  match A, B with
  | Svar x, Svar y => if string_dec x y then true else false
  | Falsum, Falsum => true
  | Verum, Verum => true
  | Neg A1, Neg B1 => eqv A1 B1
  | Conj A1 A2, Conj B1 B2 => andb (eqv A1 B1) (eqv A2 B2)
  | Disj A1 A2, Disj B1 B2 => andb (eqv A1 B1) (eqv A2 B2)
  | Subj A1 A2, Subj B1 B2 => andb (eqv A1 B1) (eqv A2 B2)
  | Equi A1 A2, Equi B1 B2 => andb (eqv A1 B1) (eqv A2 B2)
  | Seq A1 A2, Seq B1 B2 => andb (ctx_eqb A1 B1) (eqv A2 B2)
  | _, _ => false
  end.

Lemma eqv_sound: forall (A B: Fm),
  eqv A B = true -> forall M v, gsat M v A <-> gsat M v B.
Proof.
  intro A.
  induction A as [x | | | A1 ih1 | A1 ih1 A2 ih2 | A1 ih1 A2 ih2
  | A1 ih1 A2 ih2 | A1 ih1 A2 ih2 | A1 ih1 A2 ih2];
    intros B hB;
    destruct B as [y | | | B1 | B1 B2 | B1 B2 | B1 B2 | B1 B2 | B1 B2];
    simpl in hB; try discriminate.
  * (* Svar *)
    revert hB. destruct (string_dec x y) as [hl | hr].
    - intros _ M v. subst. apply iff_refl.
    - intro hB. discriminate hB.
  * (* Falsum *) intros M v. apply iff_refl.
  * (* Verum *) intros M v. apply iff_refl.
  * (* Neg *)
    intros M v. simpl.
    specialize(ih1 B1 hB M v). tauto.
  * (* Conj *)
    apply andb_true_iff in hB. destruct hB as (h1, h2).
    intros M v. simpl.
    specialize (ih1 B1 h1 M v).
    specialize (ih2 B2 h2 M v). tauto.
  * (* Disj *)
    apply andb_true_iff in hB. destruct hB as (h1, h2).
    intros M v. simpl.
    specialize (ih1 B1 h1 M v).
    specialize (ih2 B2 h2 M v). tauto.
  * (* Subj *)
    apply andb_true_iff in hB. destruct hB as (h1, h2).
    intros M v. simpl.
    specialize (ih1 B1 h1 M v).
    specialize (ih2 B2 h2 M v). tauto.
  * (* Equi *)
    apply andb_true_iff in hB. destruct hB as (h1, h2).
    intros M v. simpl.
    specialize (ih1 B1 h1 M v).
    specialize (ih2 B2 h2 M v). tauto.
  * (* Seq *)
    apply andb_true_iff in hB. destruct hB as (h1, h2).
    intros M v. simpl. split; intros h w hw.
    - apply (proj1 (ih2 B2 h2 M w)). apply h.
      apply (proj2 (ctx_eqb_sound A1 B1 h1 M w)). exact hw.
    - apply (proj2 (ih2 B2 h2 M w)). apply h.
      apply (proj1 (ctx_eqb_sound A1 B1 h1 M w)). exact hw.
Qed.

(* == The matcher (may remain unverified) == *)

(* bindf P A s: structurally binds unbound pattern variables of P to the
   matching subformulas of A. On structural mismatches, nothing is bound.
   Correctness is ensured solely by the subsequent check with eqv. *)
Fixpoint bindf (P A: Fm) (s: senv): senv :=
  match P, A with
  | Svar x, _ =>
      match lookup x s with
      | Some _ => s
      | None => (x, A) :: s
      end
  | Neg P1, Neg A1 => bindf P1 A1 s
  | Conj P1 P2, Conj A1 A2 => bindf P2 A2 (bindf P1 A1 s)
  | Disj P1 P2, Disj A1 A2 => bindf P2 A2 (bindf P1 A1 s)
  | Subj P1 P2, Subj A1 A2 => bindf P2 A2 (bindf P1 A1 s)
  | Equi P1 P2, Equi A1 A2 => bindf P2 A2 (bindf P1 A1 s)
  | Seq P1 P2, Seq A1 A2 => bindf P2 A2 (bindf P1 A1 s)
  | _, _ => s
  end.

(* Rule c = C1 -> ... -> Cn -> D, arguments A1..An, conclusion B. *)
Fixpoint bind_chain (C: Fm) (args: list Fm) (B: Fm) (s: senv): senv :=
  match args with
  | nil => bindf C B s
  | A :: args' =>
      match C with
      | Subj C1 C2 => bind_chain C2 args' B (bindf C1 A s)
      | _ => s
      end
  end.

(* == Errors, status, and checking of a rule application == *)

Inductive err: Type :=
| EUnknown: label -> err         (* unknown rule or line *)
| ECyclic : err                  (* cyclic deduction *)
| ENotRule: err                  (* expected a rule/subjunction *)
| EArg    : label -> nat -> err  (* argument i does not match *)
| EConcl  : label -> err         (* conclusion does not match *)
| ENoSeq  : label -> err.        (* context label is not a sequent *)

Inductive status: Type :=
| OK : status
| ERR: err -> status.

Fixpoint verify_chain (r: label) (i: nat) (s: senv) (C: Fm)
  (args: list Fm) (B: Fm) {struct args}: status :=
  match args with
  | nil => if eqv (inst s C) B then OK else ERR (EConcl r)
  | A :: args' =>
      match C with
      | Subj C1 C2 =>
          if eqv (inst s C1) A
          then verify_chain r (S i) s C2 args' B
          else ERR (EArg r i)
      | _ => ERR ENotRule
      end
  end.

Lemma chain_sound: forall (args: list Fm) (r: label) (i: nat)
  (s: senv) (C B: Fm), (forall f, In f args -> gvalid f) ->
  verify_chain r i s C args B = OK ->
  forall M v, gsat M v (inst s C) -> gsat M v B.
Proof.
  intro args.
  induction args as [| A args ih]; intros r i s C B hargs; simpl.
  * destruct (eqv (inst s C) B) eqn:heq.
    - intros _ M v hs.
      exact (proj1 (eqv_sound (inst s C) B heq M v) hs).
    - intro h. discriminate h.
  * destruct C as [x | | | C1 | C1 C2 | C1 C2 | C1 C2 | C1 C2 | C1 C2];
      try (intro h; discriminate h).
    simpl.
    destruct (eqv (inst s C1) A) eqn:heq.
    - intros h M v hs.
      specialize (ih r (S i) s C2 B).
      apply (ih (fun F hF => hargs F (or_intror hF)) h M v).
      apply hs.
      apply (proj2 (eqv_sound (inst s C1) A heq M v)).
      exact (hargs A (or_introl eq_refl) M v).
    - intro h. discriminate h.
Qed.

(* Resolving the argument labels in the book. *)
Fixpoint resolve (bk: book) (ls: list label): label + list Fm :=
  match ls with
  | nil => inr nil
  | l :: ls' =>
      match lookup l bk with
      | None => inl l
      | Some A =>
          match resolve bk ls' with
          | inl e => inl e
          | inr fs => inr (A :: fs)
          end
      end
  end.

Lemma resolve_valid: forall (bk: book) (ls: list label) (ps: list Fm),
  BookOK bk -> resolve bk ls = inr ps -> forall A, In A ps -> gvalid A.
Proof.
  intros bk ls. induction ls as [| l ls ih]; intros ps hbk; simpl.
  * intro h. injection h as h1. subst. intros A hA. destruct hA.
  * destruct (lookup l bk) as [g |] eqn:heq1.
    - destruct (resolve bk ls) as [e | fs].
      + intro h. discriminate h.
      + intro h. simpl in h. injection h as h1. subst.
        intros A hA. destruct hA as [hl | hr].
        -- rewrite <- hl. exact (hbk l g heq1).
        -- exact (ih fs hbk eq_refl A hr).
    - intro h. discriminate h.
Qed.

(* A rule application: rule r with arguments args yields the formula B. *)
Definition rule_step (bk: book) (r: label) (args: list label) (B: Fm): status :=
  match lookup r bk with
  | None => ERR (EUnknown r)
  | Some R =>
      match resolve bk args with
      | inl l => ERR (EUnknown l)
      | inr ps => verify_chain r 1 (bind_chain R ps B nil) R ps B
      end
  end.

Lemma rule_step_sound (bk: book) (r: label) (args: list label) (B: Fm):
  BookOK bk -> rule_step bk r args B = OK -> gvalid B.
Proof.
  intro hbk. unfold rule_step.
  destruct (lookup r bk) as [R |] eqn:heq1.
  * destruct (resolve bk args) as [l | ps] eqn:heq2.
    - intro h. discriminate h.
    - intro h. unfold gvalid. intros M v.
      assert (hR : gsat M v (inst (bind_chain R ps B nil) R)).
      { apply (proj2 (gsat_inst (bind_chain R ps B nil) M R v)).
        exact (hbk r R heq1 (variant M (bind_chain R ps B nil)) v). }
      exact (chain_sound ps r 1 (bind_chain R ps B nil) R B
        (resolve_valid bk args ps hbk heq2) h M v hR).
  * intro h. discriminate h.
Qed.

(* == Proof steps and checking entire proofs == *)

(* Plain A  : a concrete formula.
   Hyps g A : g |- A, where g is the list of labels of the hypotheses. *)
Inductive stmt: Type :=
| Plain: Fm -> stmt
| Hyps : list label -> Fm -> stmt.

Record proof_step: Type := mkstep {
  s_line : nat;        (* line number in the input, only for messages *)
  s_label: label;
  s_stmt : stmt;
  s_rule : label;      (* name of the rule or the line serving as a rule *)
  s_args : list label  (* arguments *)
}.

(* As in nd.py, the context g becomes the conjunction of the succedents of
   the referenced lines. The step's own label denotes the formula a. *)
Definition ctx_item (bk: book) (self: label) (A: Fm) (k: label): option Fm :=
  if string_dec k self then Some A
  else match lookup k bk with
       | Some (Seq _ C) => Some C
       | _ => None
       end.

Fixpoint build_ctx (bk: book) (self: label) (A: Fm)
  (g: list label) (H: Fm) : err + Fm :=
  match g with
  | nil => inr H
  | k :: g' =>
      match ctx_item bk self A k with
      | Some C => build_ctx bk self A g' (Conj H C)
      | None => inl (ENoSeq k)
      end
  end.

Definition stmt_formula (bk: book) (lab: label) (sm: stmt): err + Fm :=
  match sm with
  | Plain A => inr A
  | Hyps g A =>
      match build_ctx bk lab A g Verum with
      | inl e => inl e
      | inr H => inr (Seq H A)
      end
  end.

Definition mem_label (l: label) (ls: list label): bool :=
  if in_dec string_dec l ls then true else false.
Arguments mem_label: simpl never.

Definition commit (bk: book) (line: nat) (lab r: label)
  (args: list label) (B: Fm): (nat * err) + book :=
  if mem_label lab (r :: args)
  then inl (line, ECyclic)
  else match rule_step bk r args B with
       | OK => inr ((lab, B) :: bk)
       | ERR e => inl (line, e)
       end.

Lemma commit_sound (bk: book) (line: nat) (lab r: label)
  (args: list label) (B: Fm) (bk': book):
  BookOK bk -> commit bk line lab r args B = inr bk' -> BookOK bk'.
Proof.
  intro hbk. unfold commit.
  destruct (mem_label lab (r :: args)).
  * intro h. discriminate h.
  * destruct (rule_step bk r args B) as [| e] eqn:heq.
    - intro h. simpl in h. injection h as h1. subst.
      apply bookok_cons.
      + exact hbk.
      + exact (rule_step_sound bk r args B hbk heq).
    - intro h. discriminate h.
Qed.

Definition check_step (bk: book) (st: proof_step): (nat * err) + book :=
  match stmt_formula bk (s_label st) (s_stmt st) with
  | inl e => inl (s_line st, e)
  | inr B => commit bk (s_line st) (s_label st) (s_rule st) (s_args st) B
  end.

Lemma check_step_sound (bk: book) (st: proof_step) (bk': book):
  BookOK bk -> check_step bk st = inr bk' -> BookOK bk'.
Proof.
  intro hbk. unfold check_step.
  destruct (stmt_formula bk (s_label st) (s_stmt st)) as [e | B].
  * intro h. discriminate h.
  * exact (commit_sound bk
      (s_line st) (s_label st) (s_rule st) (s_args st)
      B bk' hbk).
Qed.

Fixpoint check_steps (bk: book) (sts: list proof_step): (nat * err) + book :=
  match sts with
  | nil => inr bk
  | st :: sts' =>
      match check_step bk st with
      | inl e => inl e
      | inr bk' => check_steps bk' sts'
      end
  end.

Lemma check_steps_sound: forall (sts: list proof_step) (bk bk': book),
  BookOK bk -> check_steps bk sts = inr bk' -> BookOK bk'.
Proof.
  intro sts. induction sts as [| st sts ih]; intros bk bk' hbk; simpl.
  * intro h. injection h as h1. subst. exact hbk.
  * destruct (check_step bk st) as [e | bk1] eqn:heq.
    - intro h. discriminate h.
    - intro h. assert (hs := check_step_sound bk st bk1 hbk heq).
      exact (ih bk1 bk' hs h).
Qed.

(* == The axioms (prelude) and their validity == *)

Notation vH  := (Svar "H"%string).
Notation vH1 := (Svar "H1"%string).
Notation vH2 := (Svar "H2"%string).
Notation vH3 := (Svar "H3"%string).
Notation vA  := (Svar "A"%string).
Notation vB  := (Svar "B"%string).
Notation vC  := (Svar "C"%string).

Definition ax_hypo: Fm := Seq (Conj Verum vH) vH.
Definition ax_conj_intro: Fm :=
  Subj (Seq vH1 vA) (Subj (Seq vH2 vB) (Seq (Conj vH1 vH2) (Conj vA vB))).
Definition ax_conj_eliml: Fm := Subj (Seq vH (Conj vA vB)) (Seq vH vA).
Definition ax_conj_elimr: Fm := Subj (Seq vH (Conj vA vB)) (Seq vH vB).
Definition ax_disj_introl: Fm := Subj (Seq vH vA) (Seq vH (Disj vA vB)).
Definition ax_disj_intror: Fm := Subj (Seq vH vB) (Seq vH (Disj vA vB)).
Definition ax_disj_elim: Fm :=
  Subj (Seq vH1 (Disj vA vB))
    (Subj (Seq (Conj vH2 vA) vC)
      (Subj (Seq (Conj vH3 vB) vC)
        (Seq (Conj (Conj vH1 vH2) vH3) vC))).
Definition ax_subj_intro: Fm :=
  Subj (Seq (Conj vH vA) vB) (Seq vH (Subj vA vB)).
Definition ax_subj_elim: Fm :=
  Subj (Seq vH1 (Subj vA vB)) (Subj (Seq vH2 vA) (Seq (Conj vH1 vH2) vB)).
Definition ax_neg_intro: Fm :=
  Subj (Seq (Conj vH vA) Falsum) (Seq vH (Neg vA)).
Definition ax_neg_elim: Fm :=
  Subj (Seq vH1 (Neg vA)) (Subj (Seq vH2 vA) (Seq (Conj vH1 vH2) Falsum)).
Definition ax_equi_intro: Fm :=
  Subj (Seq vH1 (Subj vA vB))
    (Subj (Seq vH2 (Subj vB vA)) (Seq (Conj vH1 vH2) (Equi vA vB))).
Definition ax_equi_eliml: Fm :=
  Subj (Seq vH (Equi vA vB)) (Seq vH (Subj vA vB)).
Definition ax_equi_elimr: Fm :=
  Subj (Seq vH (Equi vA vB)) (Seq vH (Subj vB vA)).
Definition ax_wk: Fm := Subj (Seq vH vB) (Seq (Conj vH vA) vB).
Definition ax_exch: Fm := Subj (Seq vH vA) (Seq vH vA).

(* Classical extensions. *)
Definition ax_efq: Fm := Subj (Seq vH Falsum) (Seq vH vA).
Definition ax_lem: Fm := Seq vH (Disj vA (Neg vA)).
Definition ax_dne: Fm := Subj (Seq vH (Neg (Neg vA))) (Seq vH vA).

Lemma gv_hypo: gvalid ax_hypo.
Proof.
  unfold gvalid. intros M v. unfold ax_hypo. simpl.
  intros w [_ hw]. exact hw.
Qed.

Lemma gv_conj_intro: gvalid ax_conj_intro.
Proof.
  unfold gvalid. intros M v. unfold ax_conj_intro. simpl.
  intros hA hB w (h1, h2). split.
  - exact (hA w h1).
  - exact (hB w h2).
Qed.

Lemma gv_conj_eliml: gvalid ax_conj_eliml.
Proof.
  unfold gvalid. intros M v. unfold ax_conj_eliml. simpl.
  intros hAB w h. exact (proj1 (hAB w h)).
Qed.

Lemma gv_conj_elimr: gvalid ax_conj_elimr.
Proof.
  unfold gvalid. intros M v. unfold ax_conj_elimr. simpl.
  intros hAB w h. exact (proj2 (hAB w h)).
Qed.

Lemma gv_disj_introl: gvalid ax_disj_introl.
Proof.
  unfold gvalid. intros M v. unfold ax_disj_introl. simpl.
  intros hA w h. left. exact (hA w h).
Qed.

Lemma gv_disj_intror: gvalid ax_disj_intror.
Proof.
  unfold gvalid. intros M v. unfold ax_disj_intror. simpl.
  intros hB w h. right. exact (hB w h).
Qed.

Lemma gv_disj_elim: gvalid ax_disj_elim.
Proof.
  unfold gvalid. intros M v. unfold ax_disj_elim. simpl.
  intros hAB hAC hBC w [[h1 h2] h3].
  destruct (hAB w h1) as [hA | hB].
  - apply hAC. split; assumption.
  - apply hBC. split; assumption.
Qed.

Lemma gv_subj_intro: gvalid ax_subj_intro.
Proof.
  unfold gvalid. intros M v. unfold ax_subj_intro. simpl.
  intros h w hH hA. apply h. split; assumption.
Qed.

Lemma gv_subj_elim: gvalid ax_subj_elim.
Proof.
  unfold gvalid. intros M v. unfold ax_subj_elim. simpl.
  intros hAB hA w (h1, h2).
  exact (hAB w h1 (hA w h2)).
Qed.

Lemma gv_neg_intro: gvalid ax_neg_intro.
Proof.
  unfold gvalid. intros M v. unfold ax_neg_intro. simpl.
  intros h w hH hA. exact (h w (conj hH hA)).
Qed.

Lemma gv_neg_elim: gvalid ax_neg_elim.
Proof.
  unfold gvalid. intros M v. unfold ax_neg_elim. simpl.
  intros hnA hA w (h1, h2). exact (hnA w h1 (hA w h2)).
Qed.

Lemma gv_equi_intro: gvalid ax_equi_intro.
Proof.
  unfold gvalid. intros M v. unfold ax_equi_intro. simpl.
  intros hAB hBA w (h1, h2). split.
  - exact (hAB w h1).
  - exact (hBA w h2).
Qed.

Lemma gv_equi_eliml: gvalid ax_equi_eliml.
Proof.
  unfold gvalid. intros M v. unfold ax_equi_eliml. simpl.
  intros h w hH. exact (proj1 (h w hH)).
Qed.

Lemma gv_equi_elimr: gvalid ax_equi_elimr.
Proof.
  unfold gvalid. intros M v. unfold ax_equi_elimr. simpl.
  intros h w hH. exact (proj2 (h w hH)).
Qed.

Lemma gv_wk: gvalid ax_wk.
Proof.
  unfold gvalid. intros M v. unfold ax_wk. simpl.
  intros h w (hH, _). exact (h w hH).
Qed.

Lemma gv_exch: gvalid ax_exch.
Proof.
  unfold gvalid. intros M v. unfold ax_exch. simpl.
  intro h. exact h.
Qed.

Lemma gv_efq: gvalid ax_efq.
Proof.
  unfold gvalid. intros M v. unfold ax_efq. simpl.
  intros h w hH. exfalso. exact (h w hH).
Qed.

Lemma gv_lem: gvalid ax_lem.
Proof.
  unfold gvalid. intros M v. unfold ax_lem. simpl.
  intros w _. apply classic.
Qed.

Lemma gv_dne: gvalid ax_dne.
Proof.
  unfold gvalid. intros M v. unfold ax_dne. simpl.
  intros h w hH. apply NNPP. exact (h w hH).
Qed.

Definition prelude: book :=
  [ ("hypo", ax_hypo);
    ("conj_intro", ax_conj_intro);
    ("conj_eliml", ax_conj_eliml);
    ("conj_elimr", ax_conj_elimr);
    ("disj_introl", ax_disj_introl);
    ("disj_intror", ax_disj_intror);
    ("disj_elim", ax_disj_elim);
    ("subj_intro", ax_subj_intro);
    ("subj_elim", ax_subj_elim);
    ("neg_intro", ax_neg_intro);
    ("neg_elim", ax_neg_elim);
    ("equi_intro", ax_equi_intro);
    ("equi_eliml", ax_equi_eliml);
    ("equi_elimr", ax_equi_elimr);
    ("wk", ax_wk);
    ("exch", ax_exch);
    ("efq", ax_efq);
    ("lem", ax_lem);
    ("dne", ax_dne) ].

Lemma prelude_valid:
  Forall (fun p: label * Fm => gvalid (snd p)) prelude.
Proof.
  unfold prelude.
  constructor; [ exact gv_hypo | ].
  constructor; [ exact gv_conj_intro | ].
  constructor; [ exact gv_conj_eliml | ].
  constructor; [ exact gv_conj_elimr | ].
  constructor; [ exact gv_disj_introl | ].
  constructor; [ exact gv_disj_intror | ].
  constructor; [ exact gv_disj_elim | ].
  constructor; [ exact gv_subj_intro | ].
  constructor; [ exact gv_subj_elim | ].
  constructor; [ exact gv_neg_intro | ].
  constructor; [ exact gv_neg_elim | ].
  constructor; [ exact gv_equi_intro | ].
  constructor; [ exact gv_equi_eliml | ].
  constructor; [ exact gv_equi_elimr | ].
  constructor; [ exact gv_wk | ].
  constructor; [ exact gv_exch | ].
  constructor; [ exact gv_efq | ].
  constructor; [ exact gv_lem | ].
  constructor; [ exact gv_dne | ].
  constructor.
Qed.

Lemma prelude_ok: BookOK prelude.
Proof.
  unfold BookOK. intros l f h.
  apply lookup_in in h.
  assert (hv := prelude_valid).
  rewrite Forall_forall in hv.
  exact (hv (l, f) h).
Qed.

(* == The checker and its soundness theorem == *)

(* Result: inl (line, error) or inr book of all proved lines. *)
Definition verify (sts: list proof_step): (nat * err) + book :=
  check_steps prelude sts.

Theorem verify_sound (sts: list proof_step) (bk: book):
  verify sts = inr bk -> forall (l : label) (A : Fm),
    lookup l bk = Some A -> forall (v: Valuation), sat v A.
Proof.
  intros h l A hl v.
  exact (check_steps_sound sts prelude bk prelude_ok h l A hl std v).
Qed.

(* A line of the form |- A is a classical tautology
   (for sequent-free A, it uses the usual Boolean semantics). *)
Theorem verify_sound_theorem (sts: list proof_step)
  (bk: book) (l: label) (A: Fm):
  verify sts = inr bk -> lookup l bk = Some (Seq Verum A) ->
    forall (v: Valuation), sat v A.
Proof.
  intros h hl v.
  assert (hA := verify_sound sts bk h l (Seq Verum A) hl v).
  unfold sat in hA. simpl in hA.
  exact (hA v I).
Qed.

(* == Ensuring conservative extension == *)

(* This section is actually superfluous, since verify_sound_theorem
   already clarifies the conservative extension. For the sake of
   pedantry, it is nevertheless shown explicitly as well. *)

Fixpoint seqfree (F: Fm): bool :=
  match F with
  | Svar _ => true
  | Falsum => true
  | Verum => true
  | Neg A => seqfree A
  | Conj A B => andb (seqfree A) (seqfree B)
  | Disj A B => andb (seqfree A) (seqfree B)
  | Subj A B => andb (seqfree A) (seqfree B)
  | Equi A B => andb (seqfree A) (seqfree B)
  | Seq _ _ => false
  end.

(* The usual evaluation with truth values (truth table). *)
Fixpoint evalb (v: Valuation) (F: Fm): bool :=
  match F with
  | Svar x => v x
  | Falsum => false
  | Verum => true
  | Neg A => negb (evalb v A)
  | Conj A B => andb (evalb v A) (evalb v B)
  | Disj A B => orb (evalb v A) (evalb v B)
  | Subj A B => implb (evalb v A) (evalb v B)
  | Equi A B => andb
      (implb (evalb v A) (evalb v B))
      (implb (evalb v B) (evalb v A))
  | Seq _ _ => false  (* meaningless here, excluded by seqfree *)
  end.

Lemma negb_T (b: bool):
  negb b = true <-> ~ (b = true).
Proof.
  destruct b; simpl; split.
  * intro h. discriminate h.
  * intro h. exfalso. apply h. reflexivity.
  * intros _ e. discriminate e.
  * intros _. reflexivity.
Qed.

Lemma implb_T (a b: bool):
  implb a b = true <-> (a = true -> b = true).
Proof.
  destruct a; simpl; split.
  * intros h _. exact h.
  * intro h. exact (h eq_refl).
  * intros _ e. discriminate e.
  * intros _. reflexivity.
Qed.

(* On sequent-free formulas, the semantics gsat std agrees
   with the truth table. *)
Lemma gsat_evalb: forall (A: Fm) (v: Valuation),
  seqfree A = true -> (gsat std v A <-> evalb v A = true).
Proof.
  intro A.
  induction A as [x | | | A1 ih1 | A1 ih1 A2 ih2 | A1 ih1 A2 ih2
  | A1 ih1 A2 ih2 | A1 ih1 A2 ih2 | A1 ih1 A2 ih2];
    intros v hs; simpl in hs; simpl.
  * (* Svar *)
    apply iff_refl.
  * (* Falsum *)
    split.
    - intro h. destruct h.
    - intro h. discriminate h.
  * (* Verum *)
    split; intros _.
    - reflexivity.
    - exact I.
  * (* Neg *)
    specialize (ih1 v hs).
    assert (h := negb_T (evalb v A1)).
    tauto.
  * (* Conj *)
    apply andb_true_iff in hs. destruct hs as (h1, h2).
    specialize (ih1 v h1). specialize (ih2 v h2).
    assert (h := andb_true_iff (evalb v A1) (evalb v A2)).
    tauto.
  * (* Disj *)
    apply andb_true_iff in hs. destruct hs as (h1, h2).
    specialize (ih1 v h1). specialize (ih2 v h2).
    assert (h := orb_true_iff (evalb v A1) (evalb v A2)).
    tauto.
  * (* Subj *)
    apply andb_true_iff in hs. destruct hs as (h1, h2).
    specialize (ih1 v h1). specialize (ih2 v h2).
    assert (h := implb_T (evalb v A1) (evalb v A2)).
    tauto.
  * (* Equi *)
    apply andb_true_iff in hs. destruct hs as (h1, h2).
    specialize (ih1 v h1). specialize (ih2 v h2).
    assert (h3 := andb_true_iff
      (implb (evalb v A1) (evalb v A2))
      (implb (evalb v A2) (evalb v A1))).
    assert (h4 := implb_T (evalb v A1) (evalb v A2)).
    assert (h5 := implb_T (evalb v A2) (evalb v A1)).
    tauto.
  * (* Seq *)
    discriminate hs.
Qed.

(* Main theorem in truth-table form: every sequent-free
   theorem A is a classical tautology. *)
Theorem verify_sound_tautology (sts: list proof_step)
  (bk: book) (l: label) (A: Fm):
  verify sts = inr bk -> lookup l bk = Some (Seq Verum A) ->
    seqfree A = true -> forall (v: Valuation), evalb v A = true.
Proof.
  intros h hl hs v.
  apply (proj1 (gsat_evalb A v hs)).
  exact (verify_sound_theorem sts bk l A h hl v).
Qed.

Extraction "kernel.ml" verify.

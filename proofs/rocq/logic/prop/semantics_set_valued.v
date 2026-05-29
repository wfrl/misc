(*===================================================================
  Equivalence of standard validity and set-theoretic validity
  ===================================================================
  The following establishes a bridge between standard propositional
  logic semantics (valuation mapping variables to {false, true})
  and algebraic semantics using set theory (valuating variables
  inside a universe set G). For simplicity, Prop is identified here
  with the two-valued Boolean algebra. Alternatively, the proof could
  also be adapted to v: ℕ → bool, see semantics_set_valued_bool.v.

  Mathematical approach:
  1. Syntax: Propositional formulas consist of variables, falsum (⊥),
     and subjunction (→) (a.k.a. implication).
  2. Standard semantics (sat): A valuation v: ℕ → Prop maps variables
     to {false, true}. A formula is valid if it evaluates to true
     under all boolean valuations. In this context, evaluation is
     synonymous with interpretation, the extension of valuation from
     variables to arbitrary formulas.
  3. Set semantics (ev): A valuation v: ℕ → Ensemble G maps
     variables to subsets of a universe G (german: Grundmenge). 
     Intuition:
       - false conceptually maps to the empty set ∅.
       - true conceptually maps to the full set G.
     A formula is set-valid if its evaluation yields the full set G 
     under all set-valuations.
  4. Bridge lemmas (translating between interpretations): To prove
     the equivalence of the two semantics, we cannot compare them
     directly. Instead, we must construct specific valuations that
     translate the context of one semantics into the other:
     4.1 Point-wise projection (sat_lemma): An element x is in the
         set-evaluation of F iff F is logically true when we valuate
         variables P based on whether x ∈ v(P).
     4.2 Lifting to constant sets (sat_lemma_reverse): A formula is
         logically true under v iff an arbitrary element x is in its
         set-evaluation under a "constant" set-valuation where P maps
         to G if v(P) is true, and ∅ if false.
  5. Equivalence: Using these lemmas, we prove that classical
     validity and set-theoretic validity imply each other.

  Note on the empty universe: Set-validity only implies standard
  validity if the universe G contains at least one element
  (inhabited G). In an empty universe, the full set and the empty
  set are identical, collapsing all truth values.
  ================================================================ *)

Require Import Sets.Ensembles.

(* Inductive datatype defining the syntax of
   propositional logic formulas *)
Inductive Formula :=
| var: nat -> Formula
| falsum: Formula
| subj: Formula -> Formula -> Formula.

(* Standard semantics of propositional logic *)
Fixpoint sat (v: nat -> Prop) (F: Formula): Prop :=
  match F with
  | var P => v P
  | falsum => False
  | subj A B => ~sat v A \/ sat v B
  end.

(* Logical validity: truth under all possible valuations *)
Definition valid (A: Formula): Prop :=
  forall v: nat -> Prop, sat v A.

(* Set-theoretic evaluation mapping a formula to
   a subset of a universe G *)
Fixpoint ev (G: Type) (v: nat -> Ensemble G) (F: Formula): Ensemble G :=
  match F with
  | var P => v P
  | falsum => Empty_set G
  | subj A B => Union G (Complement G (ev G v A)) (ev G v B)
  end.

(* Set-theoretic validity: evaluating to the full universe G *)
Definition set_valid (G: Type) (A: Formula): Prop :=
  forall v: nat -> Ensemble G, ev G v A = Full_set G.

(* Satisfaction lemma:
   Let w P := if x ∈ v P then true else false.
   We have w ⊨ F iff x ∈ ev v F. *)
Lemma sat_lemma (G: Type) (x: G) (v: nat -> Ensemble G):
  forall F, sat (fun P => In G (v P) x) F <-> In G (ev G v F) x.
Proof.
  intro F. induction F as [Q | | A ihA B ihB].
  * split.
    - intro h. simpl sat in h. simpl In. exact h.
    - intro h. simpl sat. simpl In in h. exact h.
  * simpl sat. simpl ev. unfold In. split.
    - intro h. exfalso. exact h.
    - intro h. destruct h.
  * split.
    - intro h. simpl sat in h. simpl In.
      destruct h as [hl | hr].
      -- apply Union_introl. unfold In. unfold Complement.
         intro hcontra. apply ihA in hcontra. exact (hl hcontra).
      -- apply Union_intror. apply ihB. apply hr.
    - intro h. simpl sat. simpl In in h.
      unfold In in h. destruct h as [x hl | x hr].
      -- apply or_introl. intro hcontra.
         unfold In in hl. unfold Complement in hl.
         apply ihA in hcontra. exact (hl hcontra).
      -- apply or_intror. apply ihB. exact hr.
Qed.

(* Reverse satisfaction lemma:
   Let w P := if v P = true then G else ∅, which is
   expressed as w P := λz. v P, that is, for every
   proposition P, the function λz. v P is a constant
   predicate, either (λz. false) = ∅ or (λz. true) = G 
   We have v ⊨ F iff x ∈ ev w F. *)
Lemma sat_lemma_reverse (G: Type) (x: G) (v: nat -> Prop):
  forall F, sat v F <-> In G (ev G (fun P => fun _ => v P) F) x.
Proof.
  intro F. induction F as [Q | | A ihA B ihB].
  * simpl. unfold In.
    split.
    - intro h. exact h.
    - intro h. exact h.
  * simpl ev. simpl sat. unfold In. split.
    - intro h. exfalso. exact h.
    - intro h. destruct h.
  * simpl. unfold In. split.
    - intro h. destruct h as [hl | hr].
      -- apply Union_introl. intro hcontra.
         apply ihA in hcontra. exact (hl hcontra).
      -- apply Union_intror. apply ihB. exact hr.
    - intro h. destruct h as [y hl | y hr].
      -- left. intro hcontra. apply ihA in hcontra.
         exact (hl hcontra).
      -- right. apply ihB. exact hr.
Qed.

(* Standard validity implies set-theoretic validity *)
Theorem valid_implies_set_valid (G: Type) (A: Formula):
  valid A -> set_valid G A.
Proof.
  intro h. unfold set_valid. intro v.
  apply Extensionality_Ensembles.
  unfold Same_set. split.
  * unfold Included. intros x hx. apply Full_intro.
  * unfold Included. intros x hx.
    unfold valid in h.
    specialize h with (fun P => In G (v P) x).
    apply sat_lemma. exact h.
Qed.

(* Set-theoretic validity in a non-empty universe
   implies standard validity *)
Theorem set_valid_implies_valid (G: Type) (A: Formula):
  inhabited G -> set_valid G A -> valid A.
Proof.
  intros hG h v. unfold set_valid in h.
  specialize (h (fun P => fun _ => v P)).
  destruct hG as (x). apply (sat_lemma_reverse G x v).
  rewrite h. unfold In. apply Full_intro.
Qed.

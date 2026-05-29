
(* On the substitution rule *)
(* ======================== *)

(* We want to prove the substitution rule of propositional
   logic to be admissible. To keep the presentation concise,
   only a minimal fragment of propositional logic is
   considered. *)

(* Define what a well-formed logical formula is:
   For every natural number n, var n is a formula,
     called an atomic formula or propositional variable.
   If A, B are formulas, then subj A B is also
     a formula, called subjunction or implication. *)
Inductive Formula :=
| var: nat -> Formula
| subj: Formula -> Formula -> Formula.

(* Define what a list of hypotheses is *)
Inductive List :=
| empty
| cons: List -> Formula -> List.

(* Define concatenation of lists *)
Fixpoint concat (Γ1 Γ2: List) :=
  match Γ2 with
  | empty => Γ1
  | cons Γ2' A => cons (concat Γ1 Γ2') A
  end.

(* Define what a sequent is *)
Inductive Seq := seq: List -> Formula -> Seq.

(* Define what proof tree is in natural deduction *)
Inductive Prf: Seq -> Type :=
| hypo: forall A, Prf (seq (cons empty A) A)
| subj_intro: forall Γ A B, Prf (seq (cons Γ A) B) ->
    Prf (seq Γ (subj A B))
| subj_elim: forall Γ Γ' A B,
    Prf (seq Γ (subj A B)) -> Prf (seq Γ' A) ->
    Prf (seq (concat Γ Γ') B).

(* Define substitution E[P:=F] *)
Fixpoint subst (E: Formula) (P: nat) (F: Formula) :=
  match E with
  | var Q => if Nat.eqb P Q then F else var Q
  | subj A B => subj (subst A P F) (subst B P F)
  end.

(* Define substitution Γ[P:=F] *)
Fixpoint subst_list (Γ: List) (P: nat) (A: Formula) :=
  match Γ with
  | empty => empty
  | cons Γ E => cons (subst_list Γ P A) (subst E P A)
  end.

(* Define substitution (Γ ⊢ E)[E:=F] as Γ[P:=F] ⊢ E[P:=F] *)
Definition subst_seq (S: Seq) (P: nat) (F: Formula) :=
  match S with 
  | (seq Γ E) => seq (subst_list Γ P F) (subst E P F)
  end.

(* Substitution distributes over concatenation *)
Lemma subst_list_concat: forall Γ2 Γ1 P F,
  subst_list (concat Γ1 Γ2) P F =
  concat (subst_list Γ1 P F) (subst_list Γ2 P F).
Proof.
  induction Γ2 as [| A ih].
  * intros Γ1 P F. simpl. reflexivity.
  * intros Γ1 P F. simpl. rewrite ih. reflexivity.
Qed.

(* From Γ ⊢ E we may derive (Γ ⊢ E)[P:=F] *)
Theorem substitution_is_admissble S P F:
  Prf S -> Prf (subst_seq S P F).
Proof.
  intro h. revert P F.
  induction h as [A | Γ A B _ ih | Γ Γ' A B _ ih1 _ ih2].
  * intros P F. simpl. apply hypo.
  * intros P F. simpl. apply subj_intro.
    specialize (ih P F).
    simpl in ih. exact ih.
  * intros P F. simpl. rewrite subst_list_concat.
    specialize (ih1 P F).
    specialize (ih2 P F).
    apply (subj_elim
      (subst_list Γ P F) (subst_list Γ' P F)
      (subst A P F) (subst B P F)).
    - simpl in ih1. exact ih1.
    - simpl in ih2. exact ih2.
Qed.

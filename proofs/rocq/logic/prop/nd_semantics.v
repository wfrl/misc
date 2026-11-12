
(* The following formalized discussion confirms the soundness of the
calculus used by the proof checker nd. In this calculus, a sequent H ⊢ A
is internalized into the object language as the modal logic formula
□(H → A). To this end, one first considers extending the semantics such
that satisfaction v ⊨ □A is defined as ∀w. w ⊨ A, where v and w are
valuations. Validity ⊨ A is likewise defined as ∀v. v ⊨ A. However, the
substitution lemma breaks down under this definition. Specifically,
¬□A ∧ ¬□¬A is then valid, whereas its substitution instance with
A := verum is no longer valid. The issue is resolved by defining
satisfaction (M, v) ⊨ □A as ∀w. (M, w) ⊨ A, while defining validity ⊨ A
as ∀M. ∀v. (M, v) ⊨ A. *)

(* == Table of contents ==
1. Definitions
2. Substitution lemma
3. Inference rules
4. Axiom schemas
5. Modal logic S5 axiom schemas
6. Conservativity *)

(* == 1. Definitions == *)

(* Type of formulas *)
Inductive Fm :=
| falsum: Fm (* false formula *)
| svar: nat -> Fm (* schema variable *)
| conj: Fm -> Fm -> Fm (* conjunction *)
| disj: Fm -> Fm -> Fm (* disjunction *)
| subj: Fm -> Fm -> Fm (* subjunction *)
| nec: Fm -> Fm. (* neccesity *)

(* Usual approach to keep Fm smaller, *)
(* compatible with all common semantics *)
Definition verum: Fm := subj falsum falsum.
Definition neg (A: Fm): Fm := subj A falsum. (* negation *)
Definition equi (A B: Fm): Fm := conj (subj A B) (subj B A).
Definition seq (H A: Fm): Fm := nec (subj H A). (* sequent *)
Definition pos (A: Fm): Fm := neg (nec (neg A)). (* possibility *)

(* Valuation of a variable *)
Definition Val := nat -> Prop.

(* Valuation in a model *)
Definition World := Val.
Definition Model := World -> Val.

(* Generalized satisfaction *)
(* (M, v) ⊨ F *)
Fixpoint gsat (M: Model) (v: Val) (F: Fm): Prop :=
  match F with
  | falsum => False
  | svar A => M v A
  | conj A B => gsat M v A /\ gsat M v B
  | disj A B => gsat M v A \/ gsat M v B
  | subj A B => gsat M v A -> gsat M v B
  | nec A => forall w, gsat M w A
  end.

(* Generalized validity *)
(* ⊨ A *)
Definition gvalid (A: Fm): Prop :=
  forall M, forall v, gsat M v A.

(* Instance F[C:=D] of a schema F *)
Fixpoint inst (F: Fm) (C: nat) (D: Fm): Fm :=
  match F with
  | falsum => falsum
  | svar A => if Nat.eqb A C then D else svar A
  | conj A B => conj (inst A C D) (inst B C D)
  | disj A B => disj (inst A C D) (inst B C D)
  | subj A B => subj (inst A C D) (inst B C D)
  | nec A => nec (inst A C D)
  end.

(* Variant M[C:=P] of a model M *)
Definition variant (M: Model) (C: nat) (P: Val -> Prop): Model :=
  fun v A => if Nat.eqb A C then P v else M v A.

(* == 2. Substitution lemma == *)

Theorem subst_lemma (M: Model) (C: nat) (F D: Fm):
  forall v, gsat M v (inst F C D) <->
    gsat (variant M C (fun v => gsat M v D)) v F.
Proof.
  induction F as [ | A
  | A ihA B ihB | A ihA B ihB | A ihA B ihB | A ihA].
  * intro v. simpl gsat. apply iff_refl.
  * intro v. simpl gsat. unfold variant.
    destruct (Nat.eqb A C) eqn:E.
    - apply iff_refl.
    - simpl gsat. apply iff_refl.
  * intro v. simpl gsat.
    specialize (ihA v) as ihA.
    specialize (ihB v) as ihB.
    tauto.
  * intro v. simpl gsat.
    specialize (ihA v) as ihA.
    specialize (ihB v) as ihB.
    tauto.
  * intro v. simpl gsat.
    specialize (ihA v) as ihA.
    specialize (ihB v) as ihB.
    tauto.
  * intro v. split.
    - intro h. simpl gsat. intro w.
      specialize (ihA w). apply ihA in h. exact h.
    - intro h. simpl gsat. intro w.
      specialize (ihA w). apply ihA in h. exact h.
Qed.

(* == 3. Inference rules == *)

Theorem gvalid_inst_stability (F: Fm) (C: nat) (D: Fm):
  gvalid F -> gvalid (inst F C D).
Proof.
  intro h. unfold gvalid. intros M v.
  apply subst_lemma. apply h.
Qed.

Theorem neccesitation_is_gvalid (A: Fm):
  gvalid A -> gvalid (nec A).
Proof.
  unfold gvalid. intro h. intros M v. simpl gsat.
  intro w. specialize (h M w). exact h.
Qed.

Theorem modus_ponens_is_gvalid (A B: Fm):
  gvalid (subj A B) -> gvalid A -> gvalid B.
Proof.
  unfold gvalid. simpl gsat.
  intros h1 h2. intros M v.
  specialize (h1 M v). specialize (h2 M v).
  apply h1. exact h2.
Qed.

(* == 4. Axiom schemas == *)

Theorem conj_intro_is_gvalid (H1 H2 A B: Fm):
  gvalid (subj (seq H1 A) (subj (seq H2 B)
    (seq (conj H1 H2) (conj A B)))).
Proof.
  unfold gvalid. intros M v.
  simpl gsat. intros h1 h2.
  intro w. intro hw.
  specialize (h1 w).
  specialize (h2 w).
  destruct hw as (hw1, hw2).
  exact (Logic.conj (h1 hw1) (h2 hw2)).
Qed.

Theorem conj_eliml_is_gvalid (H A B: Fm):
  gvalid (subj (seq H (conj A B)) (seq H A)).
Proof.
  unfold gvalid. intros M v. simpl gsat. intro h.
  intro w. intro hw. specialize (h w).
  apply h. exact hw.
Qed.

Theorem conj_elimr_is_gvalid (H A B: Fm):
  gvalid (subj (seq H (conj A B)) (seq H B)).
Proof.
  unfold gvalid. intros M v. simpl gsat. intro h.
  intro w. intro hw. specialize (h w).
  apply h. exact hw.
Qed.

Theorem subj_intro_is_gvalid (H A B: Fm):
  gvalid (subj (seq (conj H A) B) (seq H (subj A B))).
Proof.
  unfold gvalid. intros M v. simpl gsat.
  intro h. intro w. intro hwH. intro hwA.
  specialize (h w). apply h. exact (Logic.conj hwH hwA).
Qed.

Theorem subj_elim_is_gvalid (H1 H2 A B: Fm):
  gvalid (subj (seq H1 (subj A B)) (subj (seq H2 A)
    (seq (conj H1 H2) B))).
Proof.
  unfold gvalid. intros M v. simpl gsat.
  intros h1 h2. intro w. intros (hw1, hw2).
  specialize (h1 w). specialize (h2 w).
  exact (h1 hw1 (h2 hw2)).
Qed.

Theorem neg_intro_is_gvalid (H A: Fm):
  gvalid (subj (seq (conj H A) falsum) (seq H (neg A))).
Proof.
  unfold neg. exact (subj_intro_is_gvalid H A falsum).
Qed.

Theorem neg_elim_is_gvalid (H1 H2 A: Fm):
  gvalid (subj (seq H1 (neg A)) (subj (seq H2 A)
    (seq (conj H1 H2) falsum))).
Proof.
  unfold neg. exact (subj_elim_is_gvalid H1 H2 A falsum).
Qed.

(* == 5. Modal logic S5 axiom schemas == *)

(* □(A → B) → (□A → □B) *)
Theorem axiom_K (A B: Fm):
  gvalid (subj (nec (subj A B)) (subj (nec A) (nec B))).
Proof.
  unfold gvalid. intros M v. simpl gsat. intro h1. intro h2.
  intro w. specialize (h1 w). specialize (h2 w).
  apply h1. exact h2.
Qed.

(* □A → A *)
Theorem axiom_T (A: Fm):
  gvalid (subj (nec A) A).
Proof.
  unfold gvalid. intros M v. simpl gsat. intro h.
  exact (h v).
Qed.

(* □A → □□A *)
Theorem axiom_4 (A: Fm):
  gvalid (subj (nec A) (nec (nec A))).
Proof.
  unfold gvalid. intros M v. simpl gsat. intro h.
  intros u w. exact (h w).
Qed.

(* ◇A → □◇A *)
Theorem axiom_5 (A: Fm):
  gvalid (subj (pos A) (nec (pos A))).
Proof.
  unfold gvalid. intros M v. simpl gsat. intro h1.
  intro u. intro h2. exact (h1 h2).
Qed.

(* 6. == Conservativity == *)

Fixpoint sat (v: Val) (F: Fm): Prop :=
  match F with
  | falsum => False
  | svar A => v A
  | conj A B => sat v A /\ sat v B
  | disj A B => sat v A \/ sat v B
  | subj A B => sat v A -> sat v B
  | nec A => forall w, sat w A
  end.

Definition valid (A: Fm): Prop :=
  forall v, sat v A.

Fixpoint nec_free (F: Fm): Prop :=
  match F with
  | falsum => True
  | svar _ => True
  | conj A B => nec_free A /\ nec_free B
  | disj A B => nec_free A /\ nec_free B
  | subj A B => nec_free A /\ nec_free B
  | nec _ => False
  end.

Theorem gsat_id_equiv (F: Fm):
  forall v, sat v F <-> gsat (fun w => w) v F.
Proof.
  induction F as [ | A
  | A ihA B ihB | A ihA B ihB | A ihA B ihB | A ihA].
  * intro v. simpl sat. simpl gsat. exact (iff_refl False).
  * intro v. simpl sat. simpl gsat. exact (iff_refl (v A)).
  * intro v. simpl sat. simpl gsat. split.
    - intros (h1, h2). split.
      -- apply ihA. exact h1.
      -- apply ihB. exact h2.
    - intros (h1, h2). split.
      -- apply ihA. exact h1.
      -- apply ihB. exact h2.
  * intro v. simpl sat. simpl gsat. split.
    - intro h. destruct h as [hl | hr].
      -- left. apply ihA. exact hl.
      -- right. apply ihB. exact hr.
    - intro h. destruct h as [hl | hr].
      -- left. apply ihA. exact hl.
      -- right. apply ihB. exact hr.
  * intro v. simpl sat. simpl gsat. split.
    - intros h1 h2. apply ihB. apply h1.
      apply ihA. exact h2.
    - intros h1 h2. apply ihB. apply h1.
      apply ihA. exact h2.
  * intro v. simpl sat. simpl gsat. split.
    - intro h. intro w. specialize (ihA w).
      apply ihA. exact (h w).
    - intro h. intro w. specialize (ihA w).
      apply ihA. exact (h w).
Qed.

Theorem conservativity (A: Fm):
  gvalid A -> valid A.
Proof.
  unfold gvalid. unfold valid. intro h.
  intro v. apply (gsat_id_equiv A v).
  exact (h (fun w => w) v).
Qed.

Theorem sat_gsat_equiv (F: Fm):
  nec_free F -> forall M v, sat (M v) F <-> gsat M v F.
Proof.
  induction F as [ | A
  | A ihA B ihB | A ihA B ihB | A ihA B ihB | A ihA].
  * intro h_nf. intro M. intro v.
    simpl sat. simpl gsat. exact (iff_refl False).
  * intro h_nf. intro M. intro v.
    simpl sat. simpl gsat. exact (iff_refl (M v A)).
  * intro h_nf. simpl nec_free in h_nf.
    destruct h_nf as [h_nfA h_nfB].
    specialize (ihA h_nfA). specialize (ihB h_nfB).
    intro M. intro v.
    specialize (ihA M v). specialize (ihB M v).
    simpl sat. simpl gsat. split.
    - intros [h1 h2]. split.
      -- apply ihA. exact h1.
      -- apply ihB. exact h2.
    - intros [h1 h2]. split.
      -- apply ihA. exact h1.
      -- apply ihB. exact h2.
  * intro h_nf. simpl nec_free in h_nf.
    destruct h_nf as [h_nfA h_nfB].
    specialize (ihA h_nfA). specialize (ihB h_nfB).
    intro M. intro v.
    specialize (ihA M v). specialize (ihB M v).
    simpl sat. simpl gsat. split.
    - intro h. destruct h as [hl | hr].
      -- left. apply ihA. exact hl.
      -- right. apply ihB. exact hr.
    - intro h. destruct h as [hl | hr].
      -- left. apply ihA. exact hl.
      -- right. apply ihB. exact hr.
  * intro h_nf. simpl nec_free in h_nf.
    destruct h_nf as [h_nfA h_nfB].
    specialize (ihA h_nfA). specialize (ihB h_nfB).
    intro M. intro v.
    specialize (ihA M v). specialize (ihB M v).
    simpl sat. simpl gsat. split.
    - intros h1 h2. apply ihB. apply h1.
      apply ihA. exact h2.
    - intros h1 h2. apply ihB. apply h1.
      apply ihA. exact h2.
  * intro h_nf. simpl nec_free in h_nf.
    destruct h_nf.
Qed.

Theorem conservativity_rev (A: Fm):
  nec_free A -> valid A -> gvalid A.
Proof.
  intro h_nf. unfold valid. unfold gvalid.
  intro h_val. intro M. intro v.
  apply (sat_gsat_equiv A h_nf M v).
  exact (h_val (M v)).
Qed.

Theorem conservativity_equi (A: Fm):
  nec_free A -> (gvalid A <-> valid A).
Proof.
  intro hnfA. split.
  * exact (conservativity A).
  * exact (conservativity_rev A hnfA).
Qed.

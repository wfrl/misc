
Require Import Sets.Ensembles.
Require Import Logic.ClassicalDescription.
Require Import Bool.Bool.

Inductive Formula :=
| var: nat -> Formula
| falsum: Formula
| subj: Formula -> Formula -> Formula.

Fixpoint sat (v: nat -> bool) (F: Formula): bool :=
  match F with
  | var P => v P
  | falsum => false
  | subj A B => negb (sat v A) || sat v B
  end.

Definition valid (A: Formula): Prop :=
  forall v: nat -> bool, sat v A = true.

Fixpoint ev (G: Type) (v: nat -> Ensemble G) (F: Formula): Ensemble G :=
  match F with
  | var P => v P
  | falsum => Empty_set G
  | subj A B => Union G (Complement G (ev G v A)) (ev G v B)
  end.

Definition set_valid (G: Type) (A: Formula): Prop :=
  forall v: nat -> Ensemble G, ev G v A = Full_set G.

Definition as_bool (A : Prop): bool :=
  match excluded_middle_informative A with
  | left _ => true
  | right _ => false
  end.

Lemma cancel_as_bool_true (A: Prop):
  as_bool A = true -> A.
Proof.
  unfold as_bool. intro h.
  destruct (excluded_middle_informative A) as [hA | hnA].
  * exact hA.
  * discriminate h.
Qed.

Lemma cancel_as_bool_false (A: Prop):
  as_bool A = false -> ~A.
Proof.
  unfold as_bool. intro h.
  destruct (excluded_middle_informative A) as [hA | hnA].
  * discriminate h.
  * exact hnA.
Qed.

Lemma intro_as_bool_true (A: Prop):
  A -> as_bool A = true.
Proof.
  intro h. unfold as_bool.
  destruct (excluded_middle_informative A) as [_ | hnA].
  * reflexivity.
  * exfalso. exact (hnA h).
Qed.

Lemma intro_as_bool_false (A: Prop):
  ~A -> as_bool A = false.
Proof.
  intro h. unfold as_bool.
  destruct (excluded_middle_informative A) as [hA | _].
  * exfalso. exact (h hA).
  * reflexivity.
Qed.

Lemma sat_lemma (G: Type) (x: G) (v: nat -> Ensemble G):
  forall F, sat (fun P => as_bool (In G (v P) x)) F = true <->
    In G (ev G v F) x.
Proof.
  intro F. induction F as [Q | | A ihA B ihB].
  * split.
    - intro h. simpl sat in h. simpl In.
      apply cancel_as_bool_true in h. exact h.
    - intro h. simpl sat. simpl In in h.
      apply intro_as_bool_true. exact h.
  * simpl sat. simpl ev. unfold In. split.
    - intro h. exfalso. discriminate h.
    - intro h. destruct h.
  * split.
    - intro h. simpl sat in h. apply orb_true_iff in h. simpl In.
      destruct h as [hl | hr].
      -- apply Union_introl. unfold In. unfold Complement.
         intro hcontra. apply ihA in hcontra.
         apply negb_true_iff in hl.
         rewrite hl in hcontra. discriminate hcontra.
      -- apply Union_intror. apply ihB. apply hr.
    - intro h. simpl sat. simpl In in h.
      unfold In in h. destruct h as [x hl | x hr].
      -- apply orb_true_iff. apply or_introl.
         apply negb_true_iff.
         unfold In in hl. unfold Complement in hl.
         apply not_true_is_false. intro hcontra.
         apply ihA in hcontra. exact (hl hcontra).
      -- apply orb_true_iff. apply or_intror.
         apply ihB. exact hr.
Qed.

Lemma sat_lemma_reverse (G: Type) (x: G) (v: nat -> bool):
  forall F, sat v F = true <->
    In G (ev G (fun P => fun _ => v P = true) F) x.
Proof.
  intro F. induction F as [Q | | A ihA B ihB].
  * simpl. unfold In.
    split.
    - intro h. exact h.
    - intro h. exact h.
  * simpl ev. simpl sat. unfold In. split.
    - intro h. exfalso. discriminate h.
    - intro h. destruct h.
  * simpl. unfold In. split.
    - intro h. apply orb_true_iff in h.
      destruct h as [hl | hr].
      -- apply Union_introl. intro hcontra.
         apply ihA in hcontra. apply negb_true_iff in hl.
         rewrite hl in hcontra. discriminate hcontra.
      -- apply Union_intror. apply ihB. exact hr.
    - intro h. apply orb_true_iff.
      destruct h as [y hl | y hr].
      -- left. apply negb_true_iff. apply not_true_is_false.
         intro hcontra. apply ihA in hcontra.
         exact (hl hcontra).
      -- right. apply ihB. exact hr.
Qed.

Theorem valid_implies_set_valid (G: Type) (A: Formula):
  valid A -> set_valid G A.
Proof.
  intro h. unfold set_valid. intro v.
  apply Extensionality_Ensembles.
  unfold Same_set. split.
  * unfold Included. intros x hx. apply Full_intro.
  * unfold Included. intros x hx.
    unfold valid in h.
    specialize h with (fun P => as_bool (In G (v P) x)).
    apply sat_lemma. exact h.
Qed.

Theorem set_valid_implies_valid (G: Type) (A: Formula):
  inhabited G -> set_valid G A -> valid A.
Proof.
  intros hG h v. unfold set_valid in h.
  specialize (h (fun P => fun _ => v P = true)).
  destruct hG as (x). apply (sat_lemma_reverse G x v).
  rewrite h. unfold In. apply Full_intro.
Qed.

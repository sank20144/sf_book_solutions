From LF Require Export Basics.

Theorem add_0_r_firsttry : forall n:nat,
  n + 0 = n.
Proof.
intros. Abort.

Theorem add_0_r_secondtry : forall n:nat,
  n + 0 = n.
Proof.
 intros n. destruct n as [| n'] eqn:E.
  - reflexivity.
  - simpl. Abort.

Theorem add_0_r : forall n:nat, n + 0 = n.
Proof.
  intros. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem minus_n_n : forall n, 
  minus n n = 0.
Proof.
  intros. induction n. 
  - reflexivity.
  - simpl. rewrite IHn. reflexivity. Qed.

Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  intros. induction n.
  - reflexivity.
  - simpl. rewrite IHn. reflexivity. Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros. induction n.
  - simpl. reflexivity.
  - simpl. rewrite IHn. reflexivity. Qed.

Theorem add_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros.
  - induction n. simpl. rewrite add_0_r. reflexivity.
    simpl. rewrite IHn. rewrite plus_n_Sm. reflexivity. Qed.

Theorem add_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros. induction n.
  - simpl. reflexivity.
  - simpl. rewrite IHn. reflexivity. Qed.

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n.
Proof.
  intros. induction n.
  - simpl. reflexivity.
  - simpl. rewrite IHn. rewrite plus_n_Sm. reflexivity. Qed.

Compute ltb 5 5.

Theorem eqb_refl : forall n : nat,
 (n =? n) = true.
Proof.
  


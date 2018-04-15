(* Credit goes to https://github.com/Lysxia for guiding in “solving” the puzzle. *)
Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.
Import ListNotations.

(* Define the rules as an inductive relation, one constructor for each rule. This relation describes the pairs of words that can be converted by applying one rule. *)

Inductive char : Type :=
  | M : char
  | I : char
  | U : char.

Inductive rule : list char -> list char -> Prop :=
  | rule_1 : forall x, rule (x ++ [I]) (x ++ [I; U])
  | rule_2 : forall x, rule ([M] ++ x) ([M] ++ x ++ x)
  | rule_3 : forall x y, rule (x ++ [I; I; I] ++ y) (x ++ [U] ++ y)
  | rule_4 : forall x y, rule (x ++ [U; U] ++ y) (x ++ y).

Notation "x => y" := (rule x y) (at level 50, left associativity).

Example test_rule1 : [M; I] => [M; I; U].
Proof. apply (rule_1 [M]). Qed.

Example test_rule2 : [M; I; U] => [M; I; U; I; U].
Proof. apply (rule_2 [I; U]). Qed.

Example test_rule3 : [M; U; I; I; I; I] => [M; U; U; I].
Proof. apply (rule_3 [M; U]). Qed.

Example test_rule4 : [M; U; U; I] => [M; I].
Proof. apply (rule_4 [M]). Qed.

(* Define its transitive closure. *)

Inductive tclos {A} (R : A -> A -> Prop) : A -> A -> Prop :=
  | tclos_axiom : forall a b, R a b -> tclos R a b
  | tclos_trans : forall a b c, tclos R a b -> tclos R b c -> tclos R a c.

Notation "x =>+ y" := (tclos rule x y) (at level 50, left associativity).

Example test_tclos :
  [M; I] =>+ [M; I; U] ->
  [M; I; U] =>+ [M; I; U; I; U] ->
  [M; I] =>+ [M; I; U; I; U].
Proof.
  intros T1 T2. apply tclos_trans with (b := [M; I; U]).
  assumption. assumption.
Qed.

(* Define the invariant. *)

Lemma eq_dec_char : forall n m : char, {n = m} + {n <> m}.
Proof. induction n; destruct m; try (now left); try (now right). Defined.

Definition count l x := count_occ eq_dec_char l x.

Definition invariant : list char -> Prop :=
  fun l => (Nat.modulo (count l I) 3) <> 0.

(* Show that the invariant is preserved by the rules. *)

Theorem count_app : forall l1 l2 x,
  count (l1 ++ l2) x = count l1 x + count l2 x.
Proof.
  induction l1.
  easy.
  intros l2 x. simpl. destruct (eq_dec_char a x).
  rewrite IHl1.
  simpl. reflexivity.
  rewrite IHl1. reflexivity.
Qed.

Theorem count_com : forall l1 l2 x,
  count (l1 ++ l2) x = count (l2 ++ l1) x.
Proof.
  induction l1.
  simpl. intros. rewrite app_nil_r. reflexivity.
  simpl. intros. destruct (eq_dec_char a x).
  rewrite e. rewrite count_app, count_app. simpl.
  destruct (eq_dec_char x x).
  omega.
  contradiction.
  rewrite count_app, count_app.
  simpl.
  destruct (eq_dec_char a x).
  contradict e.
  assumption.
  rewrite Nat.add_comm.
  reflexivity.
Qed.

Theorem unchanged_doubling : forall n,
  n mod 3 <> 0 ->
  (n + n) mod 3 <> 0.
Proof.
  intro.
  intros H. intuition.
  apply H. clear H.
  apply Nat.mod_divide.
  easy.
  apply Nat.mod_divide in H0.
  apply Nat.gauss with (m := 2).
  assert (n + n = 2 * n).
  { simpl. rewrite <- plus_n_O. reflexivity. }
  rewrite H in H0.
  assumption.
  simpl. reflexivity.
  easy.
Qed.

Theorem unchanged_minus_three : forall n,
  (n + 3) mod 3 <> 0 ->
  n mod 3 <> 0.
Proof.
  intro.
  intros H. intuition.
  apply H. clear H.
  assert (3 = 1 * 3).
  { reflexivity. }
  rewrite H at 1.
  rewrite Nat.mod_add.
  assumption.
  discriminate.
Qed.

Theorem unchanged_i : forall l1 l2,
  count l1 I = 0 ->
  (Nat.modulo (count l2 I) 3) <> 0 <->
  (Nat.modulo (count (l2 ++ l1) I) 3) <> 0.
Proof.
  split.
  - intros H1.
    rewrite count_app, H, Nat.add_0_r. assumption.
  - intros H1.
    rewrite count_app, H, Nat.add_0_r in H1.
    assumption.
Qed.

Theorem invariant_preserved: forall l1 l2,
  l1 => l2 -> invariant l1 -> invariant l2.
Proof.
  intros l1 l2 R I1.
  unfold invariant in *.
  induction R; subst.
  - assert (x ++ [I; U] = (x ++ [I]) ++ [U]).
    { rewrite app_assoc_reverse. simpl. reflexivity. }
    rewrite H. apply unchanged_i.
    simpl. reflexivity.
    assumption.
  - rewrite count_app, count_app.
    assert (count [M] I = 0).
    { simpl. reflexivity. }
    rewrite H, Nat.add_0_l.
    rewrite count_app, H, Nat.add_0_l in I1.
    apply unchanged_doubling. assumption.
  - rewrite count_app, count_app in I1.
    assert (count [I; I; I] I = 3).
    { simpl. reflexivity. }
    rewrite H, Nat.add_assoc, Nat.add_shuffle0 in I1.
    rewrite count_app, count_app.
    assert (count [U] I = 0).
    { simpl. reflexivity. }
    rewrite H0, Nat.add_0_l.
    apply unchanged_minus_three.
    assumption.
  - rewrite app_assoc, count_com, app_assoc in I1.
    apply unchanged_i in I1.
    rewrite count_com. assumption.
    reflexivity.
Qed.

Theorem invariant_preserved_trans: forall l1 l2, l1 =>+ l2 -> invariant l1 -> invariant l2.
Proof.
  intros. induction H.
  apply invariant_preserved in H. assumption. assumption.
  apply IHtclos2. apply IHtclos1. assumption.
Qed.

(* Show that one string satisfies the invariant while the other doesn't. *)

Theorem mi_invariant_preserved :
  invariant [M; I].
Proof. unfold invariant. discriminate. Qed.

Theorem mu_invariant_not_preserved :
  ~ invariant [M; U].
Proof. unfold invariant, not. contradiction. Qed.

(* Derive a contradiction from the assumption that there is a derivation between them. *)

Theorem mu_puzzle :
  ~ [M; I] =>+ [M; U].
Proof.
  unfold not. intros H.
  apply invariant_preserved_trans in H.
  contradict H.
  apply mu_invariant_not_preserved.
  apply mi_invariant_preserved.
Qed.

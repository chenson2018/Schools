(** Exercise sheet for lecture 4: Tactics in Coq.

  prepared using material by Ralph Matthes
 *)

(** * Exercise 1
Formalize the following types in UniMath and construct elements for them interactively -
if they exist. Give a counter-example otherwise, i.e., give specific parameters and a
proof of the negation of the statement.

[[
1.    A × (B + C) → A × B + A × C, given types A, B, C
2.    (A → A) → (A → A), given type A (for extra credit, write down five elements of this type)
3.    Id_nat (0, succ 0)
4.    ∑ (A : Universe) (A → empty) → empty
5.    ∏ (n : nat), ∑ (m : nat), Id_nat n (2 * m) + Id_nat n (2 * m + 1),
      assuming you have got arithmetic
6.    (∑ (x : A) B × P x) → B × ∑ (x : A) P x, given types A, B, and P : A → Universe
7.    B → (B → A) → A, given types A and B
8.    B → ∏ (A : Universe) (B → A) → A, given type B
9.    (∏ (A : Universe) (B → A) → A) → B, given type B
10.   x = y → y = x, for elements x and y of some type A
11.   x = y → y = z → x = z, for elements x, y, and z of some type A
]]

More precise instructions and hints:

1.  Use [⨿] in place of the + and pay attention to operator precedence.

2.  Write a function that provides different elements for any natural number argument,
    not just five elements; for extra credits: state correctly that they are different -
    for a good choice of [A]; for more extra credits: prove that they are different.

3.  An auxiliary function may be helpful (a well-known trick).

4.  The symbol for Sigma-types is [∑], not [Σ].

5.  Same as 1; and there is need for module [UniMath.Foundations.NaturalNumbers], e.g.,
    for Lemma [natpluscomm].

6.-9. no further particulars
*)

Require Import UniMath.Foundations.Preamble.
Require Import UniMath.Foundations.PartA.
Require Import UniMath.Foundations.NaturalNumbers.

Definition p_1_1 (A B C : UU) : A × (B ⨿ C) → (A × B) ⨿ (A × C).
Proof.
  intros [pr1 pr2].
  case pr2
  ; intros x
  ; [apply ii1 | apply ii2]
  ; constructor
  ; assumption.
Defined.

Definition p_1_2 (A : UU) : (A → A) → (A → A).
Proof. 
  intros f.
  exact f.
Defined.

Definition p_1_3 (h : 0 = 1) : ∅ .
Proof.
  assert (h' : 1 > 0) by reflexivity.
  apply isasymmnatgth with 0 1; induction h; exact h'.
  Show Proof.
Qed.

(* from Mukul Agarwal *)
Lemma ex3 : ¬ (0 = S 0).
Proof.
  intros neg.
  apply (transportf (nat_rect (λ _, UU) _ (λ _ _, ∅)) neg tt).
Qed.

Definition p_1_4 : ∑ (A : UU), (A -> empty) -> empty.
Proof.
  exists nat.
  intros f.
  apply f.
  apply 0.
Defined.

Definition p_1_4' {A : UU} (a : A) : (A -> ∅) -> ∅.
Proof.
  intros f.
  apply f.
  apply a.
Qed.

(* Unset Printing Notations. *)
Definition p_1_5 : 
    ∏ (n : nat), 
    ∑ (m : nat), 
    (paths n (2 * m)) ⨿ (paths n (2 * m + 1)).
Proof.
  (* couldn't find in Unimath... I'm probably just bad at searching *)
  assert (plus_one : forall x : nat, S x = x + 1).
  {  
    induction x.
    reflexivity.
    simpl.
    rewrite IHx.
    reflexivity.
  }
  (* couldn't find in Unimath... I'm probably just bad at searching *)
  assert (add_succ : forall x y, x + S y = S (x + y)).
  {
    induction x.
    - intros y.
      reflexivity.
    - intros y.
      simpl.
      rewrite IHx.
      reflexivity.
  }
  induction n.
  - exists 0.
    apply inl.
    reflexivity.
  - destruct IHn as [m' [e | o]].
    + exists m'.
      apply inr.
      rewrite e.
      apply plus_one.
    + exists (m' + 1).
      apply inl.
      rewrite o.
      repeat rewrite <- plus_one.
      simpl.
      rewrite add_succ.
      reflexivity.
Defined.

Definition p_1_6 (A B : UU) (P : A -> UU) : (∑ x, B × P x) → B × ∑ x, P x.
Proof.
  intros h.
  induction h as [pr1 [b pred_pr1]].
  constructor.
  - exact b.
  - exists pr1.
    exact pred_pr1.
Defined.

Definition p_1_7 (A B : UU) : B → (B → A) → A.
Proof.
  intros b f.
  exact (f b).
Defined.

Definition p_1_8 (B : UU) : B → ∏ A, (B -> A) -> A.
Proof.
  intros b A f.
  apply f.
  apply b.
Defined.

Definition p_1_9 (B : UU) : (∏ A, (B -> A) -> A) -> B.
Proof.
  intros h.
  specialize h with B.
  apply h.
  intros b.
  exact b.
Defined.

Definition p_1_10 {A : UU} (x y : A) : x = y → y = x.
Proof.
  intros h.
  induction h.
  reflexivity.
Defined.

Definition p_1_11 {A : UU} (x y z : A) : x = y → y = z → x = z.
Proof.
  intros h1 h2.
  induction h1.
  exact h2.
Defined.

(** * Exercise 2
Define two computable strict comparison operators for natural numbers based on the fact
that [m < n] iff [n - m <> 0] iff [(m+1) - n = 0]. Prove that the two operators are
equal (using function extensionality, i.e., [funextfunStatement] in the UniMath library).

It may be helpful to use the definitions of the exercises for lecture 2.
The following lemmas on substraction [sub] in the natural numbers may be
useful:

a) [sub n (S m) = pred (sub n m)]

b) [sub 0 n = 0]

c) [pred (sub 1 n) = 0]

d) [sub (S n) (S m) = sub n m]

*)

(** from exercises to Lecture 2: *)
Definition ifbool (A : UU) (x y : A) : bool -> A :=
  bool_rect (λ _ : bool, A) x y.

Definition negbool : bool -> bool := ifbool bool false true.

Definition nat_rec (A : UU) (a : A) (f : nat -> A -> A) : nat -> A :=
  nat_rect (λ _ : nat, A) a f.

Definition pred : nat -> nat := nat_rec nat 0 (fun x _ => x).

Definition is_zero : nat -> bool := nat_rec bool true (λ _ _, false).

Definition iter (A : UU) (a : A) (f : A → A) : nat → A :=
  nat_rec A a (λ _ y, f y).

Notation "f ̂ n" := (λ x, iter _ x f n) (at level 10).

Definition sub (m n : nat) : nat := pred ̂ n m.


Lemma pred_sub : forall (m n : nat), sub n (S m) = pred (sub n m).
Proof.
  induction m.
  - simpl. reflexivity.
  - intros.
    simpl.
    rewrite <- IHm.
    reflexivity.
Qed.

Lemma sub_zero : forall n, sub 0 n = 0.
Proof.
  induction n.
  - reflexivity.
  - simpl.
    rewrite IHn.
    reflexivity.
Qed.

Lemma pred_sub_one : forall (n : nat), pred (sub 1 n) = 0.
Proof.
  induction n.
  - reflexivity.
  - simpl.
    rewrite IHn.
    reflexivity.
Qed.

Lemma sub_succ_succ : forall (m n : nat), sub (S n) (S m) = sub n m.
Proof.
  intros.
  induction m.
  - simpl. reflexivity.
  - rewrite pred_sub.
    rewrite IHm.
    simpl.
    reflexivity.
Qed.

Lemma Exercise_2 : 
    (fun m n => is_zero (sub (S m) n))
    = 
    (fun m n => negbool (is_zero (sub n m))).
Proof.
  apply funextfun.
  intros m.
  induction m
  ; apply funextfun
  ; intros n
  ; induction n.
  - reflexivity.
  - simpl.
    rewrite pred_sub_one.
    reflexivity.
  - simpl.
    rewrite sub_zero.
    reflexivity.
  - repeat rewrite sub_succ_succ.
    apply (eqtohomot IHm).
Qed.

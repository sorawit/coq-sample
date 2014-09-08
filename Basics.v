Inductive day: Type := 
| monday: day
| tuesday: day
| wednesday: day
| thursday: day
| friday: day
| saturday: day
| sunday: day.

Definition next_weekday (d: day): day :=
        match d with
        | monday => tuesday
        | tuesday => wednesday
        | wednesday => thursday
        | thursday => friday
        | friday => monday
        | saturday => monday
        | sunday => monday
        end.

Eval compute in (next_weekday friday).
Eval compute in (next_weekday (next_weekday saturday)).

Definition nandb (b1: bool) (b2: bool): bool := negb (andb b1 b2).
Example test_nandb1: (nandb true false) = true.
Proof. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. reflexivity. Qed.
Example test_nandb4: (nandb false false) = true.
Proof. reflexivity. Qed.

Definition andb3 (b1: bool) (b2: bool) (b3: bool): bool := 
        andb (andb b1 b2) b3.
Example test_andb31: (andb3 true true true) = true.
Proof. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. reflexivity. Qed.

Fixpoint evenb (n: nat): bool :=
        match n with
        | O => true
        | S O => false
        | S (S n') => evenb n'
        end.

Definition oddb (n: nat): bool := negb (evenb n).

Fixpoint exp (base power: nat): nat :=
        match power with
        | O => S O
        | S p => mult base (exp base p)
        end.

Fixpoint factorial (n: nat): nat :=
        match n with
        | O => S O
        | S n' => mult n (factorial n')
        end.
Example test_factorial1: (factorial 3) = 6.
Proof. reflexivity. Qed.
Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. reflexivity. Qed.

Notation "x + y" := (plus x y)
        (at level 50, left associativity)
        : nat_scope.
Notation "x - y" := (minus x y)
        (at level 50, left associativity)
        : nat_scope.

Fixpoint beq_nat (n m: nat): bool := 
        match n, m with
        | O, O => true
        | O, S m' => false
        | S n', O => false
        | S n', S m' => beq_nat n' m'
        end.

Fixpoint ble_nat (n m: nat): bool := 
        match n, m with
        | O, _ => true
        | S _, O => false
        | S n', S m' => ble_nat n' m'
        end.
Example test_ble_nat1: (ble_nat 2 2) = true.
Proof. reflexivity. Qed.
Example test_ble_nat2: (ble_nat 2 4) = true.
Proof. reflexivity. Qed.
Example test_ble_nat3: (ble_nat 4 2) = false.
Proof. reflexivity. Qed.

Definition blt_nat (n m: nat): bool := andb (ble_nat n m) (negb (beq_nat n m)).
Example test_blt_nat1: (blt_nat 2 2) = false.
Proof. reflexivity. Qed.
Example test_blt_nat2: (blt_nat 2 4) = true.
Proof. reflexivity. Qed.
Example test_blt_nat3: (blt_nat 4 2) = false.
Proof. reflexivity. Qed.

Theorem plus_0_n: forall n: nat, 0 + n = n.
Proof.
        intros n.
        reflexivity.
Qed.

Theorem plus_1_n: forall n: nat, 1 + n = S n.
Proof. 
        intros n.
        reflexivity.
Qed.

Theorem mult_0_n: forall n: nat, 0 * n = 0.
Proof.
        intros n.
        reflexivity.
Qed.

Theorem plus_id_example: forall n m: nat, n = m -> n + n = m + m.
Proof.
        intros n m H.
        rewrite -> H.
        reflexivity.
Qed.

Theorem plus_id_exercise: forall n m o: nat, 
        n = m -> m = o -> n + m = m + o.
Proof.
        intros n m o HA HB.
        rewrite -> HA.
        rewrite -> HB.
        reflexivity.
Qed.

Theorem mult_0_plus: forall n m: nat,
        (0 + n) * m = n * m.
Proof.
        intros n m.
        rewrite -> plus_0_n.
        reflexivity.
Qed.

Theorem mult_S_1: forall n m: nat,
        m = S n -> m * (1 + n) = m * m.
Proof.
        intros n m H.
        rewrite -> H.
        rewrite <- plus_1_n.
        reflexivity.
Qed.

Theorem plus_1_neg_0: forall n: nat,
        beq_nat (n + 1) 0 = false.
Proof.
        intros n.
        destruct n as [| n'].
        reflexivity.
        reflexivity.
Qed.

Theorem negb_involutive: forall b: bool, negb (negb b) = b.
Proof.
        intros b.
        destruct b.
        reflexivity.
        reflexivity.
Qed.

Theorem zero_nbeg_plus1: forall n: nat,
        beq_nat 0 (n + 1) = false.
Proof.
        intros n.
        destruct n.
        reflexivity.
        reflexivity.
Qed.

Theorem identity_fn_applied_twice:
        forall f: bool -> bool,
        (forall x: bool, f x = x) -> forall b: bool, f (f b) = b.
Proof.
        intros f H x.
        rewrite -> H.
        rewrite -> H.
        reflexivity.
Qed.

Lemma andb_left_true: forall b: bool, (andb b true) = b.
Proof. destruct b. reflexivity. reflexivity. Qed.
Lemma andb_left_false: forall b: bool, (andb b false) = false.
Proof. destruct b. reflexivity. reflexivity. Qed.
Lemma orb_left_true: forall b: bool, (orb b true) = true.
Proof. destruct b. reflexivity. reflexivity. Qed.
Lemma orb_left_false: forall b: bool, (orb b false) = b.
Proof. destruct b. reflexivity. reflexivity. Qed.

Theorem andb_eq_orb: 
        forall b c: bool,
        (andb b c = orb b c) -> b = c.
Proof.
        intros b c.
        destruct c.
        rewrite -> andb_left_true. rewrite -> orb_left_true.
        intros HA. rewrite HA. reflexivity.
        rewrite -> andb_left_false. rewrite -> orb_left_false.
        intros HB. rewrite HB. reflexivity.
Qed.

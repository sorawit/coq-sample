Fixpoint evenb (n: nat): bool :=
    match n with
    | O => true
    | S O => false
    | S (S n') => evenb n'
    end.

Definition even (n: nat): Prop :=
    evenb n = true.

Inductive ev: nat -> Prop :=
| ev_0: ev O
| ev_SS: forall n: nat, ev n -> ev (S (S n)).

Fixpoint double (n: nat): nat :=
    match n with
    | O => O
    | S n' => S (S (double n'))
    end.

Theorem double_even: forall n, ev (double n).
Proof.
    intros n.
    induction n. apply ev_0.
    simpl. apply ev_SS. apply IHn.
Qed.

Theorem ev__even: forall n, ev n -> even n.
Proof.
    intros n E.
    induction E as [| n' E'].
    unfold even. reflexivity.
    unfold even. apply IHE'.
Qed.

Lemma plus_helper: forall n m: nat, (S n) + m = S (n + m).
Proof.
    intros n m.
    induction m as [| m'].
    reflexivity.
    reflexivity.
Qed.
Theorem ev_sum: forall n m,
    ev n -> ev m -> ev (n+m).
Proof.
    intros n m Hn Hm.
    induction Hn.
    apply Hm.
    rewrite -> plus_helper. rewrite -> plus_helper. apply ev_SS. apply IHHn.
Qed.

Inductive beautiful: nat -> Prop :=
| b_0: beautiful 0
| b_3: beautiful 3
| b_5: beautiful 5
| b_sum: forall n m, beautiful n -> beautiful m -> beautiful (n+m).

Theorem three_is_beautiful: beautiful 3.
Proof.
    apply b_3.
Qed.
Theorem eight_is_beautiful: beautiful 8.
Proof.
    apply b_sum with (n:=3) (m:=5).
    apply b_3.
    apply b_5.
Qed.
Theorem beautiful_plus_eight: forall n, beautiful n -> beautiful (n+8).
Proof.
    intros n B.
    apply b_sum with (m:=8).
    apply B. apply eight_is_beautiful.
Qed.
Theorem b_times2: forall n, beautiful n -> beautiful (2*n).
Proof.
    intros n B.
    simpl.
    apply b_sum with (n:=n) (m:=n+0).
    apply B.
    apply b_sum.
    apply B. apply b_0.
Qed.
Theorem b_times3: forall n, beautiful n -> beautiful (3*n).
Proof.
    intros n B.
    simpl.
    apply b_sum with (n:=n) (m:=n+(n+0)). apply B.
    apply b_times2. apply B.
Qed.

Inductive gorgeous: nat -> Prop :=
| g_0: gorgeous 0
| g_plus3: forall n, gorgeous n -> gorgeous (3+n)
| g_plus5: forall n, gorgeous n -> gorgeous (5+n).

Theorem gorgeous_plus13: forall n, gorgeous n -> gorgeous (13+n).
Proof.
    intros n B.
    apply g_plus3. apply g_plus5. apply g_plus5. apply B.
Qed.

Theorem gorgeous_beautiful: forall n, gorgeous n -> beautiful n.
Proof. 
    intros n H.
    induction H as [| n' | n'].
    apply b_0.
    apply b_sum. apply b_3. apply IHgorgeous.
    apply b_sum. apply b_5. apply IHgorgeous.
Qed.

Theorem gorgeous_sum: forall n m, gorgeous n -> gorgeous m -> gorgeous (n+m).
Proof.
    intros n m Hn Hm.
    induction Hn.
    apply Hm.
    apply g_plus3 with (n:=n+m). apply IHHn.
    apply g_plus5 with (n:=n+m). apply IHHn.
Qed.

Theorem ev_minus2: forall n, ev n -> ev (pred (pred n)).
Proof.
    intros n E.
    inversion E as [| n' E'].
    apply ev_0.
    apply E'.
Qed.

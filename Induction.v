Require Export Basics.

Require String. Open Scope string_scope.

Ltac move_to_top x := 
        match reverse goal with
        | H : _ |- _ => try move x after H
        end.

Tactic Notation "assert_eq" ident(x) constr(v) := 
        let H := fresh in 
        assert (x = v) as H by reflexivity;
        clear H.

Tactic Notation "Case_aux" ident(x) constr(name) := 
        first [
          set (x := name); move_to_top x
        | assert_eq x name; move_to_top x
        | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.

Theorem andb_true_elim1: forall b c : bool,
        andb b c = true -> b = true.
Proof.
        intros b c H.
        destruct b.
        Case "b = true".
        reflexivity.
        Case "b = false".
        rewrite <- H.
        reflexivity.
Qed.

Theorem nadb_true_elim2: forall b c: bool,
        andb b c = true -> c = true.
Proof.
        intros b c H.
        destruct c.
        Case "c = true".
        reflexivity.
        Case "c = false".
        rewrite <- H.
        destruct b.
        SCase "b = true".
        reflexivity.
        SCase "b = false".
        reflexivity.
Qed.

Theorem plus_0_r: forall n: nat, n + 0 = n.
Proof.
        intros n.
        induction n as [| n'].
        Case "n = 0". reflexivity.
        Case "n = S n'". simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem minus_diag: forall n: nat, minus n n = 0.
Proof.
        intros n. 
        induction n as [| n'].
        Case "n = 0". reflexivity.
        Case "n = S n'". simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem mult_0_r: forall n: nat, n * 0 = 0.
Proof.
        intros n.
        induction n as [| n'].
        Case "n = 0". reflexivity.
        Case "n = S n'". simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_n_Sm: forall n m: nat, S (n + m) = n + (S m).
Proof.
        intros n m.
        induction n as [| n'].
        Case "n = 0". simpl. reflexivity.
        Case "n = S n'". simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_comm: forall n m: nat, n + m = m + n.
Proof.
        intros n m.
        induction n as [| n'].
        Case "n = 0". simpl. rewrite -> plus_0_r. reflexivity.
        Case "n = S n'". simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. reflexivity.
Qed.

Theorem plus_assoc: forall n m p: nat, n + (m + p) = (n + m) + p.
Proof.
        intros n m p.
        induction n as [| n'].
        Case "n = 0". simpl. reflexivity.
        Case "n = S n'". simpl. rewrite -> IHn'. reflexivity.
Qed.

Fixpoint double (n: nat) := 
        match n with 
        | O => O
        | S n' => S (S (double n'))
        end.
Lemma double_plus: forall n: nat, double n = n + n.
Proof.
        intros n.
        induction n as [| n'].
        Case "n = 0". reflexivity.
        Case "n = S n'". simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. reflexivity.
Qed.

Theorem plus_swap: forall n m p: nat, n + (m + p) = m + (n + p).
Proof.
        intros n m p.
        assert (HA: n + (m + p) = (n + m) + p).
                rewrite -> plus_assoc. reflexivity.
        rewrite -> HA.
        assert (HB: (n + m) = (m + n)).
                rewrite -> plus_comm. reflexivity.
        rewrite -> HB.
        rewrite -> plus_assoc.
        reflexivity.
Qed.

Theorem mult_n_Sm: forall n m: nat, n + (n * m) = n * (S m).
Proof.
        intros n m.
        induction n as [| n'].
        Case "n = 0". simpl. reflexivity.
        Case "n = S n'". simpl. rewrite -> plus_swap. rewrite -> IHn'. reflexivity.
Qed.
Theorem mult_comm: forall m n: nat, m * n = n * m.
Proof.
        intros n m.
        induction n as [| n'].
        rewrite -> mult_0_r. reflexivity.
        simpl.
        rewrite <- mult_n_Sm. rewrite -> IHn'. reflexivity.
Qed.

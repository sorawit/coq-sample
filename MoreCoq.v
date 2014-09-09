Require Export Poly.

Theorem silly1: forall (n m o p: nat),
    n = m -> [n;o] = [n;p] -> [n;o] = [m;p].
Proof.
    intros n m o p eq1 eq2.
    rewrite <- eq1.
    apply eq2.
Qed.

Theorem silly2: forall (n m o p: nat),
    n = m -> (forall q r: nat, q = r -> [q;o] = [r;p]) -> [n;o] = [m;p].
Proof.
    intros n m o p eq1 eq2.
    apply eq2.
    apply eq1.
Qed.

Theorem silly2a: forall n m: nat,
    (n,n) = (m,m) -> (forall q r: nat, (q,q) = (r,r) -> [q] = [r]) ->
    [n] = [m].
Proof.
    intros n m eq1 eq2.
    apply eq2.
    apply eq1.
Qed.

Theorem silly_ex: (forall n, evenb n = true -> oddb (S n) = true) ->
    evenb 3 = true -> oddb 4 = true.
Proof.
    intros eq1.
    apply eq1.
Qed.

Theorem silly3: forall n: nat, true = beq_nat n 5 -> 
    beq_nat (S (S n)) 7 = true.
Proof.
    intros n H.
    symmetry.
    apply H.
Qed.

Example trans_eq_example: forall a b c d e f: nat,
    [a;b] = [c;d] ->
    [c;d] = [e;f] ->
    [a;b] = [e;f].
Proof.
    intros a b c d e f eq1 eq2.
    rewrite -> eq1.
    rewrite -> eq2.
    reflexivity.
Qed.

Theorem trans_eq: forall (X: Type) (n m o: X),
    n = m -> m = o -> n = o.
Proof. intros X n m o eq1 eq2. rewrite eq1. apply eq2. Qed.

Example trans_eq_example': forall a b c d e f: nat,
    [a;b] = [c;d] ->
    [c;d] = [e;f] ->
    [a;b] = [e;f].
Proof.
    intros a b c d e f eq1 eq2.
    apply trans_eq with (m:=[c;d]). apply eq1. apply eq2.
Qed.

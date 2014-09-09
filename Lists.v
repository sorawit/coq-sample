Require Export Induction.

Module NatList.

Inductive natprod: Type := 
        pair: nat -> nat -> natprod.
Notation "( x , y )" := (pair x y).

Definition fst (p: natprod): nat :=
        match p with
        | (x,y) => x
        end.
Definition snd (p: natprod): nat :=
        match p with
        | (x,y) => y
        end.
Definition swap_pair (p: natprod): natprod :=
        match p with
        | (x,y) => (y,x)
        end.

Theorem subjective_pairing: forall p: natprod, p = (fst p, snd p).
Proof.
        intros p.
        destruct p as [n m].
        reflexivity.
Qed.

Theorem fst_swap_is_snd: forall p: natprod, fst (swap_pair p) = snd p.
Proof.
        intros p.
        destruct p as [n m].
        reflexivity.
Qed.

Theorem snd_swap_is_fst: forall p: natprod, snd (swap_pair p) = fst p.
Proof.
        intros p.
        destruct p as [n m].
        reflexivity.
Qed.

Inductive natlist: Type :=
| nil: natlist
| cons: nat -> natlist -> natlist.

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) .. ).

Fixpoint repeat (n count: nat): natlist :=
        match count with
        | 0 => nil
        | S count' => n :: (repeat n count')
        end.

Fixpoint length (l: natlist): nat :=
        match l with
        | nil => O
        |  _ :: xs => S (length xs)
        end.

Fixpoint app (l1 l2: natlist): natlist :=
        match l1 with
        | nil => l2
        | x :: xs => x :: (app xs l2)
        end.

Notation "x ++ y" := (app x y) (at level 60, right associativity).
Example test_app1: [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity. Qed.
Example test_app2: nil ++ [4;5] = [4;5].
Proof. reflexivity. Qed.
Example test_app3: [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity. Qed.

Definition hd (default: nat) (l: natlist): nat :=
        match l with 
        | nil => default
        | x :: _ => x
        end.

Definition tl (l: natlist): natlist :=
        match l with
        | nil => nil
        | _ :: xs => xs
        end.
Example test_hd1: hd 0 [1;2;3] = 1.
Proof. reflexivity. Qed.
Example test_hd2: hd 0 [] = 0.
Proof. reflexivity. Qed.
Example test_tl: tl [1;2;3] = [2;3].
Proof. reflexivity. Qed.

Fixpoint nonzeros (l: natlist): natlist :=
        match l with
        | nil => nil
        | 0 :: xs => nonzeros xs 
        | x :: xs => x :: (nonzeros xs)
        end.
Example test_nonzeros: nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. reflexivity. Qed.

Fixpoint oddmembers (l: natlist): natlist :=
        match l with
        | nil => nil
        | x :: xs => (if evenb x then nil else [x]) ++ (oddmembers xs)
        end.
Example test_oddmembers: oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof. reflexivity. Qed.

Definition countoddmembers (l: natlist): nat := length (oddmembers l).

Example test_countoddmembers1: countoddmembers [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.
Example test_countoddmembers2: countoddmembers [0;2;4] = 0.
Proof. reflexivity. Qed.
Example test_countoddmembers3: countoddmembers nil = 0.
Proof. reflexivity. Qed.

Fixpoint alternate (l1 l2: natlist): natlist :=
        match l1, l2 with
        | nil, _ => l2
        | _, nil => l1
        | x :: xs, y :: ys => x :: y :: (alternate xs ys)
        end.
Example test_alternate1: alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof. reflexivity. Qed.
Example test_alternate2: alternate [1] [4;5;6] = [1;4;5;6].
Proof. reflexivity. Qed.
Example test_alternate3: alternate [1;2;3] [4] = [1;4;2;3].
Proof. reflexivity. Qed.
Example test_alternate4: alternate [] [20;30] = [20;30].
Proof. reflexivity. Qed.

Definition bag := natlist.

Fixpoint count (v: nat) (s: bag): nat :=
        match s with 
        | nil => 0
        | x :: xs => (if beq_nat x v then 1 else 0) + (count v xs)
        end.
Example test_count1: count 1 [1;2;3;1;4;1] = 3.
Proof. reflexivity. Qed.
Example test_count2: count 6 [1;2;3;1;4;1] = 0.
Proof. reflexivity. Qed.

Definition sum: bag -> bag -> bag := app.
Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof. reflexivity. Qed.

Definition add (v: nat) (s: bag): bag := sum [v] s.
Example test_add1: count 1 (add 1 [1;4;1]) = 3.
Proof. reflexivity. Qed.
Example test_add2: count 5 (add 1 [1;4;1]) = 0.
Proof. reflexivity. Qed.

Definition member (v: nat) (s: bag): bool := blt_nat 0 (count v s).
Example test_member1: member 1 [1;4;1] = true.
Proof. reflexivity. Qed.
Example test_member2: member 2 [1;4;1] = false.
Proof. reflexivity. Qed.

Fixpoint remove_one (v: nat) (s: bag): bag :=
        match s with
        | nil => nil
        | x :: xs => if beq_nat x v then xs else x :: (remove_one v xs)
        end.
Example test_remove_one1: count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_one2: count 5 (remove_one 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_one3: count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.
Example test_remove_one4: count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
Proof. reflexivity. Qed.

Fixpoint remove_all (v: nat) (s: bag): bag :=
        match s with
        | nil => nil
        | x :: xs => (if beq_nat x v then [] else [x]) ++ (remove_all v xs)
        end.
Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.
Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
Proof. reflexivity. Qed.

Fixpoint subset (s1 s2: bag): bool :=
        match s1 with 
        | nil => true
        | x :: xs => andb (member x s2) (subset xs (remove_one x s2))
        end.

Example test_subset1: subset [1;2] [2;1;4;1] = true.
Proof. reflexivity. Qed.
Example test_subset2: subset [1;2;2] [2;1;4;1] = false.
Proof. reflexivity. Qed.

Theorem nil_app: forall l: natlist, [] ++ l = l.
Proof. reflexivity. Qed.

Theorem tl_length_pred: forall l: natlist, pred (length l) = length (tl l).
Proof.
        intros l.
        destruct l as [| n l'].
        Case "l = nil". reflexivity.
        Case "l = cons n l'". reflexivity.
Qed.

Theorem app_assoc: forall l1 l2 l3: natlist, (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
        intros l1 l2 l3.
        induction l1 as [| n l1'].
        reflexivity.
        simpl. rewrite -> IHl1'. reflexivity.
Qed.

Theorem app_length: forall l1 l2: natlist, length (l1 ++ l2) = (length l1) + (length l2).
Proof.
        intros l1 l2.
        induction l1 as [| n l1'].
        reflexivity.
        simpl. rewrite -> IHl1'. reflexivity.
Qed.

Fixpoint snoc (l: natlist) (v: nat): natlist :=
        match l with 
        | nil => [v]
        | x :: xs => x :: (snoc xs v)
        end.

Fixpoint rev (l: natlist): natlist :=
        match l with
        | nil => nil
        | x :: xs => snoc (rev xs) x
        end.
Example test_rev1: rev [1;2;3] = [3;2;1].
Proof. reflexivity. Qed.
Example test_rev2: rev nil = nil.
Proof. reflexivity. Qed.

Theorem length_snoc: forall n: nat, forall l: natlist, 
        length (snoc l n) = S (length l).
Proof.
        intros n l.
        induction l as [| x xs].
        reflexivity.
        simpl. rewrite -> IHxs. reflexivity.
Qed.

Theorem rev_length: forall l: natlist, length (rev l) = length l.
Proof.
        intros l.
        induction l as [| x xs].
        reflexivity.
        simpl. rewrite -> length_snoc. rewrite -> IHxs. reflexivity.
Qed.

Theorem app_nil_end: forall l: natlist, l ++ [] = l.
Proof.
        intros l.
        induction l as [| x xs].
        reflexivity.
        simpl. rewrite -> IHxs. reflexivity.
Qed.

Lemma rev_snoc: forall n: nat, forall l: natlist, 
    rev (snoc l n) = n :: (rev l).
Proof.
    intros n l.
    induction l as [| x xs].
    reflexivity.
    simpl. rewrite -> IHxs. reflexivity.
Qed.

Theorem rev_innolutive: forall l: natlist, rev (rev l) = l.
Proof.
        intros l.
        induction l as [| x xs].
        reflexivity.
        simpl. rewrite -> rev_snoc. rewrite -> IHxs. reflexivity.
Qed.

Theorem app_assoc3: forall l1 l2 l3: natlist,
    l1 ++ (l2 ++ l3) = (l1 ++ l2) ++ l3.
Proof.
    intros l1 l2 l3.
    induction l1 as [| x xs].
    reflexivity.
    simpl. rewrite -> IHxs. reflexivity.
Qed.
Theorem app_assoc4: forall l1 l2 l3 l4: natlist,
    l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
    intros l1 l2 l3 l4.
    rewrite -> app_assoc3. rewrite -> app_assoc3. reflexivity.
Qed.

Theorem snoc_append: forall (l: natlist) (n: nat), 
    snoc l n = l ++ [n].
Proof.
    intros l n.
    induction l as [| x xs].
    reflexivity.
    simpl. rewrite -> IHxs. reflexivity.
Qed.

Theorem distr_rev: forall l1 l2: natlist, 
    rev (l1 ++ l2) = (rev l2) ++ (rev l1).
Proof.
    intros l1 l2.
    induction l1 as [| x xs].
    simpl. rewrite -> app_nil_end. reflexivity.
    simpl. rewrite -> IHxs. rewrite -> snoc_append. rewrite -> snoc_append.
    rewrite -> app_assoc3. reflexivity.
Qed.

Lemma nonzeros_app: forall l1 l2: natlist,
    nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
    intros l1 l2.
    induction l1 as [| x xs].
    reflexivity.
    destruct x.
    simpl. rewrite -> IHxs. reflexivity.
    simpl. rewrite -> IHxs. reflexivity.
Qed.

Fixpoint beq_natlist (l1 l2: natlist): bool := 
    match l1, l2 with
    | nil, nil => true
    | nil, _ => false
    | _, nil => false
    | x :: xs, y :: ys => if beq_nat x y then beq_natlist xs ys else false
    end.
Example test_beq_natlist1 : (beq_natlist nil nil = true).
Proof. reflexivity. Qed.
Example test_beq_natlist2 : beq_natlist [1;2;3] [1;2;3] = true.
Proof. reflexivity. Qed.
Example test_beq_natlist3 : beq_natlist [1;2;3] [1;2;4] = false.
Proof. reflexivity. Qed.

Theorem ben_natlist_refl: forall l: natlist,
    true = beq_natlist l l.
Proof.
    intros l.
    induction l as [| x xs].
    reflexivity.
    simpl. rewrite -> IHxs.
    assert (H: beq_nat x x = true).
    induction x as [| x'].
    reflexivity.
    simpl. rewrite -> IHx'. reflexivity.
    rewrite -> H. reflexivity.
Qed.

Theorem count_member_nonzero: forall s: bag,
    ble_nat 1 (count 1 (1 :: s)) = true.
Proof. reflexivity. Qed.

Theorem ble_n_Sn: forall n: nat,
    ble_nat n (S n) = true.
Proof.
    intros n.
    induction n as [| n'].
    reflexivity.
    simpl. rewrite IHn'. reflexivity.
Qed.

Theorem remove_decreases_count: forall s: bag,
    ble_nat (count 0 (remove_one 0 s)) (count 0 s) = true.
Proof.
    intros s.
    induction s as [| x xs].
    reflexivity.
    induction x as [| x'].
    rewrite -> ble_n_Sn. reflexivity.
    simpl.  rewrite -> IHxs. reflexivity.
Qed.

Inductive natoption: Type :=
| Some: nat -> natoption
| None: natoption.

Fixpoint index (n: nat) (l: natlist): natoption :=
    match l, n with
    | nil, _ => None
    | x :: _, O => Some x
    | _ :: xs, S n' => index n' xs
    end. 
Example test_index1 : index 0 [4;5;6;7] = Some 4.
Proof. reflexivity. Qed.
Example test_index2 : index 3 [4;5;6;7] = Some 7.
Proof. reflexivity. Qed.
Example test_index3 : index 10 [4;5;6;7] = None.
Proof. reflexivity. Qed.
   
Definition option_elim (d: nat) (o: natoption): nat :=
    match o with
    | Some n' => n'
    | None => d
    end.

Definition hd_opt (l: natlist): natoption :=
    match l with 
    | nil => None
    | x :: _ => Some x
    end.
Example test_hd_opt1 : hd_opt [] = None.
Proof. reflexivity. Qed.
Example test_hd_opt2 : hd_opt [1] = Some 1.
Proof. reflexivity. Qed.
Example test_hd_opt3 : hd_opt [5;6] = Some 5.
Proof. reflexivity. Qed.

Theorem option_elim_hd: forall l: natlist, forall default: nat,
    hd default l = option_elim default (hd_opt l).
Proof.
    intros l default.
    induction l as [| x xs].
    reflexivity.
    reflexivity.
Qed.

Module Dictionary.

Inductive dictionary: Type :=
| empty: dictionary
| record: nat -> nat -> dictionary -> dictionary.

Definition insert (key value: nat) (d: dictionary): dictionary :=
    record key value d.

Fixpoint find (key: nat) (d: dictionary): natoption :=
    match d with
    | empty => None
    | record k v d' => if beq_nat key k then Some v else find key d'
    end.

Theorem dictionary_invariant1': forall (d: dictionary) (k v: nat),
    (find k (insert k v d)) = Some v.
Proof.
    intros d k v.
    simpl.
    assert (H: beq_nat k k = true).
    induction k as [| k'].
    reflexivity.
    simpl. rewrite -> IHk'. reflexivity.
    rewrite -> H. reflexivity.
Qed.

End Dictionary.
End NatList.

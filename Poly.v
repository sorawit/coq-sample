Require Export Lists.

Inductive boollist: Type :=
| bool_nil: boollist
| bool_cons: bool -> boollist -> boollist.

Inductive list (X: Type): Type := 
| nil: list X
| cons: X -> list X -> list X.

Fixpoint length (X: Type) (l: list X): nat :=
    match l with
    | nil => 0
    | cons h t => S (length X t)
    end.
Example test_length1 :
        length nat (cons nat 1 (cons nat 2 (nil nat))) = 2.
Proof. reflexivity. Qed.
Example test_length2 :
        length bool (cons bool true (nil bool)) = 1.
Proof. reflexivity. Qed.

Fixpoint app (X : Type) (l1 l2 : list X)
    : (list X) :=
    match l1 with
    | nil => l2
    | cons h t => cons X h (app X t l2) 
    end.

Fixpoint snoc (X:Type) (l:list X) (v:X) : (list X) :=
    match l with
    | nil => cons X v (nil X)
    | cons h t => cons X h (snoc X t v)
    end.

Fixpoint rev (X:Type) (l:list X) : list X :=
    match l with
    | nil => nil X
    | cons h t => snoc X (rev X t) h
    end.

Example test_rev1 :
    rev nat (cons nat 1 (cons nat 2 (nil nat)))
    = (cons nat 2 (cons nat 1 (nil nat))).
Proof. reflexivity. Qed.

Example test_rev2:
    rev bool (nil bool) = nil bool.
Proof. reflexivity. Qed.

Module MumbleBaz.
Inductive mumble: Type :=
| a: mumble
| b: mumble -> nat -> mumble
| c: mumble.
Inductive grumble (X: Type): Type :=
| d: mumble -> grumble X
| e: X -> grumble X.

Inductive baz: Type :=
| x: baz -> baz
| y: baz -> bool -> baz.
End MumbleBaz.

Arguments nil {X}.
Arguments cons {X} _ _.
Arguments length {X} l.
Arguments app {X} l1 l2.
Arguments rev {X} l.
Arguments snoc {X} l v.
Notation "x :: y" := (cons x y)
    (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
    (at level 60, right associativity).

Fixpoint repeat {X: Type} (n: X) (count: nat): list X :=
    match count with
    | O => nil
    | S count' => cons n (repeat n count')
    end.
Example test_repeat1:
      repeat true 2 = cons true (cons true nil).
Proof. reflexivity. Qed.

Theorem nil_app: forall (X: Type) (l: list X), app [] l = l.
Proof. reflexivity. Qed.

(* Skipped polymorphic DS *)

Definition doit3times {X: Type} (f: X -> X) (n: X): X := f (f (f n)).
Example test_doit3times': doit3times negb true = false.
Proof. reflexivity. Qed.

Definition plus3 := plus 3.
Example test_plus3 : plus3 4 = 7.
Proof. reflexivity. Qed.
Example test_plus3' : doit3times plus3 0 = 9.
Proof. reflexivity. Qed.
Example test_plus3'' : doit3times (plus 3) 0 = 9.
Proof. reflexivity. Qed.

Definition prod_curry {X Y Z: Type} (f: X * Y -> Z) (x: X) (y: Y): Z :=
    f (x, y).
Definition prod_uncurry {X Y Z: Type} (f: X -> Y -> Z) (p: X * Y): Z :=
    match p with (x, y) => f x y end.
Theorem uncurry_curry : forall(X Y Z : Type) (f : X -> Y -> Z) x y,
    prod_curry (prod_uncurry f) x y = f x y.
Proof. reflexivity. Qed.
Theorem curry_uncurry : forall(X Y Z : Type) (f : (X * Y) -> Z) (p : X * Y),
    prod_uncurry (prod_curry f) p = f p.
Proof. Admitted.

Fixpoint filter {X: Type} (test: X -> bool) (l: list X): list X :=
    match l with
    | nil => []
    | x :: xs => if test x then x :: (filter test xs) else (filter test xs)
    end.
Example test_filter1: filter evenb [1;2;3;4] = [2;4].
Proof. reflexivity. Qed.

Definition length_is_1 {X : Type} (l : list X) : bool :=
    beq_nat (length l) 1.

Example test_filter2:
    filter length_is_1 [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
    = [ [3]; [4]; [8] ].
Proof. reflexivity. Qed.

Definition countoddmembers' (l:list nat) : nat :=
      length (filter oddb l).
Example test_countoddmembers'1: countoddmembers' [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.
Example test_countoddmembers'2: countoddmembers' [0;2;4] = 0.
Proof. reflexivity. Qed.
Example test_countoddmembers'3: countoddmembers' nil = 0.
Proof. reflexivity. Qed.

Example test_anon_fun':
    doit3times (fun n => n * n) 2 = 256.
Proof. reflexivity. Qed.
Example test_filter2':
    filter (fun l => beq_nat (length l) 1)
    [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ] = [ [3]; [4]; [8] ].
Proof. reflexivity. Qed.

Definition filter_even_gt7 (l: list nat): list nat :=
    filter (fun n => andb (evenb n) (ble_nat 7 n)) l.
Example test_filter_even_gt7_1 :
    filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
Proof. reflexivity. Qed.
Example test_filter_even_gt7_2 :
    filter_even_gt7 [5;2;6;19;129] = [].
Proof. reflexivity. Qed.

Definition partition {X: Type} (test: X -> bool) (l: list X): list X * list X :=
    pair (filter test l) (filter (fun n => negb (test n)) l).
Example test_partition1: partition oddb [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof. reflexivity. Qed.
Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof. reflexivity. Qed.

Fixpoint map {X Y: Type} (f: X -> Y) (l: list X): list Y :=
    match l with
    | nil => []
    | x :: xs => f x :: map f xs
    end.
Example test_map1: map (plus 3) [2;0;2] = [5;3;5].
Proof. reflexivity. Qed.
Example test_map2: map oddb [2;1;2;5] = [false;true;false;true].
Proof. reflexivity. Qed.
Example test_map3:
    map (fun n => [evenb n;oddb n]) [2;1;2;5]
    = [[true;false];[false;true];[true;false];[false;true]].
Proof. reflexivity. Qed.

Fixpoint fold {X Y: Type} (f: X -> Y -> Y) (l: list X) (b: Y): Y :=
    match l with
    | nil => b
    | x :: xs => f x (fold f xs b)
    end.
Example fold_example1 : fold mult [1;2;3;4] 1 = 24.
Proof. reflexivity. Qed.
Example fold_example2 : fold andb [true;true;false;true] true = false.
Proof. reflexivity. Qed.
Example fold_example3 : fold app [[1];[];[2;3];[4]] [] = [1;2;3;4].
Proof. reflexivity. Qed.

Definition constfun {X: Type} (x: X) : nat -> X :=
      fun (k:nat) => x.
Definition ftrue := constfun true.
Example constfun_example1 : ftrue 0 = true.
Proof. reflexivity. Qed.
Example constfun_example2 : (constfun 5) 99 = 5.
Proof. reflexivity. Qed.

Definition override {X: Type} (f: nat -> X) (k:nat) (x:X) : nat -> X:=
    fun (k':nat) => if beq_nat k k' then x else f k'.
Definition fmostlytrue := override (override ftrue 1 false) 3 false.
Example override_example1 : fmostlytrue 0 = true.
Proof. reflexivity. Qed.
Example override_example2 : fmostlytrue 1 = false.
Proof. reflexivity. Qed.
Example override_example3 : fmostlytrue 2 = true.
Proof. reflexivity. Qed.
Example override_example4 : fmostlytrue 3 = false.
Proof. reflexivity. Qed.

Theorem override_example: forall b: bool, 
    (override (constfun b) 3 true) 2 = b.
Proof.
    intros b.
    reflexivity.
Qed.

Theorem unfold_example: forall m n,
    3 + n = m -> plus3 n + 1 = m + 1.
Proof.
    intros n m H.
    unfold plus3.
    rewrite -> H.
    reflexivity.
Qed.

Theorem override_neq: forall (X: Type) x1 x2 k1 k2 (f: nat -> X),
    f k1 = x1 -> beq_nat k2 k1 = false -> (override f k2 x2) k1 = x1.
Proof.
    intros x x1 x2 k1 k2 f H1 H2.
    unfold override.
    rewrite -> H2.
    rewrite -> H1.
    reflexivity.
Qed.

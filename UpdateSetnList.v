(** Type **)
Variable X: Type.
Variable X': forall x x': X, x = x' \/ x <> x'.
Definition UpdateX (x: X) (f: X -> bool) (u: X -> X): X := if f x then u x else x.

(** List **)
Inductive list: Type :=
| nil: list
| cons: X -> list -> list.
Fixpoint InList (l: list) (e: X): Prop :=
    match l with 
    | nil => False
    | cons x xs => e = x \/ InList xs e
    end.
Fixpoint UpdateList (l: list) (f: X -> bool) (u: X -> X): list :=
    match l with
    | nil => nil
    | cons x xs => cons (if f x then u x else x) (UpdateList xs f u)
    end.

(** Set **)
Definition set := X -> Prop.
Definition InSet (s: set) (x: X): Prop := s x.
Definition Minus (s: set) (x: X): set := fun x0 => InSet s x0 /\ x <> x0.
Definition Add (s: set) (x: X): set := fun x0 => InSet s x0 \/ x = x0.
Definition UpdateSet (s: set) (f: X -> bool) (u: X -> X): set :=
    fun x0 => exists x: X, InSet s x /\ x0 = if f x then u x else x. 

(** Similarity Function **)
Definition Similar (l: list) (s: set): Prop := 
    forall x: X, InList l x <-> InSet s x.

(** Proof **)

(** Helping Lemmas **)
Lemma ClassicalOrInList: forall (l: list) (x: X), InList l x \/ ~ InList l x.
Proof.
    intros. induction l as [| h t].
        right. intuition.
        simpl. pose (X' x h). destruct o.
            intuition.
            destruct IHt.
                intuition.
                right. intuition.
Qed.

Lemma SimilarInclusive: forall (x: X) (xs: list) (s: set),
    Similar (cons x xs) s -> InList xs x -> Similar xs s.
Proof.
    unfold Similar in *. intros. pose (X' x0 x). destruct o.
        intuition.
            apply H. rewrite H1. simpl. left. intuition.
            rewrite H1. intuition.
        intuition.
            apply H. simpl. right. intuition.
            apply H in H2. simpl in H2. intuition.
Qed.

Lemma SimilarExclusive: forall (x: X) (xs: list) (s: set),
    Similar (cons x xs) s -> ~ InList xs x -> Similar xs (Minus s x).
Proof.
    unfold Similar in *. intros. intuition.
        unfold InSet, Minus. split.
            apply H. simpl. intuition.
            intuition. rewrite H2 in H0. intuition.
        unfold InSet, Minus in H1. intuition. apply H in H2. simpl in H2. intuition. rewrite H1 in H3.
        intuition.
Qed.
           
Lemma InSetMinusInvariant: forall (x x0: X) (s: set) (f: X -> bool) (u: X -> X),
    InSet (UpdateSet (Minus s x0) f u) x -> InSet (UpdateSet s f u) x.
Proof.
    intros. unfold InSet, UpdateSet in *. destruct H. intuition. case_eq (f x1).
        intros. rewrite H in H1. exists x1. intuition.
            unfold Minus in H0. destruct H0. intuition.
            rewrite H. intuition.
        intros. rewrite H in H1. exists x1. intuition.
            unfold Minus in H0. destruct H0. intuition.
            rewrite H. intuition.
Qed.

Lemma InSetMinusUpdatedInvariant: forall (x x0: X) (s: set) (f: X -> bool) (u: X -> X),
    InSet (UpdateSet s f u) x0 -> x0 <> UpdateX x f u -> InSet (UpdateSet (Minus s x) f u) x0. 
Proof.
    intros. unfold Minus, UpdateSet, InSet, UpdateX in *. destruct H. destruct H. exists x1. intuition.
    rewrite <- H2 in H1. intuition.
Qed.

(** Main Theorem **)
Theorem UpdateSimilarity: forall (l: list) (s: set) (f: X -> bool) (u: X -> X),
    Similar l s -> Similar (UpdateList l f u) (UpdateSet s f u).
Proof.
    unfold Similar in *. induction l as [| x xs].
    - split.
        simpl. intuition.
        intros. unfold InSet, UpdateSet in H0. destruct H0. intuition. apply H in H1. intuition.
    - split.
        simpl. intros. intuition.
            case_eq (f x).
                intros. rewrite H0 in H1. rewrite H1. unfold InSet, UpdateSet. exists x. split.
                    apply H. simpl. intuition.
                    rewrite H0. intuition.
                intros. rewrite H0 in H1. rewrite H1. unfold InSet, UpdateSet. exists x. split.
                    apply H. simpl. intuition.
                    rewrite H0. intuition.
            pose (ClassicalOrInList xs x). destruct o.
                apply IHxs.
                    apply SimilarInclusive with (x:=x).
                        intuition.
                        intuition.
                    assumption.
                apply InSetMinusInvariant with (x0:=x). apply IHxs.
                    apply SimilarExclusive.
                        intuition.
                        intuition.
                    intuition.
        intros. simpl. pose (X' x0 (if f x then u x else x)). intuition. right. pose (ClassicalOrInList xs x). destruct o.
            apply IHxs with (s:=s).
                apply SimilarInclusive with (x:=x).
                    intuition.
                    intuition.
                intuition.
            apply InSetMinusUpdatedInvariant with (x:=x) in H0.
                apply IHxs with (s:=(Minus s x)).
                    apply SimilarExclusive.
                        intuition.
                        intuition.
                    intuition.
                intuition.
Qed.

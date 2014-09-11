(** Type **)
Variable X: Type.

(** List **)
Inductive list: Type :=
| nil: list
| cons: X -> list -> list.

Fixpoint UpdateList (l: list) (f: X -> bool) (u: X -> X): list :=
    match l with
    | nil => nil
    | cons x xs => cons (if f x then u x else x) (UpdateList xs f u)
    end.

Fixpoint InList (l: list) (e: X): Prop :=
    match l with 
    | nil => False
    | cons x xs => e = x \/ InList xs e
    end.


(** Set **)
Definition set := X -> Prop.
Definition InSet (s: set) (x: X): Prop := s x.
Definition EmptySet: set := fun x => False.
Inductive UpdateSet (s: set) (f: X -> bool) (u: X -> X): set :=
| update_new: forall x: X, InSet s x -> f x = true -> InSet (UpdateSet s f u) (u x)
| update_old: forall x: X, InSet s x -> f x = false -> InSet (UpdateSet s f u) x.

(** Similarity Function **)
Definition similar (l: list) (s: set): Prop := 
    forall x: X, InList l x <-> InSet s x.

(** Proof **)
Lemma similar_with_null: forall s: set, similar nil EmptySet.
Proof.
    intros s.
    unfold similar. intros x. split. simpl. unfold EmptySet. unfold InSet. auto.
    simpl. unfold EmptySet. unfold InSet. auto.
Qed.
Theorem please_work: forall (l: list) (s: set) (f: X -> bool) (u: X -> X),
    similar l s -> similar (UpdateList l f u) (UpdateSet s f u).
Proof.
    induction l as [| x xs].
    simpl. unfold similar. intros. split. simpl. intuition.
    unfold InSet. intros. destruct H0. unfold similar in H. apply H in H0. 
    unfold InList in H0. contradiction. apply H. apply H0.
    unfold similar. intros. split. unfold similar in *. simpl. 
    intros. destruct H0. case_eq (f x). intros. rewrite H1 in H0. rewrite H0.
    constructor. apply H. simpl. intuition. intuition.
    intros. constructor. apply H. rewrite H1 in H0. rewrite H0. simpl.
    intuition. rewrite H1 in H0. rewrite <- H0 in H1. assumption.
    apply IHxs. 

Qed.

CoInductive Stream (A: Type): Type :=
    SCons: A -> Stream A -> Stream A.

Arguments SCons {_} _ _ .
Infix ":::" := SCons (at level 60, right associativity).

CoFixpoint repeat {A} (a: A) := a ::: (repeat a).
Notation "# a" := (repeat a) (at level 60).

Definition head {A} (s: Stream A): A := match s with x ::: _ => x end.
Definition tail {A} (s: Stream A): Stream A := 
    match s with _ ::: s => s end.

Notation "s '" := (tail s).

CoFixpoint map {A B} (f: A -> B) (s: Stream A): Stream B :=
    f (head s) ::: map f (s ').
CoFixpoint zipWith {A B C} (f: A -> B -> C)(s: Stream A)(t: Stream B): Stream C :=
    f (head s) (head t) ::: zipWith f (s ') (t ').

CoInductive equal {A} (s t: Stream A): Prop :=
    make_equal: head s = head t -> equal (s ') (t ') -> equal s t.

Notation "s === t" := (equal s t)(at level 60).


CoFixpoint repeat_map {A B} (f: A -> B) x: #(f x) === map f (#x) :=
    make_equal (#(f x)) (map f (#x)) eq_refl (repeat_map f x).
Lemma repeat_mapl {A B} (f: A -> B) x : #(f x) === map f (#x).
Proof.
cofix CH.
constructor.
- reflexivity.
- apply CH.
Qed.
Definition relation (A: Type):= A -> A -> Prop.
Definition bisimulation {A} (R: relation (Stream A)): Prop :=
    forall s t, R s t -> head s = head t /\ R (s ') (t ').

Lemma bisimulation_equal {A} (R: relation (Stream A)): forall  s t,
    bisimulation R -> R s t -> s ===t.
Proof.
cofix CH.
intros s t Hb HR.
pose proof (HBsim := Hb).
specialize (Hb _ _ HR) as [Hhead Htail].
constructor.
- exact Hhead.
- apply CH; auto.
Qed.

Fixpoint elt {A} (s: Stream A) (i: nat): A :=
    match i with 0 => head s | S j => elt (s ') j end.
Notation "s !! i" := (elt s i)(at level 60).

Lemma equal_elt {A} (s t: Stream A): s === t -> forall i, s !! i = t !! i.
Proof.
intros HC i.
revert HC.
revert s t.
revert i.
induction i; intros s t [HC1 HC2].
- assumption.
- apply IHi. exact HC2.
Qed.

From Stdlib Require Import Morphisms.
From Stdlib Require Import Classes.RelationClasses.

Instance equal_equivalence {A}: Equivalence (@equal A).
constructor.
- unfold Reflexive. cofix CH. 
    constructor;[reflexivity | apply CH].
- unfold Symmetric. cofix CH.
    intros x y [H1 H2].
    constructor;[auto | apply CH; exact H2].
- unfold Transitive. cofix CH.
    intros x y z [Hxy1 Hxy2] [Hyz1 Hyz2].
    constructor.
    + rewrite Hxy1. exact Hyz1.
    + apply CH with (y := y '); auto.
Qed.


Instance SCons_proper {A}: Proper (eq ==> (@equal A) ==> (@equal A)) SCons.
Proof.
intros x1 x2 Hx s1 s2 Hs.
subst x2.
constructor.
- reflexivity.
- exact Hs.
Qed.

Instance head_proper {A}: Proper (equal ==> eq) (@head A).
Proof.
intros s1 s2 [Hh _].
assumption.
Qed.

Instance tail_proper {A}: Proper (equal ==> equal) (@tail A).
Proof.
intros s1 s2 [_ Ht].
assumption.
Qed.

Instance map_proper {A B} :
    Proper ((pointwise_relation A eq) ==> (@equal A) ==> (@equal B)) (@map A B).
Proof.
cofix CH.
intros f g Hfg s1 s2 [H1 H2].
unfold pointwise_relation in Hfg.
constructor; simpl.
- rewrite H1. apply Hfg.
- apply CH; auto.
Qed.

Instance zipWith_proper {A B C} :
  Proper (pointwise_relation A (pointwise_relation B eq) ==> 
          (@equal A) ==> (@equal B) ==> (@equal C)) (@zipWith A B C).
Proof.
cofix CH.
intros f g Hfg s1 s2 [X1 X2] s3 s4 [X3 X4].
unfold pointwise_relation in Hfg.
constructor; simpl.
- rewrite X1. rewrite X3. apply Hfg.
- apply CH; auto.
Qed. 
 

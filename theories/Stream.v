CoInductive stream (A: Type): Type := SCons {
    shd: A;
    stl: stream A
}.

Notation "x ::: xs" := {|shd := x; stl:= xs |} (at level 60, right associativity).

CoFixpoint repeat {A} (a: A) := a ::: (repeat a).
Notation "# a" := (repeat a) (at level 60).

Arguments shd {A} _.
Arguments stl {A} _.

Notation "s '" := (stl s).
Notation "s `" := (shd s).

CoFixpoint smap {A B} (f: A -> B) (s: stream A): stream B :=
    f (s `) ::: smap f (s ').
CoFixpoint zipWith {A B C} (f: A -> B -> C)(s: stream A)(t: stream B): stream C :=
    f (s `) (t `) ::: zipWith f (s ') (t ').

CoInductive equal {A} (s t: stream A): Prop := {
    head_equal: (s `) = (t `);
    tail_equal: equal (s ') (t ')
}.

Arguments head_equal {A} _ _.
Arguments tail_equal {A} _ _.

Notation "s === t" := (equal s t)(at level 60).


Definition head_repeat_map {A B} (f: A -> B) (x: A):
    (# (f x)) ` = (smap f (#x)) `.
Proof. reflexivity. Qed.
(* Using eq_refl or even ltac:(reflexivity) for head_equal will make tail_equal fail as unification match t to be syntactically exactaily s*)
CoFixpoint repeat_map {A B} (f : A -> B) (x : A) :
    #(f x) === smap f (#x) :=
  {| 
    head_equal := head_repeat_map f x; 
    tail_equal := repeat_map f x
  |}.
Lemma repeat_mapl {A B} (f: A -> B) x : #(f x) === smap f (#x).
Proof.
cofix CH.
constructor.
- reflexivity.
- apply CH.
Qed.

CoFixpoint eq_stream_refl {A} (s: stream A): s === s := {|
    head_equal:= eq_refl;
    tail_equal:= eq_stream_refl (s ')
|}.

From Stdlib Require Import List.
Import ListNotations.
Check shd.

CoFixpoint crop {A} (xss: list (stream A))
    (yss: stream (stream A)): stream (list A) := {|
        shd := map shd xss;
        stl := crop (map stl (xss ++ [yss `])) (yss ')
    |}.



Definition relation (A: Type):= A -> A -> Prop.
Definition bisimulation {A} (R: relation (stream A)): Prop :=
    forall s t, R s t -> (s `) = (t `) /\ R (s ') (t ').

Lemma bisimulation_equal {A} (R: relation (stream A)): forall  s t,
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


Fixpoint elt {A} (s: stream A) (i: nat): A :=
    match i with 
    | 0 => s  `
    | S j => elt (s ') j 
    end.
Notation "s !! i" := (elt s i)(at level 60).

Lemma equal_elt {A} (s t: stream A):
    s === t -> forall i, s !! i = t !! i.
Proof.
intros HC i.
revert HC.
revert s t.
revert i.
induction i; intros s t [HC1 HC2].
- assumption.
- apply IHi. exact HC2.
Qed.



From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Classes.RelationClasses.

Instance equal_equivalence {A}: Equivalence (@equal A).
Proof.
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

(*
Instance SCons_proper {A}: Proper (eq ==> (@equal A) ==> (@equal A)) SCons.
Proof.
intros x1 x2 Hx s1 s2 Hs.
subst x2.
constructor.
- reflexivity.
- exact Hs.
Qed.
*)

Instance head_proper {A}: Proper (equal ==> eq) (@shd A).
Proof.
intros s1 s2 [Hh _].
exact Hh.
Qed.

Instance tail_proper {A}: Proper (equal ==> equal) (@stl A).
Proof.
intros s1 s2 [_ Ht].
exact Ht.
Qed.

Instance map_proper {A B} :
    Proper ((pointwise_relation A eq) ==> (@equal A) ==> (@equal B)) (@smap A B).
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

Lemma zipWith_map {A B C} 
    (f: A -> B -> C)(g: A -> B)(s t: stream A):
    s === t -> 
    zipWith f s (smap g t) === zipWith f t (smap g s).
Proof.
intro Hst.
setoid_rewrite Hst.
reflexivity.
Qed.

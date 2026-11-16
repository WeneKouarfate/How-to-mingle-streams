From Stdlib Require Import List.
Import ListNotations.

From Mingle Require Export Stream.


Arguments app {A} _.
(* Infix "<++>" := (zipWith app)(at level 60, right associativity). *)
Notation "x <++> y" := (zipWith app x y)(at level 60, right associativity).
Definition emp: stream (list nat) := (# []).
Check zipWith app emp emp.
Check emp <++> emp.
 

Infix "<:>" := (zipWith cons)(at level 61, no associativity).





CoFixpoint crop {A} (xss: list (stream A))
    (yss: stream (stream A)): stream (list A) := {|
        shd := map shd xss;
        stl := crop (map stl xss ++ [yss `]) (yss ')
    |}.

Definition diags {A} (xss: stream (stream A)): stream (list A) :=
    crop [xss `] (xss ').

CoFixpoint ssucc n := n ::: (ssucc (S n)).
Definition snat := ssucc 0.

Fixpoint take {A} (n: nat) (xss: stream A) := match n with
    | 0 => []
    | S m => (xss `) :: (take m (xss '))
    end.

Definition sharp_snat := (# snat).

Eval compute in take 9 sharp_snat.

CoFixpoint cols {A} (xss: list (stream A)): stream (list A):= {|
    shd := map shd xss;
    stl := cols (map stl xss)
|}.

CoFixpoint unfold {A B} (f: B -> (A * B))(b: B): stream A :=
    let (a, b') := f b in a ::: (unfold f b').

Definition diags2 {A} (xss: stream (stream A))
    : stream (list A) :=
    unfold
      (fun '(active, remaining) =>
        (map shd active,
         (map stl active ++ [shd remaining],
          stl remaining)))
      ([shd xss], stl xss).



Lemma zip_app_assoc {A}:
    forall xss yss zss: stream (list A),
    (xss <++> yss) <++> zss ===
    xss <++> (yss <++> zss).
Proof.
cofix CH.
intros xss yss zss.
constructor.
- simpl. symmetry. apply app_assoc.
- apply CH.
Qed.

Lemma cols_app {A}:
    forall xss yss: list (stream A),
    cols (xss ++ yss) === cols xss <++> cols yss.
Proof.
Admitted.


Theorem crop_cols_diags1 {A}
    (xss: list (stream A))
    (yss: stream (stream A)) :
    crop xss yss ===
      cols xss <++> ([] ::: diags1 yss).




Lemma diags2_unfold {A} (xss : stream (stream A)) :
  diags xss === (shd xss) <:> ([] ::: diags (stl xss)).
  Proof.
  Admitted.









    


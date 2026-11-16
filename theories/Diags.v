From Stdlib Require Import List.
Import ListNotations.

From Mingle Require Export Stream.

Infix "<++>" := (zipWith app)(at level 60, right associativity). 
Infix "<:>" := (zipWith cons)(at level 61, no associativity).

CoFixpoint crop {A} (xss: list (stream A))
    (yss: stream (stream A)): stream (list A) := {|
        shd := map shd xss;
        stl := crop (map stl (xss ++ [yss `])) (yss ')
    |}.

Definition diags1 {A} (xss: stream (stream A)): stream (list A) :=
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

Lemma diags2_unfold {A} (xss : stream (stream A)) :
  diags1 xss === zipWith cons (shd xss) ([] ::: diags1 (stl xss)).

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


CoFixpoint diags2 {A} (xss : stream (stream A)) : stream (list A) :=
  {| shd := [hd (hd xss)];
     stl := zipWith cons (tl (hd xss)) (diags2 (tl xss)) |}.

CoFixpoint cols {A} (xss: list (stream A)): stream (list A) := {|
    shd := map shd xss;
    stl := cols (map stl xss)
|}.







    


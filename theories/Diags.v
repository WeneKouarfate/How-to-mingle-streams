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

CoFixpoint diags2 {A} (xss: stream (stream A)): stream (list A) := {|
    shd := [(xss `)`];
    stl := ((xss `) ') <:> diags2 (xss ') 
|}.

CoFixpoint cols {A} (xss: list (stream A)): stream (list A) := {|
    shd := map shd xss;
    stl := cols (map stl xss)
|}.







    


Load "Game".

Require Import Coq.Vectors.Vector.
From Coq Require Import List.
Import ListNotations.
Import VectorNotations.


Record Tournament (k : nat) := {
    strategies : t Strategy k;
    games : t (t Game k) k
}.


Definition start_tournament {k : nat} (strats : t Strategy k) : Tournament k :=
  {| strategies := strats;
     games := Vector.const (Vector.const (nil : Game) k) k |}.


Definition play_tournament {k : nat} (tour : Tournament k) : Tournament k :=
  {|
    strategies := strategies k tour;
    games := map2 (
        fun s1 row => map2 (
            fun s2 g =>
                play g s1 s2
            )
            (strategies k tour) row
        ) (strategies k tour) (games k tour)
  |}.

Fixpoint play_tournament_many {k : nat} (tour : Tournament k) (n : nat) : Tournament k :=
  match n with
  | 0 => tour
  | S n' => play_tournament (play_tournament_many tour n')
  end.

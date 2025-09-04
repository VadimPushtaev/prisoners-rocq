Load "Game".

Require Import Coq.Vectors.Vector.
From Coq Require Import List.
Import ListNotations.
Import VectorNotations.

Definition symmetric {A k} (M : t (t A k) k) : Prop :=
  forall (i j : Fin.t k),
    @Vector.nth A k (@Vector.nth (t A k) k M i) j
  = @Vector.nth A k (@Vector.nth (t A k) k M j) i.

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

(* Playing tournament N times and then again is the same as playing it N+1 times *)
Theorem play_tournament_many_N_plus_1 :
  forall (k : nat) (tour : Tournament k) (n : nat),
  play_tournament_many tour (S n) = play_tournament (play_tournament_many tour n).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

(* Playing many and then once is the same as playing once and then many *)
Theorem play_tournament_many_plus_1_eq_1_plus_many :
  forall (k : nat) (tour : Tournament k) (n : nat),
  play_tournament (play_tournament_many tour n) = play_tournament_many (play_tournament tour) n.
Proof.
  intros.
  simpl.
  induction n.
  * simpl. reflexivity.
  * rewrite play_tournament_many_N_plus_1.
    rewrite play_tournament_many_N_plus_1.
    rewrite IHn.
    reflexivity.
Qed.

(* Playing tournament once and then N times is the same as playing it N+1 times *)
Theorem play_tournament_many_1_plus_N :
  forall (k : nat) (tour : Tournament k) (n : nat),
  play_tournament_many tour (S n) = play_tournament_many (play_tournament tour) n.
Proof.
  intros.
  simpl.
  rewrite play_tournament_many_plus_1_eq_1_plus_many.
  reflexivity.
Qed.

(* Playing tourname once gives symmteric matrix *)
Theorem play_tournament_once_gives_symmetric_matrix :
  forall (k : nat) (tour : Tournament k),
  symmetric (games k (play_tournament tour)).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

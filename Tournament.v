Load "Game.v".

Require Import Coq.Vectors.Vector.
From Coq Require Import List.
Import ListNotations.
Import VectorNotations.

Definition symmetric_games {k} (M : t (t Game k) k) : Prop :=
  forall (i j : Fin.t k),
    Vector.nth (Vector.nth M i) j
  = swap_game (Vector.nth (Vector.nth M j) i).

Record Tournament (k : nat) := { 
  strategies : t Strategy k;   
  games : t (t Game k) k       
}.                               

Definition tournament_result {k} (tour : Tournament k)
  : t (t (nat*nat) k) k :=
  Vector.map (fun row => Vector.map game_result row) (games k tour).

Definition sum_tournament_result {k} (result : t (t (nat*nat) k) k) : (t nat k) :=
  Vector.map (fun row => 
    Vector.fold_left (fun acc game => fst game + acc) 0 row
  ) result.

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

Definition get_ij_game {k : nat} (tour : Tournament k) (i j : Fin.t k) : Game :=
  Vector.nth (Vector.nth (games k tour) i) j.

Lemma get_ij_game_fold :
  forall (k : nat) (tour : Tournament k) (i j : Fin.t k),
  (((games k (tour))[@i])[@j]) = (get_ij_game (tour) i j).
Proof.
  intros.
  unfold get_ij_game.
  reflexivity.
Qed.

Definition get_idx_strategy {k : nat} (tour : Tournament k) (i : Fin.t k) : Strategy :=
  Vector.nth (strategies k tour) i.

(* Playing tournament and then getting games for (i, j) is the same as *)
(* getting games for (i, j) and then playing one more game with (i, j)-strategies *)
Theorem play_tournament_ij :
  forall (k : nat) (tour : Tournament k) (i j : Fin.t k),
  get_ij_game (play_tournament tour) i j
  = play (get_ij_game tour i j) (get_idx_strategy tour i) (get_idx_strategy tour j).
Proof.
  intros.
  unfold play_tournament.
  unfold get_ij_game.
  simpl.
  rewrite nth_map2 with (p2 := i) (p3 := i).
  rewrite nth_map2 with (p2 := j) (p3 := j).
  unfold get_idx_strategy.
  all: reflexivity.
Qed.

(* const+const gives symmetric matrix *)
Theorem const_const_gives_symmetric_matrix :
  forall (k : nat) (g : Game),
  g = swap_game g -> symmetric_games (Vector.const (Vector.const g k) k).
Proof.
  intros.
  unfold symmetric_games.
  intros.
  repeat rewrite const_nth.
  apply H.
Qed.

(* Games matrix stays symmetric after one play *)
Theorem games_matrix_stays_symmetric :
  forall (k : nat) (tour : Tournament k),
  symmetric_games (games k tour) -> symmetric_games (games k (play_tournament tour)).
Proof.
  unfold symmetric_games.
  intros.
  repeat rewrite get_ij_game_fold.
  repeat rewrite play_tournament_ij.
  rewrite swap_game_again.

  unfold get_ij_game.
  rewrite H.
  simpl.
  repeat rewrite swap_game_double.

  auto.
Qed.

(* Games matrix is symmetric after start and play *)
Theorem games_matrix_is_symmetric_after_start_and_play :
  forall (k : nat) (strats : t Strategy k),
  symmetric_games (games k (play_tournament (start_tournament strats))).
Proof.
  intros.
  apply games_matrix_stays_symmetric.
  unfold start_tournament.
  simpl.
  apply const_const_gives_symmetric_matrix.
  reflexivity.
Qed.

(* Games matrix is symmetric after start and play many times *)
Theorem games_matrix_is_symmetric_many_times :
  forall (k : nat) (strats : t Strategy k) (n : nat),
  symmetric_games (games k (play_tournament_many (start_tournament strats) n)).
Proof.
  intros.
  induction n.
  * simpl.
    apply const_const_gives_symmetric_matrix.
    reflexivity.
  * rewrite play_tournament_many_N_plus_1.
    apply games_matrix_stays_symmetric.
    apply IHn.
Qed.

Lemma tournament_result_idx :
(* Vector.map (fun row => Vector.map game_result row) (games k tour) *)
  forall (k : nat) (tour : Tournament k) (i : Fin.t k),
  (tournament_result tour)[@i] =
  Vector.map game_result ((games k tour)[@i]).
Proof.
  intros.
  unfold tournament_result.
  rewrite nth_map with (p2 := i).
  all: reflexivity.
Qed.

(* Equal strategies give equal results *)
Theorem equal_strategies_give_equal_results :
  forall (k: nat) (strats : t Strategy k) (i j : Fin.t k),
  strats[@i] = strats[@j] ->
  (tournament_result (play_tournament (start_tournament strats)))[@i] =
  (tournament_result (play_tournament (start_tournament strats)))[@j].
Proof.
  intros.
  repeat rewrite tournament_result_idx.
  apply f_equal.

  simpl.
  rewrite nth_map2 with (p2 := i) (p3 := i).
  rewrite nth_map2 with (p2 := j) (p3 := j).

  rewrite H.
  repeat rewrite const_nth.
  all: reflexivity.
Qed.    

Compute  (tournament_result (play_tournament_many (start_tournament [st_always_true; st_always_false; st_tit_for_tat; st_tit_for_tat]) 10)). 
Compute sum_tournament_result (tournament_result (play_tournament_many (start_tournament [st_always_true; st_always_false; st_tit_for_tat; st_tit_for_tat]) 10)).
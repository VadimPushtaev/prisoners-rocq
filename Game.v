From Coq Require Import List.
Import ListNotations.


Definition Game := list (bool * bool).

Definition Strategy := Game -> bool.

Definition swap_game (g : Game) : Game :=
  map (fun '(b1, b2) => (b2, b1)) g.

Definition game_last (g : Game) : bool * (bool * bool) :=
  match g with
  | [] => (false, (false, false))
  | (b1, b2) :: g' => (true, (b1, b2))
  end.

Definition play (g : Game) (s1 s2 : Strategy) : Game :=
  g ++ [(s1 g, s2 (swap_game g))].



(* Strategies *)
Definition st_always_true : Strategy :=
  fun (_ : Game) => true.



(* Proofs *)

(* game_last: first bool is false only for empty game *)
Theorem game_last_false_first :
  forall g : Game,
    fst (game_last g) = false <-> g = [].
Proof.
  split.
  - intros H.
    destruct g.
    + reflexivity.
    + destruct p.
      simpl in H. discriminate H.
  - intros H.
    destruct g.
    + reflexivity.
    + destruct p.
      destruct g.
      discriminate H.
      discriminate H.
Qed.   

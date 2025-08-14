From Coq Require Import List.
Import ListNotations.
From Coq Require Import String Ascii.


Definition Game := list (bool * bool).

Definition Strategy := Game -> bool.

Definition swap_game (g : Game) : Game :=
  map (fun '(b1, b2) => (b2, b1)) g.

Fixpoint game_last (g : Game) : bool * (bool * bool) :=
  match g with
  | [] => (false, (false, false))
  | (b1, b2) :: g' =>
    match g' with
    | [] => (true, (b1, b2))
    | (_, _) :: _ => game_last g'
    end
  end.

Definition game_to_string (g : Game) : string :=
  let fix rows (g' : Game) : string * string :=
    match g' with
    | [] => (""%string, ""%string)
    | (b1, b2) :: tl =>
        let '(top, bottom) := rows tl in
        (String.append (if b1 then "1"%string else "0"%string) top,
         String.append (if b2 then "1"%string else "0"%string) bottom)
    end in
  let newline := String (Ascii.ascii_of_nat 10) ""%string in
  let '(top_row, bottom_row) := rows g in
  String.append (String.append newline (String.append top_row (String.append newline bottom_row))) newline.




Definition play (g : Game) (s1 s2 : Strategy) : Game :=
  g ++ [(s1 g, s2 (swap_game g))].

Fixpoint play_many (g : Game) (s1 s2 : Strategy) (n : nat) : Game :=
  match n with
  | 0 => g
  | S n' => play_many (play g s1 s2) s1 s2 n'
  end.


(* Strategies *)
Definition st_always_true : Strategy :=
  fun (_ : Game) => true.

Compute (game_to_string (play_many [] st_always_true st_always_true 10)).



(* Proofs *)

(* game_last: first bool is false only for empty game *)
Theorem game_last_false_first :
  forall (g: Game) (r1 r2: bool),
    (game_last g) = (false, (r1, r2)) -> g = [].
Proof.
  intros g r1 r2 H.
  induction g.
  * reflexivity.
  * destruct a. simpl in H. destruct g eqn:E.
    + discriminate H.  
    + destruct p. apply IHg in H. discriminate H.
Qed. 

(* game_last always yeilds tail (if any) *)
Lemma game_last_tail :
  forall (g: Game) (r1 r2: bool),
    (game_last (g ++ [(r1, r2)])) = (true, (r1, r2)).
Proof.
  intros.
  induction g.
  * simpl. reflexivity.
  * destruct a. simpl.
    destruct g.
    + simpl. reflexivity.
    + destruct p. simpl. simpl in IHg. apply IHg.
Qed.

(* Always true strategy can yield only true *)
Theorem always_true_yields_only_true :
  forall g : Game,
  game_last (play g st_always_true st_always_true) = (true, (true, true)).
Proof.
  intros.
  unfold play.
  unfold st_always_true.
  apply game_last_tail.
Qed.

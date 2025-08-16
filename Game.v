From Coq Require Import List.
Import ListNotations.
From Coq Require Import String Ascii.

From Coq Require Import ZArith.


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

Definition add_pair '(x1, y1) '(x2, y2) : nat * nat :=
  (x1 + x2, y1 + y2).

Definition game_step_result (b1 b2 : bool) : nat * nat :=
  if b1 then
    if b2 then (3, 3) else (5, 0)
  else
    if b2 then (0, 5) else (1, 1).

Fixpoint game_result (g : Game) : nat * nat :=
  match g with
  | [] => (0, 0)
  | (b1, b2) :: tl =>
    let '(r1, r2) := game_result tl in
    add_pair (game_result tl) (game_step_result b1 b2)
  end.



Definition play (g : Game) (s1 s2 : Strategy) : Game :=
  g ++ [(s1 g, s2 (swap_game g))].

Fixpoint play_many (g : Game) (s1 s2 : Strategy) (n : nat) : Game :=
  match n with
  | 0 => g
  | S n' => play (play_many g s1 s2 n') s1 s2
  end.


(* Strategies *)
Definition st_always_true : Strategy :=
  fun (_ : Game) => true.

Compute (game_to_string (play_many [] st_always_true st_always_true 10)).



(* Proofs *)

(* add_pair: adding (0, 0) doesn't change the pair *)
Lemma add_pair_0_0 :
  forall (p: nat * nat),
  add_pair p (0, 0) = p.
Proof.
  intros.
  destruct p.
  simpl.
  rewrite Nat.add_0_r; rewrite Nat.add_0_r.
  reflexivity.
Qed.

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

(* Play N+1 times is plaing N times and then 1 more *)
Lemma play_many_N_plus_1 :
  forall (g : Game) (s1 s2 : Strategy) (n : nat),
  play_many g s1 s2 (S n) = play (play_many g s1 s2 n) s1 s2.
Proof.
  intros. simpl. reflexivity.
Qed.

(* Game result after play is like before plus the last step *)
Lemma game_result_play :
  forall (g : Game) (s1 s2 : Strategy),
  game_result (play g s1 s2) = add_pair (game_result g) (game_step_result (s1 g) (s2 (swap_game g))).
Proof.
  intros.
  unfold game_result. simpl.



(* Always true against always true gives 3*n *)
Theorem always_true_against_always_true_gives_3_n :
  forall n : nat,
    game_result (play_many [] st_always_true st_always_true n) = (3 * n, 3 * n).
Proof.
  induction n.
  * simpl. reflexivity.
  * rewrite play_many_N_plus_1.
    rewrite game_result_play.
    rewrite IHn.
    simpl.
    apply (f_equal2 (@pair nat nat)).
    + repeat rewrite Nat.add_succ_r.
      repeat rewrite Nat.add_0_r.
      reflexivity.
    + repeat rewrite Nat.add_succ_r.
      repeat rewrite Nat.add_0_r.
      reflexivity.
Qed.
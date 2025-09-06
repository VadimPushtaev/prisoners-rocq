From Coq Require Import List.
Import ListNotations.
From Coq Require Import String Ascii.

From Coq Require Import ZArith.


Definition Game := list (bool * bool).

Definition Strategy := Game -> bool.

Definition swap_game (g : Game) : Game :=
  map (fun '(b1, b2) => (b2, b1)) g.

Definition game_last (g : Game) : bool * (bool * bool) :=
  match g with
  | [] => (false, (false, false))
  | (b1, b2) :: g' => (true, (b1, b2))
  end.

Definition game_to_string (g : Game) : string :=
  let fix rows (g' : Game) : string * string :=
    match g' with
    | [] => (""%string, ""%string)
    | (b1, b2) :: tl =>
        let '(top, bottom) := rows tl in
        (String.append top (if b1 then "1"%string else "0"%string),
         String.append bottom (if b2 then "1"%string else "0"%string))
    end in
  let newline := String (Ascii.ascii_of_nat 10) ""%string in
  let '(top_row, bottom_row) := rows g in
  String.append (String.append newline (String.append top_row (String.append newline bottom_row))) newline.

Definition add_pair '(x1, y1) '(x2, y2) : nat * nat :=
  (x1 + x2, y1 + y2).

Definition game_step_result (b1 b2 : bool) : nat * nat :=
  if b1 then 
    if b2 then (3, 3) else (0, 5)
  else
    if b2 then (5, 0) else (1, 1).

Fixpoint game_result (g : Game) : nat * nat :=
  match g with
  | [] => (0, 0)
  | (b1, b2) :: tl =>
    let '(r1, r2) := game_result tl in
    add_pair (game_result tl) (game_step_result b1 b2)
  end.



Definition play (g : Game) (s1 s2 : Strategy) : Game :=
  (s1 g, s2 (swap_game g)) :: g.

Fixpoint play_many (g : Game) (s1 s2 : Strategy) (n : nat) : Game :=
  match n with
  | 0 => g
  | S n' => play (play_many g s1 s2 n') s1 s2
  end.


(* Strategies *)
Definition st_always_true : Strategy :=
  fun (_ : Game) => true.

Definition st_always_false : Strategy :=
  fun (_ : Game) => false.

Definition st_tit_for_tat : Strategy :=
  fun (g : Game) =>
    match g with
    | [] => true
    | (_, b2) :: _ => b2
    end.

Compute (game_to_string (play (play_many [] st_always_true st_always_true 5) st_always_false st_always_false)).



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

(* swap_game: double swap is the same as no swap *)
Lemma swap_game_double :
  forall (g : Game),
  swap_game (swap_game g) = g.
Proof.
  intros.
  induction g.
  * reflexivity.
  * destruct a. simpl. rewrite IHg. reflexivity.
Qed.

(* swap_game: swap empty does nothing *)
Lemma swap_game_empty :
  forall (g : Game),
  g = [] -> swap_game g = [].
Proof.
  intros.
  rewrite H. reflexivity.
Qed.

(* game_last: first bool is false only for empty game *)
Theorem game_last_false_first :
  forall (g: Game) (r1 r2: bool),
    (game_last g) = (false, (r1, r2)) -> g = [].
Proof.
  intros g r1 r2 H.
  induction g.
  * reflexivity.
  * destruct a. simpl in H.
    injection H. intros. discriminate H2.
Qed. 

(* game_last always yeilds head (if any) *)
Lemma game_last_head :
  forall (g: Game) (r1 r2: bool),
    (game_last ((r1, r2) :: g)) = (true, (r1, r2)).
Proof.
  intros.
  induction g.
  * simpl. reflexivity.
  * destruct a. simpl.
    destruct g.
    + simpl. reflexivity.
    + destruct p. simpl. simpl in IHg. apply IHg.
Qed.

(* Game last is reverted for swapped game *)
Lemma game_last_swapped :
  forall (g: Game) (b1 b2 b3: bool),
    game_last g = (b1, (b2, b3)) <-> game_last (swap_game g) = (b1, (b3, b2)).
Proof.
  split; intro H;
  destruct g as [| p]; simpl in *; try destruct p; simpl in *;
  inversion H; subst; reflexivity.
Qed. 

(* Play N+1 times is plaing N times and then 1 more *)
Lemma play_many_N_plus_1 :
  forall (g : Game) (s1 s2 : Strategy) (n : nat),
  play_many g s1 s2 (S n) = play (play_many g s1 s2 n) s1 s2.
Proof.
  intros. simpl. reflexivity.
Qed.

(* Play only adds head to the game *)
Lemma play_adds_head :
  forall (g : Game) (s1 s2 : Strategy),
  play g s1 s2 = (s1 g, s2 (swap_game g)) :: g.
Proof.
  intros.
  unfold play.
  reflexivity.
Qed.

(* game_result is associative to head *)
Lemma game_result_assoc_head :
  forall (g : Game) (s1 s2 : Strategy) (r1 r2 : bool),
  game_result ((r1, r2) :: g) = add_pair (game_result g) (game_step_result r1 r2).
Proof.
  intros.
  simpl.
  destruct (add_pair (game_result g) (game_step_result r1 r2)).
  destruct (game_result g).
  reflexivity.
Qed.

(* Game result after play is like before plus the last step *)
Lemma game_result_play :
  forall (g : Game) (s1 s2 : Strategy),
  game_result (play g s1 s2) = add_pair (game_result g) (game_step_result (s1 g) (s2 (swap_game g))).
Proof.
  intros.
  rewrite play_adds_head.
  rewrite game_result_assoc_head.
  * reflexivity.
  * auto.
  * auto.
Qed.

Lemma swap_game_head :
  forall (g : Game) (b1 b2 : bool),
  swap_game ((b1, b2) :: g) = (b2, b1) :: swap_game g.
Proof.
  intros.
  unfold swap_game.
  simpl.
  reflexivity.
Qed.

(* swap_game: playing swapped game is the same as playing the original game with swapped strategies *)
Lemma swap_game_again :
  forall (g : Game) (s1 s2 : Strategy),
  play g s1 s2 = swap_game (play (swap_game g) s2 s1).
Proof.
  intros.
  repeat rewrite play_adds_head.
  rewrite swap_game_double.
  rewrite swap_game_head.
  rewrite swap_game_double.
  reflexivity.
Qed.

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
    repeat rewrite Nat.add_succ_r.
    repeat rewrite Nat.add_0_r.
    reflexivity.
Qed.

(* Always false against always false gives n *)
Theorem always_false_against_always_false_gives_n :
  forall n : nat,
    game_result (play_many [] st_always_false st_always_false n) = (n, n).
Proof.
  induction n.
  * simpl. reflexivity.
  * rewrite play_many_N_plus_1.
    rewrite game_result_play.
    rewrite IHn.
    simpl.
    rewrite Nat.add_1_r.
    reflexivity.
Qed.

(* Always true against false gives (0, 5*n) *)
Theorem always_true_against_always_false_gives_0_5_n :
  forall n : nat,
    game_result (play_many [] st_always_true st_always_false n) = (0, 5 * n).
Proof.
  induction n.
  * simpl. reflexivity.
  * rewrite play_many_N_plus_1.
    rewrite game_result_play.
    rewrite IHn.
    simpl.
    repeat rewrite Nat.add_succ_r.
    rewrite Nat.add_0_r.
    reflexivity.
Qed.

(* Always false against always true gives (5*n, 0) *)
Theorem always_false_against_always_true_gives_5_n_0 :
  forall n : nat,
    game_result (play_many [] st_always_false st_always_true n) = (5 * n, 0).
Proof.
  induction n.
  * simpl. reflexivity.
  * rewrite play_many_N_plus_1.
    rewrite game_result_play.
    rewrite IHn.
    simpl.
    repeat rewrite Nat.add_succ_r.
    rewrite Nat.add_0_r.
    reflexivity.
Qed.

(* Tit for tat returns true when head is true or none *)
Theorem tit_for_tat_head_true :
  forall (g: Game),
  g = [] \/ game_last g = (true, (true, true)) \/ game_last g = (true, (false, true)) ->
  st_tit_for_tat g = true.
Proof.
  intros.
  * destruct H.
    + rewrite H. auto.
    + unfold st_tit_for_tat.
       destruct g. reflexivity.
      destruct p.
      rewrite game_last_head in H.
      destruct H.
      inversion H. reflexivity.
      inversion H. reflexivity.
Qed.

Lemma tit_for_tat_gives_true_if_given_true :
  forall (g: Game) (b: bool) (s: Strategy),
  game_last g = (true, (b, true)) ->
  play g st_tit_for_tat s = (true, true) :: g \/ play g st_tit_for_tat s = (true, false) :: g.
Proof.
  intros.
  unfold play.
  destruct g.
  + discriminate H.
  + destruct p. rewrite game_last_head in H.
    inversion H.
    simpl.
    destruct (s ((true, b) :: swap_game g)).
    * left. reflexivity.
    * right. reflexivity.
Qed.

Lemma tit_for_tat_gives_true_true_if_last_true_true :
  forall (g: Game),
  game_last g = (true, (true, true)) ->
  play g st_tit_for_tat st_tit_for_tat = (true, true) :: g.
Proof.
  intros.
  unfold play.
  replace (st_tit_for_tat g) with (true).
  * replace (st_tit_for_tat (swap_game g)) with (true).
    + reflexivity.
    + symmetry. apply tit_for_tat_head_true.
      rewrite game_last_swapped in H.
      right. left. apply H.
  * symmetry. apply tit_for_tat_head_true.
    right. left. apply H.
Qed.

(* Tit for tat against itself always yiels (true, true) *)
Theorem tit_for_tat_against_itself_always_true :
  forall n : nat,
  game_last (play_many [] st_tit_for_tat st_tit_for_tat n) = (true, (true, true)) \/
  n = 0 (* n=0 *).
Proof.
  intros.
  induction n.
  * right. reflexivity.
  * left.
    destruct IHn.
    + rewrite play_many_N_plus_1.
      apply tit_for_tat_gives_true_true_if_last_true_true in H.
      rewrite H.
      simpl.
      reflexivity. 
    + rewrite H. simpl. reflexivity.
Qed.

(* Tit for tat against always true always yields (true, true) *)
Theorem tit_for_tat_against_always_true_always_true :
  forall n : nat,
  game_last (play_many [] st_tit_for_tat st_always_true n) = (true, (true, true)) \/
  n = 0 (* n=0 *).
Proof.
  intros.
  induction n.
  * right. reflexivity.
  * left.
    destruct IHn.
    + rewrite play_many_N_plus_1.
      apply (tit_for_tat_gives_true_if_given_true _ _ st_always_true) in H.
      destruct H.
      +++ rewrite H. auto.
      +++ apply (f_equal game_last) in H.
          simpl in H.
          destruct (st_tit_for_tat (play_many [] st_tit_for_tat st_always_true n)).
          *** replace (st_always_true (swap_game (play_many [] st_tit_for_tat st_always_true n))) with true in H.
              discriminate H.
              unfold st_always_true. reflexivity.
          *** replace (st_always_true (swap_game (play_many [] st_tit_for_tat st_always_true n))) with true in H.
              discriminate H.
              unfold st_always_true. reflexivity.
    + rewrite H. simpl. unfold st_always_true. reflexivity.
Qed.

(* Tit for tat against tit for tat gives 3*n *)
Theorem tit_for_tat_against_tit_for_tat_gives_3_n :
  forall n : nat,
    game_result (play_many [] st_tit_for_tat st_tit_for_tat n) = (3 * n, 3 * n). 
Proof.
  induction n.
  * simpl. reflexivity.
  * rewrite play_many_N_plus_1.
    rewrite game_result_play.
    rewrite IHn.
    replace (st_tit_for_tat (play_many [] st_tit_for_tat st_tit_for_tat n)) with (true).
    replace (st_tit_for_tat (swap_game (play_many [] st_tit_for_tat st_tit_for_tat n))) with (true).
    simpl.
    repeat rewrite Nat.add_succ_r.
    repeat rewrite Nat.add_0_r.
    reflexivity.
    + symmetry. apply tit_for_tat_head_true.
      destruct (tit_for_tat_against_itself_always_true n).
      +++ apply game_last_swapped in H. rewrite H. auto.
      +++ rewrite H. auto.
    + symmetry. apply tit_for_tat_head_true.
      destruct (tit_for_tat_against_itself_always_true n).
      +++ rewrite H. auto.
      +++ rewrite H. auto.
Qed.

(* Tit for tat against always true gives 3*n *)
Theorem tit_for_tat_against_always_true_gives_3_n :
  forall n : nat,
    game_result (play_many [] st_tit_for_tat st_always_true n) = (3 * n, 3 * n).
Proof.
  induction n.
  * simpl. reflexivity.
  * simpl.
    rewrite IHn.
    replace (st_tit_for_tat (play_many [] st_tit_for_tat st_always_true  n)) with (true).
    replace (st_always_true (swap_game (play_many [] st_tit_for_tat st_always_true  n))) with (true).
    simpl.
    repeat rewrite Nat.add_succ_r.
    repeat rewrite Nat.add_0_r.
    reflexivity.
    + unfold st_always_true.
      reflexivity.
    + symmetry. apply tit_for_tat_head_true.
      destruct (tit_for_tat_against_always_true_always_true n); rewrite H; auto.
Qed.

(* Tit for tat against always false gives (n-1, 5 + n-1) *)
Theorem tit_for_tat_against_always_false_gives :
  forall n : nat,
    game_result (play_many [] st_tit_for_tat st_always_false (S n)) = (n, n + 5).
Proof.
  induction n.
  * simpl. reflexivity.
  * remember (S n) as k eqn:Heqk.  (* make opaque for simpl *)
    simpl.
    rewrite Heqk in *.
    rewrite IHn.
    simpl.
    repeat rewrite Nat.add_1_r.
    reflexivity.
Qed.

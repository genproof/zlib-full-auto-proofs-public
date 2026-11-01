(* The headless inflate_fast specification against Spec5's, and the contexts of inflate()'s body
   (RTH8Defs.rth8_delta_stmt). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.roundtrip.RTHSpec.
Require Import Zlib.proof.roundtrip.RTH8Spec.
Require Import Zlib.proof.roundtrip.RTH8Defs.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* ---------------------------------------------------------------------------------------------- *)
(* inflate_fast's model keeps the header: the gz_header model m_h and the flag i_head                *)

Lemma rth8_fwalk_h fx dx k il t here m h' m' :
  fwalk_f fx dx k il t here m = (h', m') -> m_h m' = m_h m /\ i_head (m_s m') = i_head (m_s m).
Proof.
  revert here m; induction k; intros here m E; cbn [fwalk_f] in E.
  - inversion E; subst; cbn; auto.
  - destruct (il (e_op here)).
    + apply IHk in E; destruct E as [-> ->]; cbn; auto.
    + inversion E; subst; cbn; auto.
Qed.

Ltac rth8_dest x :=
  lazymatch x with
  | match ?c with _ => _ end => rth8_dest c
  | context [match ?c with _ => _ end] => rth8_dest c
  | _ => tryif is_var x then destruct x else (let E := fresh "E" in destruct x eqn:E)
  end.

Lemma rth8_fast_iter_h fx dx m :
  m_h (snd (fast_iter fx dx m)) = m_h m /\ i_head (m_s (snd (fast_iter fx dx m))) = i_head (m_s m).
Proof.
  unfold fast_iter.
  repeat (cbv beta iota zeta;
          match goal with |- context [match ?x with _ => _ end] => rth8_dest x end).
  all: repeat match goal with
         | E: fwalk_f _ _ _ _ _ _ _ = (_, _) |- _ => apply rth8_fwalk_h in E; destruct E as [? ?]
         end.
  all: cbn -[fwalk_f copy_bytes]; repeat match goal with
         | H: m_h ?a = _ |- context [m_h ?a] => rewrite H
         | H: i_head ?a = _ |- context [i_head ?a] => rewrite H
         end; auto.
Qed.

Lemma rth8_fast_loop_h fx dx k m :
  m_h (fast_loop fx dx k m) = m_h m /\ i_head (m_s (fast_loop fx dx k m)) = i_head (m_s m).
Proof.
  revert m; induction k; intros m; cbn [fast_loop]; [auto|].
  destruct (rth8_fast_iter_h fx dx m) as [A B].
  destruct (fast_iter fx dx m) as [go m1] eqn:E; cbn in A, B |- *.
  destruct ((_ && _)%bool); [destruct (IHk m1) as [-> ->]|]; auto.
Qed.

Lemma rth8_fast_h fx dx m : m_h (fast fx dx m) = m_h m /\ i_head (m_s (fast fx dx m)) = i_head (m_s m).
Proof. unfold fast. cbn. apply rth8_fast_loop_h. Qed.

(* Loop.head_part depends only on m_h and i_head, which inflate_fast keeps *)
Lemma rth8_head_part_fast F m : head_part F (fast lenfix_list distfix_list m) = head_part F m.
Proof. unfold head_part. destruct (rth8_fast_h lenfix_list distfix_list m) as [-> ->]. reflexivity. Qed.

(* the loop state with the header is the headless one and Loop.head_part *)
Lemma rth8_mem_rep_hl F m : mem_rep F m = mem_rep_hl F m * head_part F m.
Proof.
  unfold mem_rep, mem_rep_hl, head_part_hl, RTHLoop.hnoneH.
  destruct (i_head (m_s m)); apply pred_ext; cancel.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the specification and the contexts                                                             *)

Lemma rth8_fast_sub : funspec_sub (snd inflate_fast_spec3_hl) (snd inflate_fast_spec3).
Proof.
  do_funspec_sub. destruct w as [F m]. Exists (F, m) (head_part F m). simpl. Intros.
  rewrite rth8_mem_rep_hl.
  apply andp_right; [apply prop_right | cancel].
  split; [ | tauto ].
  intros rho. Intros. rewrite rth8_mem_rep_hl, rth8_head_part_fast. cancel.
Qed.

(* a function context whose functions have stronger specifications (pointwise, same names) is a larger
   type context *)
Lemma rth8_tsub (G1 G2 : funspecs) V f :
  Forall2 (fun a b => fst a = fst b /\ funspec_sub (snd b) (snd a)) G1 G2 ->
  tycontext_sub (func_tycontext f V G1 nil) (func_tycontext f V G2 nil).
Proof.
  intros H. apply tycontext_sub_i99. split.
  - assert (E : make_tycontext_g V G1 = make_tycontext_g V G2).
    { unfold make_tycontext_g. induction H as [ | a b G1 G2 [Ei Es] H IH]; [reflexivity | ].
      simpl. rewrite IH, Ei. f_equal.
      destruct a as [ia fa], b as [ib fb]; simpl in *. destruct fa, fb; simpl in Es.
      destruct Es as [[-> ->] _]. reflexivity. }
    intros id. rewrite E. destruct (Maps.PTree.get id (make_tycontext_g V G2)); simpl; auto.
  - intros id. rewrite !semax_prog.find_id_maketycontext_s.
    induction H as [ | a b G1 G2 [Ei Es] H IH]; [exact I | ].
    destruct a as [ia fa], b as [ib fb]; simpl in *. subst ib.
    if_tac; [ | exact IH].
    exists fb. split; [reflexivity | ]. apply funspec_sub_sub_si; exact Es.
Qed.

Lemma rth8_sub_inflate5 : tycontext_sub Delta_inflate5 Delta_inflate5_hl.
Proof.
  unfold Delta_inflate5, Delta_inflate5_hl. apply rth8_tsub.
  unfold Gprog_inflate3, Gprog_inflate3_hl. apply Forall2_app; unfold Gprog_cases3, Gprog_cases3_hl.
  do 2 (apply Forall2_cons; [split; [reflexivity | apply funspec_sub_refl] | ]).
  (* the names are compared after reducing fst: plain conversion would compare the two funspecs *)
  apply Forall2_cons; [split; [change (_inflate_fast = _inflate_fast); reflexivity | exact rth8_fast_sub] | ].
  do 3 (apply Forall2_cons; [split; [reflexivity | apply funspec_sub_refl] | ]).
  1-2: repeat (apply Forall2_cons; [split; [reflexivity | apply funspec_sub_refl] | ]); apply Forall2_nil.
Qed.

Lemma rth8_delta : rth8_delta_stmt.
Proof.
  split; [exact rth8_fast_sub | ].
  split; [eapply tycontext_sub_trans; [apply sub_cases_inflate5 | apply rth8_sub_inflate5] | ].
  split; [exact rth8_sub_inflate5 | ].
  unfold Gprog_inflate8, Gprog_inflate3, Gprog_inflate3_hl, Gprog_cases3, Gprog_cases3_hl.
  cbn [map app].
  (* element by element; the name tests are decided by lazy reduction, which never unfolds the funspecs *)
  repeat (apply (f_equal2 (@cons (ident * funspec))); [ | ]); [ | | | | | | | | reflexivity].
  all: match goal with |- context [ident_eq ?a ?b] => destruct (ident_eq a b) as [E|E] end.
  all: first [ exfalso; lazy in E; discriminate
             | exfalso; apply E; lazy; reflexivity
             | reflexivity ].
Qed.

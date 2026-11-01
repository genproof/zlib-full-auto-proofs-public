(** * SendKit2: fixes of SendKit's tactics

    [sfwd] now gives the ranges of loaded tree entries ([sk_tree_range]: [0 <= Znth i (dl t) < 65536] from
    [tree_ok t n]) and fails over to the next goal only when the side conditions are SOLVED (with SendKit's
    [sfwd], an unsolved tc_val side condition of a tree load stayed first and the next tactic ran on it:
    "simplify_Delta did not put Delta_specs and Delta into canonical form").  [sb_block] asserts
    [0 <= l <= 65535] after the length statement (so a loaded length's range is available).
    Use: [Require Import Zlib.proof.trees.SendKit2.] (re-exports SendKit; the tactics here shadow SendKit's). *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Arith.
Require Import Zlib.proof.trees.TSpec.
Require Export Zlib.proof.trees.SendKit.
Require Import Zlib.trees.code.

#[export] Existing Instance DCS.CS.

Open Scope cmodel_scope.

(** The constants of trees.c (Model.v). *)
Ltac sk_consts :=
  unfold LENGTH_CODES, LITERALS, L_CODES, D_CODES, BL_CODES, HEAP_SIZE, MAX_BITS, END_BLOCK in *.

(** [0 <= i < Zlength (fc t)] from a [tree_ok t n] hypothesis. *)
Ltac sk_idx :=
  lazymatch goal with
  | |- 0 <= ?i < Zlength (fc ?t) =>
    lazymatch goal with
    | Ht : tree_ok t ?n |- _ =>
      let E1 := fresh "E" in let E2 := fresh "E" in
      pose proof Ht as (E1 & E2 & _); rewrite E1; clear E1 E2; sk_consts; lia
    end
  end.

Lemma sk_tree_rng_dl t n i : tree_ok t n -> 0 <= i < n -> 0 <= Znth i (dl t) < 65536.
Proof. intros (_ & _ & H) Hi. apply H; auto. Qed.
Lemma sk_tree_rng_fc t n i : tree_ok t n -> 0 <= i < n -> 0 <= Znth i (fc t) < 65536.
Proof. intros (_ & _ & H) Hi. apply H; auto. Qed.

(** The ranges of the tree entries [Znth i (dl t)], [Znth i (fc t)] of the goal, as hypotheses. *)
Ltac sk_tree_range :=
  repeat match goal with
  | |- context [Znth ?i (dl ?t)] =>
      lazymatch goal with
      | _ : 0 <= Znth i (dl t) < 65536 |- _ => fail
      | Ht : tree_ok t ?n |- _ => assert (0 <= Znth i (dl t) < 65536) by (apply (sk_tree_rng_dl t n i Ht); sk_consts; lia)
      end
  | |- context [Znth ?i (fc ?t)] =>
      lazymatch goal with
      | _ : 0 <= Znth i (fc t) < 65536 |- _ => fail
      | Ht : tree_ok t ?n |- _ => assert (0 <= Znth i (fc t) < 65536) by (apply (sk_tree_rng_fc t n i Ht); sk_consts; lia)
      end
  end.

(** A load [tree[i].Len] / [tree[i].Code] from [tree_codes] leaves [Znth i (ct_arr ftrue ftrue t)] under the
    union projections: rewrite it to [Vint (Int.repr (Znth i (dl t)))] / [... (fc t)], with the ranges. *)
Ltac sk_norm_tree :=
  lazymatch goal with
  | |- context [Znth _ (ct_arr ftrue ftrue _)] =>
      repeat (rewrite Znth_tree_codes by sk_idx); cbv beta iota; sk_tree_range
  end.

(** Side conditions of forward: tc_val of ush/uch loads, typechecks of stores (shift amounts, overflows),
    array indices. *)
Ltac sb_side :=
  lazymatch goal with
  | |- _ |-- local _ => first [tc_side | entailer!]
  | |- _ |-- denote_tc_assert _ => entailer!; try (change (Int.unsigned Int.iwordsize) with 32; lia)
  | |- _ |-- !! _ => entailer!; try (sk_consts; lia)
  end.
Ltac sfwd := forward; try (idtac; sk_norm_tree); try (solve [sb_side]).

(** The SEP list without the six items of an opened [out_at]. *)
Ltac sb_rm_out R :=
  lazymatch R with
  | nil => constr:(@nil mpred)
  | @field_at _ _ _ (DOT _pending) _ _ :: ?R' => sb_rm_out R'
  | @field_at _ _ _ (DOT _pending_buf) _ _ :: ?R' => sb_rm_out R'
  | @field_at _ _ _ (DOT _bi_buf) _ _ :: ?R' => sb_rm_out R'
  | @field_at _ _ _ (DOT _bi_valid) _ _ :: ?R' => sb_rm_out R'
  | @field_at _ _ _ (DOT _bi_used) _ _ :: ?R' => sb_rm_out R'
  | @data_at _ _ (tarray tuchar (Zlength _)) (pb_vals _ _) _ :: ?R' => sb_rm_out R'
  | ?x :: ?R' => let r := sb_rm_out R' in constr:(x :: r)
  end.

(** The branch condition of forward_if as a comparison of numbers. *)
Ltac sb_cond :=
  repeat match goal with H : context [Int.sub (Int.repr _) (Int.repr _)] |- _ => rewrite sub_repr32 in H end;
  repeat match goal with H : context [Int.signed (Int.repr ?x)] |- _ => rewrite (Int.signed_repr x) in H by rep_lia end.

(** forward_if, joining both branches at [out_at o1 m1] in place of the opened fields. *)
Ltac sb_forward_if o1 m1 :=
  lazymatch goal with
  | |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    let R' := sb_rm_out R in
    lazymatch R with
    | context [@field_at _ _ _ (DOT _pending_buf) ?pbp ?sp] =>
      forward_if (PROPx P (LOCALx Q (SEPx (out_at o1 m1 sp pbp :: R'))))
    end
  end.

(** Forward until the store [s->bi_buf = ... | (ush)VALUE << ...] has been made. *)
Ltac sb_to_or normv :=
  repeat (lazymatch goal with
          | |- semax _ (PROPx _ (LOCALx _ (SEPx ?R))) _ _ =>
              lazymatch R with
              | context [Int.or (Int.repr _) (Int.shl _ _)] => fail
              | _ => sfwd; normv; try (solve [sb_side])
              end
          end).

Ltac sb_rw_or Hsb valtac :=
  lazymatch goal with
  | |- context [Int.zero_ext 16 (Int.or (Int.repr ?bb) (Int.shl (Int.zero_ext 16 ?iv) (Int.repr ?bv)))] =>
    lazymatch type of Hsb with
    | c_send_bits (mkOut ?buf ?p bb bv ?bu, ?m) ?v _ = Some _ =>
    lazymatch goal with
    | Hok : out_ok (mkOut buf p bb bv bu) m |- _ =>
      let Hval := fresh "Hval" in
      assert (Hval : Int.zero_ext 16 iv = Int.repr (u16 v)) by valtac;
      rewrite (sb_or_eq bb bv iv v (out_ok_bb _ _ _ _ _ _ Hok) ltac:(lia) Hval)
    end end
  end.

Ltac sb_then Hsb normv valtac :=
  lazymatch type of Hsb with
  | c_send_bits (mkOut ?buf ?p ?bb ?bv ?bu, ?m) ?v ?l = Some (?o1, ?m1) =>
  lazymatch goal with
  | Hok : out_ok (mkOut buf p bb bv bu) m |- _ =>
    let Hbv' := fresh "Hbv" in let Hp0 := fresh "Hp0" in let Hp1 := fresh "Hp1" in let Hr := fresh "Hr" in
    pose proof (c_send_bits_then _ _ _ _ _ _ _ _ _ Hsb ltac:(lia)) as (Hbv' & Hp0 & Hp1 & Hr);
    injection Hr as -> ->;
    sb_to_or normv;
    sb_rw_or Hsb valtac;
    let Hval := match goal with H : Int.zero_ext 16 _ = Int.repr (u16 v) |- _ => H end in
    let Hok1 := fresh "Hok1" in let Hi0 := fresh "Hi0" in
    pose proof (sb_bb1_range bb bv v);
    assert (Hok1 : out_ok (mkOut buf p (sb_bb1 bb bv v) bv bu) m)
      by (eapply out_ok_set_bits; [exact Hok | lia | lia | exact (out_ok_bu _ _ _ _ _ _ Hok)]);
    assert (Hi0 : 0 <= p < Zlength buf) by lia;
    fwd; fwd; fwd; fwd; fwd;
    fold_put_byte; open_out_at;
    let Hi1 := fresh "Hi1" in
    assert (Hi1 : 0 <= p + 1 < Zlength (upd_Znth p buf (u8 (Z.land (sb_bb1 bb bv v) 255))))
      by (rewrite Zlength_upd_Znth; lia);
    fwd; fwd; fwd; fwd; fwd;
    fold_put_byte; open_out_at;
    sfwd; sfwd;
    rewrite (sb_shr_eq bv _ v Hbv' Hval);
    sfwd; forward; try (solve [sb_side]);
    lazymatch goal with |- context [@field_at _ _ _ (DOT _pending_buf) ?pbp ?sp] =>
      sep_apply (sb_then_close buf p bb bv bu m v l sp pbp Hok Hp0 Hp1 Hbv' ltac:(lia) ltac:(rep_lia)) end;
    entailer!
  end end.

Ltac sb_else Hsb normv valtac :=
  lazymatch type of Hsb with
  | c_send_bits (mkOut ?buf ?p ?bb ?bv ?bu, ?m) ?v ?l = Some (?o1, ?m1) =>
  lazymatch goal with
  | Hok : out_ok (mkOut buf p bb bv bu) m |- _ =>
    let Hbv' := fresh "Hbv" in let Hr := fresh "Hr" in
    pose proof (c_send_bits_else _ _ _ _ _ _ _ _ _ Hsb ltac:(lia)) as (Hbv' & Hr);
    injection Hr as -> ->;
    sb_to_or normv;
    sb_rw_or Hsb valtac;
    sfwd; forward; try (solve [sb_side]);
    lazymatch goal with |- context [@field_at _ _ _ (DOT _pending_buf) ?pbp ?sp] =>
      sep_apply (sb_else_close buf p bb bv bu m v l sp pbp Hok Hbv' ltac:(lia) ltac:(rep_lia)) end;
    entailer!
  end end.

Ltac sb_block Hsb normv valtac :=
  lazymatch type of Hsb with
  | c_send_bits (?o, ?m) ?v ?l = Some ?r =>
    lazymatch o with mkOut _ _ _ _ _ => idtac | _ => is_var o; destruct o as [?buf ?p ?bb ?bv ?bu] end;
    is_var r;
    let o1 := fresh "o" in let m1 := fresh "m" in destruct r as [o1 m1];
    sfwd; normv; try (solve [sb_side]);
    assert (0 <= l <= 65535) by rep_lia;
    open_out_at;
    lazymatch type of Hsb with c_send_bits (mkOut ?buf ?p ?bb ?bv ?bu, ?m) _ _ = Some _ =>
    lazymatch goal with Hok : out_ok (mkOut buf p bb bv bu) m |- _ =>
      pose proof (out_ok_bv _ _ _ _ _ _ Hok); pose proof (out_ok_bb _ _ _ _ _ _ Hok) end end;
    sfwd;
    sb_forward_if o1 m1;
    [ sb_cond; sb_then Hsb normv valtac | sb_cond; sb_else Hsb normv valtac | idtac .. ]
  end.

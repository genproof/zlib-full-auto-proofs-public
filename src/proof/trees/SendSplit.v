(** * SendKit2's sb_block / sb_then cut into sentences of < 30 s each

    One [sb_block] sentence takes ~2 min on this machine (the per-sentence budget is fixed).  Use:

      sb_pre Hsb normv.
      { sb_cond. sbt1 Hsb normv valtac. sbt2 Hsb. sbt3 Hsb. sbt4 Hsb. }
      { sb_cond. sb_else Hsb normv valtac. }
      (continuation: SEP has out_at o m sp pbp, Hsb : c_send_bits .. = Some (o, m))

    Measured: sb_pre 9 s, sbt1 18 s, sbt2 14 s, sbt3 14 s, sbt4 22 s, sb_else 25 s. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Arith.
Require Import Zlib.proof.trees.TSpec.
Require Export Zlib.proof.trees.SendKit2.
Require Import Zlib.trees.code.

#[export] Existing Instance DCS.CS.

Open Scope cmodel_scope.

(** [SendKit2.sb_block] cut in sentences (one [sb_block] sentence takes ~2 min on this machine): the length
    statement and the [forward_if]; then [sb_cond; sb_then Hsb normv valtac] and [sb_cond; sb_else Hsb normv
    valtac] on the two branches. *)
Ltac sb_pre Hsb normv :=
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
    sb_forward_if o1 m1
  end.

(** [SendKit2.sb_then] cut in four sentences: [sbt1 Hsb normv valtac. sbt2 Hsb. sbt3 Hsb. sbt4 Hsb.] *)
Ltac sbt1 Hsb normv valtac :=
  lazymatch type of Hsb with
  | c_send_bits (mkOut ?buf ?p ?bb ?bv ?bu, ?m) ?v ?l = Some (?o1, ?m1) =>
  lazymatch goal with
  | Hok : out_ok (mkOut buf p bb bv bu) m |- _ =>
    pose proof (c_send_bits_then _ _ _ _ _ _ _ _ _ Hsb ltac:(lia)) as (Hbv_ & Hp0_ & Hp1_ & Hr_);
    injection Hr_ as -> ->;
    sb_to_or normv;
    sb_rw_or Hsb valtac
  end end.

Ltac sbt2 Hsb :=
  lazymatch type of Hsb with
  | c_send_bits (mkOut ?buf ?p ?bb ?bv ?bu, ?m) ?v ?l = Some _ =>
  lazymatch goal with
  | Hok : out_ok (mkOut buf p bb bv bu) m |- _ =>
    pose proof (sb_bb1_range bb bv v);
    assert (Hok1_ : out_ok (mkOut buf p (sb_bb1 bb bv v) bv bu) m)
      by (eapply out_ok_set_bits; [exact Hok | lia | lia | exact (out_ok_bu _ _ _ _ _ _ Hok)]);
    assert (Hi0_ : 0 <= p < Zlength buf) by lia;
    fwd; fwd; fwd; fwd; fwd;
    fold_put_byte; open_out_at
  end end.

Ltac sbt3 Hsb :=
  lazymatch type of Hsb with
  | c_send_bits (mkOut ?buf ?p ?bb ?bv ?bu, ?m) ?v ?l = Some _ =>
    assert (Hi1_ : 0 <= p + 1 < Zlength (upd_Znth p buf (u8 (Z.land (sb_bb1 bb bv v) 255))))
      by (rewrite Zlength_upd_Znth; lia);
    fwd; fwd; fwd; fwd; fwd;
    fold_put_byte; open_out_at
  end.

Ltac sbt4 Hsb :=
  lazymatch type of Hsb with
  | c_send_bits (mkOut ?buf ?p ?bb ?bv ?bu, ?m) ?v ?l = Some _ =>
  lazymatch goal with
  | Hok : out_ok (mkOut buf p bb bv bu) m |- _ =>
    let Hval := match goal with H : Int.zero_ext 16 _ = Int.repr (u16 v) |- _ => H end in
    sfwd; sfwd;
    rewrite (sb_shr_eq bv _ v ltac:(lia) Hval);
    sfwd; forward; try (solve [sb_side]);
    lazymatch goal with |- context [@field_at _ _ _ (DOT _pending_buf) ?pbp ?sp] =>
      sep_apply (sb_then_close buf p bb bv bu m v l sp pbp Hok ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rep_lia)) end;
    entailer!
  end end.


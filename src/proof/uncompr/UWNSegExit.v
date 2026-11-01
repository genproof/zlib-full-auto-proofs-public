(* uncompress2_z with a Z_NULL source of length 0 (UWNSegs.v), statements 15-: after the loop, len += avail_in (0),
   left += avail_out, *sourceLen -= len (it stays 0), *destLen -= left, inflateEnd, and the return value
   UModel.unc_ret.  The script is UWSegExit.v's. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Uncompr.
Require Zlib.units.Inflate.
Require Import Zlib.uncompr.code.
Require Import Zlib.proof.uncompr.UWNSegs.
Require Import Zlib.proof.uncompr.UWSegExit.
Require Import Zlib.proof.inflate_api.Spec5.
Require Import Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Uncompr.CS.
Local Open Scope logic.

(* the last test of the return value, `err == Z_BUF_ERROR && len == 0`, with len = 0 *)
Ltac un_ret_tac :=
  simpl in *; unfold unc_ret, Z_STREAM_END, Z_NEED_DICT, Z_BUF_ERROR, Z_DATA_ERROR in *;
  repeat match goal with Hx: ?e <> ?k |- context [?e =? ?k] => rewrite (proj2 (Z.eqb_neq e k) Hx) end;
  match goal with |- context [?e =? -5] => destruct (e =? -5) end;
  simpl in *; try reflexivity; try discriminate.

Lemma un_exit : un_exit_stmt.
Proof.
  intros Espec A v F Pv.
  destruct A as [gv dnull dsh dp dn dc cap dlp dtok slp gsh tsh].
  unfold un_brk, un_lcl, un_sep, un_fr, un_facts, un_sfacts, uw_seg15, POST_un in *.
  destruct F as (Hd & Hgsh & Htsh).
  abbreviate_semax.
  Intros err m out z L ao.
  unfold istream. Intros. unfold zstrm_at, strm_rep.
  remember (gv inflate.code._zcalloc) as zca. remember (gv inflate.code._zcfree) as zcf.
  change_compspecs Zlib.units.Uncompr.CS.
  forward. forward. forward. forward. forward. forward. forward. forward.
  match goal with Hx: zf_ok z, Hy: live_ok L |- _ =>
    sep_apply (istream_fold gv v z L zca zcf Heqzca Heqzcf Hx Hy) end.
  clear dependent zca. clear dependent zcf.
  forward_call (gv, Tsh, v, z, Some L).
  { rewrite istream_opt_ptr by auto. cancel. }
  rewrite istream_opt_ptr by auto.
  match goal with Hx: zf_ai z = 0 |- _ => rewrite Hx end.
  match goal with Hx: zf_ao z = ao |- _ => rewrite Hx end.
  match goal with Hx: 0 <= ao <= uw_max |- _ => unfold uw_max in Hx end.
  rewrite !Int.unsigned_repr by rep_lia. rewrite !add64_repr, !sub64_repr.
  replace (cap - Zlength out - ao + ao) with (cap - Zlength out) by lia.
  replace (cap - (cap - Zlength out)) with (Zlength out) by lia.
  change (0 + 0) with 0. change (0 - 0) with 0.
  forward_if (temp _t'9 (Vint (Int.repr (unc_ret err 0)))).
  { forward. entailer!. }
  { forward_if (temp _t'9 (Vint (Int.repr (unc_ret err 0)))).
    { forward. forward. entailer!. }
    { forward_if (temp _t'10 (Val.of_bool ((err =? -5) && (0 =? 0)))).
      { forward. entailer!.
        match goal with Hx: Int.repr err = Int.repr _ |- _ => apply repr_inj_signed in Hx; [| rep_lia | rep_lia] end.
        subst err. reflexivity. }
      { forward. entailer!.
        assert (Hn5: err <> -5) by (intro; subst; contradiction).
        rewrite (proj2 (Z.eqb_neq _ _) Hn5). reflexivity. }
      forward_if (temp _t'9 (Vint (Int.repr (unc_ret err 0)))).
      { forward. forward. forward. entailer!. un_ret_tac. }
      { forward. forward. forward. entailer!. un_ret_tac. }
      all: try entailer!. }
    all: try entailer!. }
  unfold istream, zstrm_at, strm_rep. Intros. change_compspecs Zlib.units.Uncompr.CS.
  forget (gv inflate.code._zcalloc) as zca. forget (gv inflate.code._zcfree) as zcf.
  forward.
  Exists (unc_ret err 0) 0 (Zlength out) out.
  apply andp_right; [apply prop_right; split; [right; exists err; auto | reflexivity] |].
  unfold uversion_lit, inflate_globals, uw_lit.
  sep_apply (data_at_data_at_ Tsh t_strm). cancel.
Qed.

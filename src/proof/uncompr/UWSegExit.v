(* uncompress2_z for any sizes (UWSegs.v), statements 15-: after the loop, len += avail_in, left += avail_out,
   *sourceLen -= len, *destLen -= left, inflateEnd, and the return value UModel.unc_ret. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Uncompr Zlib.units.Inflate.
Require Import Zlib.uncompr.code.
Require Import Zlib.proof.uncompr.UWSegs.
Require Import Zlib.proof.inflate_api.Spec5.
Require Import Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Uncompr.CS.
Local Open Scope logic.

(* the counters' additions `len += stream.avail_in`, `left += stream.avail_out` on unsigned long *)
Lemma add64_repr: forall a b, Int64.add (Int64.repr a) (Int64.repr b) = Int64.repr (a + b).
Proof.
  intros. unfold Int64.add. apply Int64.eqm_samerepr. apply Int64.eqm_add; apply Int64.eqm_sym; apply Int64.eqm_unsigned_repr.
Qed.

Lemma uw_exit : uw_exit_stmt.
Proof.
  intros Espec A v F Pv.
  destruct A as [gv dnull dsh dp dn dc cap dlp dtok stok ssh sp sn sc src slp gsh tsh].
  unfold uw_brk, uw_lcl, uw_sep, uw_fr, uw_facts, uw_sfacts, uw_seg15, POST_uw in *.
  destruct F as (Hd & Hssh & Hsp & Hsn & Hsl & Hsc & Hsnmax & Hsub & Hbytes & Hgsh & Htsh).
  abbreviate_semax.
  Intros err m used out z L ai ao.
  unfold istream. Intros. unfold zstrm_at, strm_rep.
  remember (gv inflate.code._zcalloc) as zca. remember (gv inflate.code._zcfree) as zcf.
  change_compspecs Zlib.units.Uncompr.CS.
  forward. forward. forward. forward. forward. forward. forward. forward.
  sep_apply (istream_fold gv v z L zca zcf Heqzca Heqzcf H20 H22).
  clear dependent zca. clear dependent zcf.
  forward_call (gv, Tsh, v, z, Some L).
  { rewrite istream_opt_ptr by auto. cancel. }
  rewrite istream_opt_ptr by auto.
  rewrite H18, H19.
  unfold uw_max in H13, H14.
  rewrite !Int.unsigned_repr by rep_lia. rewrite !add64_repr, !sub64_repr.
  replace (cap - Zlength out - ao + ao) with (cap - Zlength out) by lia.
  replace (Zlength src - used - ai + ai) with (Zlength src - used) by lia.
  replace (cap - (cap - Zlength out)) with (Zlength out) by lia.
  replace (Zlength src - (Zlength src - used)) with used by lia.
  forward_if (temp _t'9 (Vint (Int.repr (unc_ret err (Zlength src - used))))).
  { forward. entailer!. }
  { forward_if (temp _t'9 (Vint (Int.repr (unc_ret err (Zlength src - used))))).
    { forward. forward. entailer!. }
    { forward_if (temp _t'10 (Val.of_bool ((err =? -5) && (Zlength src - used =? 0)))).
      { forward. entailer!.
        match goal with Hx: Int.repr err = Int.repr _ |- _ => apply repr_inj_signed in Hx; [| rep_lia | rep_lia] end.
        subst err. simpl andb. unfold Int64.cmpu.
        destruct (Zlength src - used =? 0) eqn:E.
        - apply Z.eqb_eq in E. rewrite E. reflexivity.
        - apply Z.eqb_neq in E. rewrite Int64.eq_false; [reflexivity |].
          intro Hx. apply repr_inj_unsigned64 in Hx; rep_lia. }
      { forward. entailer!.
        assert (Hn5: err <> -5) by (intro; subst; contradiction).
        rewrite (proj2 (Z.eqb_neq _ _) Hn5). reflexivity. }
      forward_if (temp _t'9 (Vint (Int.repr (unc_ret err (Zlength src - used))))).
      { forward. forward. forward. entailer!. ret_tac. }
      { forward. forward. forward. entailer!. ret_tac. }
      all: try entailer!. }
    all: try entailer!. }
  unfold istream, zstrm_at, strm_rep. Intros. change_compspecs Zlib.units.Uncompr.CS.
  forget (gv inflate.code._zcalloc) as zca. forget (gv inflate.code._zcfree) as zcf.
  forward.
  Exists (unc_ret err (Zlength src - used)) used (Zlength out) out.
  apply andp_right; [apply prop_right; split; [right; exists err; auto | reflexivity] |].
  unfold uversion_lit, inflate_globals, uw_lit.
  sep_apply (data_at_data_at_ Tsh t_strm). cancel.
Qed.

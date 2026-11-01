(* Body of inflateSync, segment 4 (Body5_sync_kit.v): the pattern was found; from `if (state->flags == -1)` (no
   header read yet: raw, with a window of 2^15 if none was set; else no check value) to `flags = state->flags`. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.Body5_sync_kit.
#[local] Existing Instance Zlib.units.Inflate.CS.

Local Open Scope logic.

Lemma sync_part4 (NEXT: sync_seg5) : sync_seg4.
Proof.
  intros E gv shs strmp z sp winp s h headp hsh xb nb cb ish ip ilo ilen ic inp v_buf s1 bc len.
  intros HY LOK1 M1 SS GL SG.
  pose proof HY as (HIN & NI & H2 & ZOK & H4 & Hn).
  pose proof HIN as (ISH & IP & ILO & ILEN & IC & IMAX & ISUB & IBY).
  pose proof ZOK as (ZAI & ZAO & ZTIN & ZTOUT & ZDT & ZADL).
  set (s1g := set_i_have s1 4) in *.
  destruct (have_fields s1 4) as (HM & HW & HF & HB & HH & HBI & HG). fold s1g in HM, HW, HF, HB, HH, HBI, HG.
  set (s2 := sync_fix s1g).
  destruct (sync_fix_ww s1g) as [W2 B2]. fold s2 in W2, B2.
  assert (SW1: swf s1) by (destruct LOK1 as (_ & X & _); exact X).
  assert (Hsp: isptr sp) by (destruct LOK1 as (X & _); exact X).
  sync_seg_start.
  remember (gv _zcalloc) as zca eqn:Hzca. remember (gv _zcfree) as zcf eqn:Hzcf.
    forward.
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx Q (SEPx (replace_nth 8 (replace_nth 10 R
          (field_at Ews t_state (DOT _wbits) (zv (i_wbits s2)) sp))
          (field_at Ews t_state (DOT _wrap) (zv (i_wrap s2)) sp)))))
    end.
    { clear SG.
      assert (FM: i_flags s1 = -1).
      { match goal with X: Int.repr (i_flags s1) = _ |- _ => rewrite Int.neg_repr in X; apply repr_inj_signed in X;
          [exact X | pose proof (sw_flags _ SW1); unfold srange in *; rep_lia | rep_lia] end. }
      forward. forward.
      forward_if.
      { forward. assert (WZ: i_wbits s1 = 0).
        { match goal with X: Int.repr (i_wbits s1) = _ |- _ => apply repr_inj_unsigned in X;
            [exact X | pose proof (sw_wbits _ SW1); rep_lia | rep_lia] end. }
        rewrite W2, B2, HF, HB, FM, Z.eqb_refl, (proj2 (Z.eqb_eq _ _) WZ). entailer!.
        all: cbn [replace_nth fold_right_sepcon]; cancel. }
      { forward. assert (WN: i_wbits s1 <> 0).
        { intro X. rewrite X in *. contradiction. }
        rewrite W2, B2, HF, HB, FM, Z.eqb_refl, (proj2 (Z.eqb_neq _ _) WN). entailer!.
        all: cbn [replace_nth fold_right_sepcon]; cancel. } }
    { clear SG.
      assert (FM: i_flags s1 <> -1).
      { intro X. rewrite X in *. match goal with Y: Int.repr (-1) <> _ |- _ => apply Y; reflexivity end. }
      forward. forward.
      rewrite and_not4 by exact (sw_wrap_range _ SW1).
      rewrite W2, B2, HF, HB, HW, (proj2 (Z.eqb_neq _ _) FM). entailer!.
      all: cbn [replace_nth fold_right_sepcon]; cancel. }
    cbn [replace_nth].
    drop_LOCAL 0%nat. subst zca zcf.
    exact (NEXT E gv shs strmp z sp winp s h headp hsh xb nb cb ish ip ilo ilen ic inp v_buf s1 bc len
             HY LOK1 M1 SS GL SG).
Qed.

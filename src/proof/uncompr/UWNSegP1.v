(* uncompress2_z with a Z_NULL source of length 0 (UWNSegs.v), statements 0-4: the argument checks pass since
   *sourceLen = 0 (a Z_NULL source is then allowed), len = 0, left = *destLen, and dest becomes the stream's member
   reserved when it is Z_NULL.  The script is UWSegP1.v's. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Uncompr.
Require Zlib.units.Inflate.
Require Import Zlib.uncompr.code.
Require Import Zlib.proof.uncompr.UWNSegs.
Require Import Zlib.proof.inflate_api.Spec5.
Require Import Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Uncompr.CS.
Local Open Scope logic.

Lemma un_p1 : un_p1_stmt.
Proof.
  intros Espec A v F K.
  destruct A as [gv dnull dsh dp dn dc cap dlp dtok slp gsh tsh].
  unfold un_facts in F. destruct F as (Hd & Hg & Ht).
  unfold PRE_un, un_A5, un_lcl, POST_un in *. unfold uw_seg0. abbreviate_semax.
  forward.
  assert_PROP (isptr slp /\ isptr dlp) as Hpp by entailer!. destruct Hpp as [Hslp Hdlp].
  forward_if (temp _t'1 (Val.of_bool false)).
  { subst slp; contradiction. }
  { forward. forward_if (temp _t'1 (Val.of_bool false)).
    - match goal with Hx: Int64.unsigned _ < Int64.unsigned _ |- _ => rewrite !Int64.unsigned_repr in Hx by rep_lia end.
      lia.
    - forward. entailer!.
    - entailer!. }
  forward_if (temp _t'2 (Val.of_bool false)).
  { contradiction. }
  { forward. entailer!. destruct dlp; try contradiction; reflexivity. }
  destruct dnull.
  - (* Z_NULL destination of 0 bytes: dest becomes &stream.reserved *)
    destruct Hd as (-> & -> & -> & -> & ->). unfold dest_rep.
    forward_if (temp _t'3 (Val.of_bool false)).
    { contradiction. }
    { forward. forward_if (temp _t'3 (Val.of_bool false)).
      - match goal with Hx: Int64.unsigned _ < Int64.unsigned _ |- _ => rewrite !Int64.unsigned_repr in Hx by rep_lia end. lia.
      - forward. entailer!.
      - entailer!. }
    forward_if.
    { contradiction. }
    forward. forward.
    forward_if (temp _t'4 (Val.of_bool true)).
    { forward. entailer!. }
    { match goal with Hx: Int64.repr 0 <> Int64.repr 0 |- _ => contradiction end. }
    forward_if (temp _dest (offset_val 104 v)).
    2: { match goal with Hx: Int.one = Int.zero |- _ => inv Hx end. }
    { forward. entailer!. }
    eapply semax_pre; [| exact K]. unfold uw_dq, dest_rep. entailer!.
  - (* a destination object *)
    destruct Hd as (Hdsh & Hdp & Hcap & Hdtok & Hdc & Hdn). unfold dest_rep. Intros.
    forward_if (temp _t'3 (Val.of_bool false)).
    { contradiction. }
    { forward. forward_if (temp _t'3 (Val.of_bool false)).
      - try match goal with Hx: Int64.unsigned _ < Int64.unsigned _ |- _ => rewrite !Int64.unsigned_repr in Hx by rep_lia end.
        forward. forward. entailer!. destruct dp; try contradiction; reflexivity.
      - forward. entailer!.
      - entailer!. }
    forward_if.
    { contradiction. }
    forward. forward.
    forward_if (temp _t'4 (Val.of_bool false)).
    + forward.
      * entailer!. apply denote_tc_test_eq_split; [| auto with valid_pointer].
        buf_valid_tac dsh (Zlength dc) dc dp dtok.
      * entailer!. destruct dp; try contradiction; reflexivity.
    + forward. entailer!.
    + forward_if (temp _t'4 (Val.of_bool false)).
      * contradiction.
      * forward. entailer!.
      * eapply semax_pre; [| exact K]. unfold uw_dq, dest_rep. entailer!.
Qed.

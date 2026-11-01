(* The decode theory for calls of up to 2^32 - 1 bytes of input and of output space on inputs of any length:
   Decode7.v's decode_init7_stmt and decode_call7_stmt.

   They are the theorems of the wide port of the decode theory (src/proof/wide/rfc1951/, generated from
   src/proof/rfc1951/ by docs/port-za/port.py with docs/port-za/cfg_wide_decode.py): Decode.decode_of_parts
   with the machine invariant Inv.mwf's bounds on a call's input and output space raised to Int.max_unsigned
   (mwf_wide) and DecodeDefs.dctx_ok's bound on the input raised to 2^64 - 1 (dctx_ok_wide, literally
   Decode7.dctx_ok7).  The one part the port does not prove is the preservation of the machine invariant by a
   pass of the switch (stepf2_kd_stmt); it follows from InvW.stepf2_mwf3W_stmt, the same preservation for
   InvW's wide invariant, whose extra condition hdrW is about modes EXLEN / EXTRA only, where a decoder
   between two passes never is (DecodeDefs.kd_not_ext). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.rfc1951.Decode7.
Require Import Zlib.proof.inflate.InvW.
Require Zlib.proof.inflate.StepW.
Require Import Zlib.proof.wide.rfc1951.Decode.
Require Import Zlib.proof.wide.rfc1951.DecKit.
Require Import Zlib.proof.rfc1951.TabDec.
Require Import Zlib.proof.wide.rfc1951.DecHdr.
Require Import Zlib.proof.wide.rfc1951.DecType.
Require Import Zlib.proof.wide.rfc1951.DecTab.
Require Import Zlib.proof.wide.rfc1951.DecDec.
Require Import Zlib.proof.wide.rfc1951.DecFast.
Require Import Zlib.proof.wide.rfc1951.DecTrl.
Require Import Zlib.proof.wide.rfc1951.DecCall.
Import ListNotations.
Local Open Scope Z_scope.

(* the port's wide machine invariant is InvW's mwfW, field by field *)
Lemma mwf_wide_mwfW m : mwf_wide m -> mwfW m.
Proof. intros []. constructor; assumption. Qed.

Lemma mwfW_mwf_wide m : mwfW m -> mwf_wide m.
Proof. intros []. constructor; assumption. Qed.

(* a pass of the switch keeps the invariant, from a machine outside EXLEN / EXTRA *)
Lemma stepf2_kd_of_mwf3W : stepf2_mwf3W_stmt -> stepf2_kd_stmt.
Proof.
  intros SW flush m [W S] [N1 N2] L.
  assert (H: mwf3W m).
  { split; [apply mwf_wide_mwfW; exact W|]. split; [exact S|]. split; intros E; contradiction. }
  pose proof (SW flush m H L) as R.
  destruct (Zlib.proof.inflate.Model2.stepf2 flush lenfix_list distfix_list m) as [m'|r m'];
    destruct R as (W' & S' & _); (split; [apply mwfW_mwf_wide; exact W' | exact S']).
Qed.

(* dctx_ok7's windowBits for a zlib stream (the header's window, 0 or 32 + it) is among the port's *)
Lemma dctx_ok7_wide G : dctx_ok7 G -> dctx_ok_wide G.
Proof.
  intros (S & A & R). split; [exact S|]. split; [|exact R].
  destruct S as (Hwb & _). unfold accepts, accepts_wide in *.
  destruct (dc_w G); [exact A| |exact A]. destruct A as [A|A]; [left; lia|right; exact A].
Qed.

Theorem decode7_of_mwf3W : stepf2_mwf3W_stmt -> decode_init7_stmt /\ decode_call7_stmt.
Proof.
  intros SW.
  destruct (decode_of_parts_wide
    (conj dkit_wide (conj tabdec (conj (stepf2_kd_of_mwf3W SW)
    (conj (proj1 dec_hdr_part_wide) (conj (proj2 dec_hdr_part_wide)
    (conj group_type_wide (conj group_tab_wide (conj group_dec_wide (conj dfast_wide
    (conj group_trl_wide dec_call_wide))))))))))) as [I C].
  split.
  - intros G sp D. exact (I G sp (dctx_ok7_wide G D)).
  - intros G pos out L z inp flush res D. exact (C G pos out L z inp flush res (dctx_ok7_wide G D)).
Qed.

(* the decode theory for calls of any size *)
Theorem decode7 : decode_init7_stmt /\ decode_call7_stmt.
Proof. exact (decode7_of_mwf3W Zlib.proof.inflate.StepW.stepf2_mwf3W). Qed.

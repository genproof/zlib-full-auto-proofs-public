(* Decode7Step's statements (the decode theory with inflateInit2's window larger than a zlib header's, and
   its invariant at the loop heads of a call), from the wide port of the decode theory (src/proof/wide/rfc1951/)
   and InvW.stepf2_mwf3W (StepW.v). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.rfc1951.Decode7Step.
Require Zlib.proof.inflate.StepW.
Require Import Zlib.proof.rfc1951.TabDec.
Require Import Zlib.proof.wide.rfc1951.Decode.
Require Import Zlib.proof.wide.rfc1951.DecKit.
Require Import Zlib.proof.wide.rfc1951.DecHdr.
Require Import Zlib.proof.wide.rfc1951.DecType.
Require Import Zlib.proof.wide.rfc1951.DecTab.
Require Import Zlib.proof.wide.rfc1951.DecDec.
Require Import Zlib.proof.wide.rfc1951.DecFast.
Require Import Zlib.proof.wide.rfc1951.DecTrl.
Require Import Zlib.proof.wide.rfc1951.DecCall.
Require Import Zlib.proof.wide.Decode7.
Import ListNotations.
Local Open Scope Z_scope.

(* dctx_ok7a is the port's dctx_ok_wide: accepts7 is the port's accepts (a zlib window from the header's to 15
   contains the header's own window, which stream_ok bounds by 8..15) *)
Lemma dctx_ok7a_wide G : dctx_ok7a G -> dctx_ok_wide G.
Proof.
  intros (S & A & R). split; [exact S|]. split; [|exact R].
  destruct S as (Hwb & _). unfold accepts7, accepts, accepts_wide in *.
  destruct A as [A|(wb & fl & did & E & A)].
  - destruct (dc_w G); [exact A| |exact A]. destruct A as [A|A]; [left; lia|right; exact A].
  - rewrite E. left. exact A.
Qed.

(* InvW's wide machine invariant and the port's, at a loop head (never in EXLEN / EXTRA) *)
Lemma mwf3W_mwf3_wide m : mwf3W m -> mwf3_wide m.
Proof. intros (W & S & _). split; [apply mwfW_mwf_wide; exact W | exact S]. Qed.

Lemma mwf3_wide_mwf3W G pos inp ob m : Kd G pos inp ob m -> mwf3_wide m -> mwf3W m.
Proof.
  intros K (W & S). destruct (kd_not_ext _ _ _ _ _ K) as (N1 & N2).
  split; [apply mwf_wide_mwfW; exact W|]. split; [exact S|]. split; intros E; contradiction.
Qed.

(* the parts of the wide decode theory *)
Lemma parts_wide : decode_parts_wide.
Proof.
  exact (conj dkit_wide (conj tabdec (conj (stepf2_kd_of_mwf3W Zlib.proof.inflate.StepW.stepf2_mwf3W)
    (conj (proj1 dec_hdr_part_wide) (conj (proj2 dec_hdr_part_wide)
    (conj group_type_wide (conj group_tab_wide (conj group_dec_wide (conj dfast_wide
    (conj group_trl_wide dec_call_wide)))))))))).
Qed.

(* one pass of the switch from a loop head, every group *)
Lemma dc_all_wide_ok : dc_all_wide.
Proof.
  destruct parts_wide as (K & T & S & _ & H & Ty & Ta & De & Fa & Tr & _).
  pose proof (De K (Fa K)) as DE.
  exact (dc_step_wide (H K) (Ty K T) (Ta K T S DE) DE (Tr K)).
Qed.

Theorem decode7a : decode7a_stmt.
Proof.
  destruct (decode_of_parts_wide parts_wide) as [I C].
  split; [|split; [|split; [|split]]].
  - intros G sp D. exact (I G sp (dctx_ok7a_wide G D)).
  - intros G pos out L z inp flush res D. exact (C G pos out L z inp flush res (dctx_ok7a_wide G D)).
  - intros G pos out L z inp D DI LV ZF AO LI BI.
    destruct (dc_init_wide G pos out L z inp DI LV ZF AO LI BI) as (K & W).
    split; [exact K | exact (mwf3_wide_mwf3W _ _ _ _ _ K W)].
  - intros G pos inp ob flush m D P0 PL IE K W L.
    exact (dc_all_wide_ok G pos inp ob flush m (dctx_ok7a_wide G D) P0 PL IE K (mwf3W_mwf3_wide m W) L).
  - exact Zlib.proof.inflate.StepW.stepf2_mwf3W.
Qed.

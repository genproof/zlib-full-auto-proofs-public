(* Law rt_session (harness/rt_session.c), main's statement 23 (SMA1Kit.v), the case where none of the five
   pointers is NULL: every operand is 0, main goes on, in the state A24 of the setup of the drawn values and the
   five objects. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.rt_session.SCS.
Require Import Zlib.proof.harness.rt_session.SDFacts.
Require Import Zlib.proof.harness.rt_session.SMainStmt.
Require Import Zlib.proof.harness.rt_session.SMKit.
Require Import Zlib.proof.harness.rt_session.SMA1Kit.
Require Import Zlib.harness.rt_session.code.
#[local] Existing Instance SCS.CS.
Local Open Scope logic.

Lemma sa1_c6 {Espec : OracleKind} gv vh vg vc va vd lvl wb mem str ch dl cap text utm os hcrc
    dict xf nm cm data dp xp np cmp datp :
  a1_facts lvl wb mem str ch dl cap text utm os hcrc dict xf nm cm data ->
  dp <> nullval -> xp <> nullval -> np <> nullval -> cmp <> nullval -> datp <> nullval ->
  a1_triple gv vh vg vc va vd lvl wb mem str ch dl cap text utm os hcrc dict xf nm cm data dp xp np cmp datp.
Proof.
  intros HF Hd Hx Hn Hc Ht. sa1_start.
  sa1_nn dp dict. sa1_mkptr dp bd od. sa1_nn xp xf. sa1_mkptr xp bx ox.
  sa1_ifpost _t'24 (Vint Int.zero); [sa1_tceq | sa1_nob | forward; [sa1_tceq | sa1_close] | ].
  sa1_nn np (nm ++ [0]). sa1_mkptr np bn on.
  sa1_ifpost _t'25 (Vint Int.zero); [sa1_nob | forward; [sa1_tceq | sa1_close] | ].
  sa1_nn cmp (cm ++ [0]). sa1_mkptr cmp bc oc.
  sa1_ifpost _t'26 (Vint Int.zero); [sa1_nob | forward; [sa1_tceq | sa1_close] | ].
  sa1_nn datp data. sa1_mkptr datp bt ot.
  sa1_ifpost _t'27 (Vint Int.zero); [sa1_nob | forward; [sa1_tceq | sa1_close] | ].
  forward_if; [sa1_nob | ].
  forward.
  (* the setup of the draws and the five objects; the other objects are not allocated yet *)
  set (U := mkSU lvl wb mem str ch dict xf nm cm data cap text utm os hcrc (Vptr bd od) (Vptr bx ox) (Vptr bn on)
              (Vptr bc oc) (Vptr bt ot) nullval nullval nullval nullval nullval nullval nullval nullval nullval
              nullval).
  assert (HU : su_dok U).
  { unfold a1_facts in HF. unfold su_dok.
    cbn [su_level su_wbits su_mem su_strategy su_choice su_dict su_xf su_nm su_cm su_data su_cap su_text su_time
         su_os su_hcrc su_dictp su_xp su_np su_cmp su_dp U].
    destruct HF as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17 &
                    F18 & F19 & F20 & F21 & F22).
    rewrite F7. unfold rs32 in *. repeat split; try exact I; auto; lia. }
  Exists U. unfold A24, o_locals, d_locals, lvs, lv_locals, dictobj, datobj, with_dict, with_head.
  cbn [su_level su_wbits su_mem su_strategy su_choice su_dict su_xf su_nm su_cm su_data su_cap su_text su_time
       su_os su_hcrc su_dictp su_xp su_np su_cmp su_dp U app].
  entailer!.
Qed.

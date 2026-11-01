(* The generalized decode theory of the round trip (RTIGDefs.v: any gzip header, a gz_header attached) for calls of
   up to 2^32 - 1 bytes of input and of output space on inputs of any length.

   RTIGTheory.rtig_loop_ok states the rest of ONE call from a loop head (Kd) for inputs of at most 2^31 - 1 bytes
   (RTIGDefs.dctx_ok, Inv3.mwf3), and gives no invariant between calls.  Law rt_gzip_header feeds inflate() a gzip
   stream with a header of up to ~2^33 bytes in pieces of up to 2^32 - 1 bytes: after the header (which may end
   in the middle of a call) the calls need the decode invariant from a loop head to the end of the call and from
   one call to the next ([rtigw_loop], [rtigw_init]), with InvW's wide machine invariant (mwf3W).  [rtigw_ok] is
   RTIGDefs.dctx_ok with the input's length bounded by 2^64 - 1 only. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTIGDefs.
Require Export Zlib.proof.inflate.InvW.
Require Export Zlib.proof.inflate_api.Spec5.
Require Zlib.proof.inflate.StepW.
Require Zlib.proof.wide.Decode7.
Require Zlib.proof.rfc1951.TabDec.
Require Zlib.proof.wide.roundtrip.RTIGDefs.
Require Zlib.proof.wide.roundtrip.RTIGDecKit.
Require Zlib.proof.wide.roundtrip.RTIGDecType.
Require Zlib.proof.wide.roundtrip.RTIGDecTab.
Require Zlib.proof.wide.roundtrip.RTIGDecDec.
Require Zlib.proof.wide.roundtrip.RTIGDecFast.
Require Zlib.proof.wide.roundtrip.RTIGDecTrl.
Require Zlib.proof.wide.roundtrip.RTIGDecCall.
Import ListNotations.
Local Open Scope Z_scope.

Definition rtigw_ok (G: dctx) : Prop :=
  stream_ok (dc_w G) (dc_wb G) (dc_hist G) (dc_bs G) /\ accepts G /\
  (forall wb fl did, dc_w G = WZlib wb fl did ->
     did = None \/ did = Some (Zlib.proof.adler32.Model.ref_adler32 1 (dc_hist G))) /\
  slen G <= Zlength (dc_src G) /\ Zlength (dc_src G) <= 2 ^ 64 - 1 /\ bytes_ok (dc_src G) /\
  sublist 0 (slen G) (dc_src G) = stream_bytes (dc_w G) (dc_hist G) (dc_bs G).

(* the start of a call (DecCall.dc_init over RTIGDefs) *)
Definition rtigw_init_stmt : Prop := forall G pos out L z inp,
  rtigw_ok G -> dinv G pos out (l_s L) (zf_tout z) -> live_ok L -> zf_ok z ->
  zf_ao z <= 2 ^ 32 - 1 -> Zlength inp <= 2 ^ 32 - 1 -> bytes_ok inp ->
  Kd G pos inp out (m_init z L inp) /\ mwf3W (m_init z L inp).

(* the rest of a call from a loop head: RTIGDefs.rtig_loop_stmt for wide calls, with the decode invariant
   between calls at the end (as Decode.decode_call_stmt) *)
Definition rtigw_loop_stmt : Prop := forall G pos inp ob flush m o res,
  rtigw_ok G -> 0 <= pos -> pos + Zlength inp <= Zlength (dc_src G) ->
  inp = sublist pos (pos + Zlength inp) (dc_src G) ->
  Kd G pos inp ob m -> mwf3W m -> m_leave m = 0 ->
  (exists d0, ob = dc_hist G ++ d0) -> bytes_ok ob ->
  loop2 flush lenfix_list distfix_list m o ->
  match o with IRet r m' => res = Res r m' None | IBrk m' => inf_leave flush m' res end ->
  let m' := r_m res in
  r_ret res = Z_MEM_ERROR \/
  ((r_ret res = Z_OK \/ r_ret res = Z_BUF_ERROR \/ r_ret res = Z_STREAM_END) /\
   0 <= m_snx m' <= Zlength inp /\ m_sow m' = Zlength (m_ow m') /\ m_aout m' = m_aout m /\
   (exists rest, full G = ob ++ m_ow m' ++ rest) /\
   dinv G (pos + m_snx m') (ob ++ m_ow m') (m_s m') (m_tout m') /\
   (r_ret res = Z_STREAM_END -> ob ++ m_ow m' = full G /\ pos + m_snx m' = slen G) /\
   (r_ret res <> Z_STREAM_END ->
      (m_snx m' = Zlength inp /\ pos + Zlength inp < slen G) \/
      (Zlength (m_ow m') = m_aout m /\ Zlength (ob ++ m_ow m') < Zlength (full G)) \/
      flush = Z_BLOCK \/ flush = Z_TREES)).

(* The proofs below are those of the wide port of the generalized theory (src/proof/wide/roundtrip/RTIG*.v,
   generated from RTIGDec*.v by docs/port-za/port_rtig.py): its context condition is RTIGDefs.dctx_ok with the
   bound 2^64 - 1 and the zlib windowBits of the wide decode theory (DecodeDefs.accepts widened), its machine
   invariant Inv3.mwf3 with the bounds of a call raised to 2^32 - 1. *)
Module P := Zlib.proof.wide.roundtrip.RTIGDefs.
Module C := Zlib.proof.wide.roundtrip.RTIGDecCall.

(* rtigw_ok is the port's context condition *)
Lemma rtigw_ok_wide G : rtigw_ok G -> P.dctx_ok_wide G.
Proof.
  intros (S & A & D & R).
  split; [exact S|]. split; [|split; [intros; exact I|split; [exact D|exact R]]].
  destruct S as (Hwb & _). unfold accepts, Zlib.proof.wide.rfc1951.DecodeDefs.accepts_wide in *.
  destruct (dc_w G); [exact A| |exact A]. destruct A as [A|A]; [left; lia|right; exact A].
Qed.

(* the port's machine invariant and InvW's, at a loop head (never in EXLEN / EXTRA) *)
Lemma mwf3W_wide m : mwf3W m -> Zlib.proof.wide.inflate.Inv3.mwf3_wide m.
Proof.
  intros (W & S & _). split; [apply Zlib.proof.wide.Decode7.mwfW_mwf_wide; exact W | exact S].
Qed.

Lemma mwf3_wide_W G pos inp ob m : Kd G pos inp ob m -> Zlib.proof.wide.inflate.Inv3.mwf3_wide m -> mwf3W m.
Proof.
  intros K (W & S). destruct (P.kd_not_ext _ _ _ _ _ K) as [N1 N2].
  split; [apply Zlib.proof.wide.Decode7.mwf_wide_mwfW; exact W|]. split; [exact S|].
  split; intros E; contradiction.
Qed.

Lemma rtigw_init : rtigw_init_stmt.
Proof.
  intros G pos out L z inp _ DI LV ZF AO LI BI.
  destruct (C.dc_init_wide G pos out L z inp DI LV ZF ltac:(cbn; lia) ltac:(cbn; lia) BI) as [K W].
  split; [exact K|]. exact (mwf3_wide_W _ _ _ _ _ K W).
Qed.

Lemma rtigw_loop : rtigw_loop_stmt.
Proof.
  intros G pos inp ob flush m o res OK P0 PL IE K0 W0 L0 HP BO LP RO.
  pose proof (rtigw_ok_wide G OK) as CW.
  pose proof Zlib.proof.wide.roundtrip.RTIGDecKit.dkit_wide as K.
  pose proof (Zlib.proof.wide.Decode7.stepf2_kd_of_mwf3W Zlib.proof.inflate.StepW.stepf2_mwf3W) as SM.
  pose proof (Zlib.proof.wide.roundtrip.RTIGDecDec.group_dec_wide K
                (Zlib.proof.wide.roundtrip.RTIGDecFast.dfast_wide K)) as H4.
  pose proof (C.dc_step_wide (Zlib.proof.wide.roundtrip.RTIGDecType.group_type_wide K Zlib.proof.rfc1951.TabDec.tabdec)
    (Zlib.proof.wide.roundtrip.RTIGDecTab.group_tab_wide K Zlib.proof.rfc1951.TabDec.tabdec SM H4) H4
    (Zlib.proof.wide.roundtrip.RTIGDecTrl.group_trl_wide K)) as ST.
  destruct (C.dc_loop_wide SM ST G pos inp ob flush CW P0 PL IE _ _ LP K0 (mwf3W_wide _ W0) L0)
    as (mE & -> & KE & WE & LE & (d & Dw) & WHY & AE).
  inversion RO; subst.
  - left. reflexivity.
  - right.
    destruct (C.dc_fin_wide K G pos inp ob flush mE CW KE WE LE WHY HP BO)
      as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10).
    rewrite AE in R4, R9.
    split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [exact R4|].
    split; [exact R6|]. split; [exact R7|]. split; [exact R8|]. exact R9.
Qed.

Theorem rtigw : rtigw_init_stmt /\ rtigw_loop_stmt.
Proof. exact (conj rtigw_init rtigw_loop). Qed.

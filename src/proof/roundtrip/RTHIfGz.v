(* RT-H: the gzip header passes and the gzip run of deflate_roundtrip's inflate() call, with the
   facts RTHIfDefs.ifacts6 needs beyond RTIGzPass.rti_gz_pass / RTIGz.rti_gz_run: the modes of the two passes,
   state->flags after the header (gp_F), the explicit gz_header after it (gh_at 8), and the mode at the end of
   the call (a mode after the header, or MEM). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import compcert.lib.Integers.
Require Import Zlib.proof.roundtrip.RTIKit.
Require Import Zlib.proof.roundtrip.RTIGDefs.
Require Import Zlib.proof.roundtrip.RTIGzPassDefs.
Require Import Zlib.proof.roundtrip.RTIGDecCall.
Require Zlib.proof.roundtrip.RTIGzPassHF Zlib.proof.roundtrip.RTIGzPassEx Zlib.proof.roundtrip.RTIGzPassNC Zlib.proof.roundtrip.RTIGzPassHc Zlib.proof.roundtrip.RTIGzPassKd Zlib.proof.roundtrip.RTIGzPassCtx.
Require Zlib.proof.roundtrip.RTIGTheory Zlib.proof.roundtrip.RTIGz.
Require Zlib.proof.rfc1951.Decode.
Import ListNotations.
Local Open Scope Z_scope.

Lemma rthi_gz_pass : forall gh xfl wb bs D O L z,
  9 <= wb <= 15 -> wf (2 ^ wb) [] bs -> data [] bs = D -> (xfl = 0 \/ xfl = 2 \/ xfl = 4) ->
  O = stream_bytes (WGzip (RF.fhdr_of gh xfl)) [] bs ->
  (forall g, gh = Some g -> RF.rhdr_ok g) ->
  Zlength D <= 1048576 -> Zlength O <= 4194304 ->
  live_ok L -> zcall_ok z O D ->
  (l_s L = init_s 7 0 \/
   (l_s L = set_i_head (init_s 7 0) true /\ h_done (l_h L) = 0 /\
    exists g x nm cm, gh = Some g /\ head_bufs g x nm cm (l_h L))) ->
  let G := gz_ctx gh xfl wb bs O in
  dctx_ok G /\
  exists m1 m2,
    stepf2 Z_FINISH lenfix_list distfix_list (m_init z L O) = IBrk m1 /\ m_leave m1 = 0 /\
    m_mode m1 = FLAGS /\
    stepf2 Z_FINISH lenfix_list distfix_list m1 = IBrk m2 /\ m_leave m2 = 0 /\
    Kd G 0 O [] m2 /\ m_mode m2 = Zlib.proof.inflate.Model.TYPE /\ m_ow m2 = [] /\ m_aout m2 = zf_ao z /\
    i_flags (m_s m2) = gp_F gh xfl /\
    (i_head (l_s L) = true -> exists g x nm cm, gh = Some g /\ head_bufs g x nm cm (l_h L) /\
       m_h m2 = gh_at xfl (l_h L) 8 g x nm cm).
Proof.
  intros gh xfl wb bs D O L z Hwb Hwf HD Hx HO Hgh LD LO LV ZC HL G.
  pose proof (Zlib.proof.roundtrip.RTIGzPassCtx.gp_dctx_ok gh xfl wb bs D O Hwb Hwf HD Hx HO Hgh LD LO) as C.
  destruct (Zlib.proof.roundtrip.RTIGzPassHF.gp_hf_ok) as (GH & GF & GT & GO).
  destruct (Zlib.proof.roundtrip.RTIGzPassEx.gp_ex_ok) as (GE & GX).
  destruct (Zlib.proof.roundtrip.RTIGzPassNC.gp_nc_ok) as (GN & GC).
  pose proof Zlib.proof.roundtrip.RTIGzPassHc.gp_hc_ok as GK.
  pose proof Zlib.proof.roundtrip.RTIGzPassKd.gp_kd_ok as KD.
  assert (OK: gp_ok gh xfl O).
  { split; [|split; [|split; [exact Hgh | split; [exact Hx | exact LO]]]].
    - rewrite HO. cbn [stream_bytes]. eexists. reflexivity.
    - exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 C))))))). }
  set (hd := i_head (l_s L)).
  set (h0 := l_h L).
  assert (HB: hd = true -> exists g x nm cm, gh = Some g /\ head_bufs g x nm cm h0 /\ h_done h0 = 0).
  { intros E. destruct HL as [S | (S & Hd & g & x & nm & cm & Eg & B)].
    - unfold hd in E. rewrite S in E. discriminate.
    - exists g, x, nm, cm. split; [exact Eg|]. split; [exact B|]. exact Hd. }
  assert (HL': l_s L = init_s 7 0 \/ l_s L = set_i_head (init_s 7 0) true) by (destruct HL as [S | (S & _)]; [left | right]; exact S).
  destruct (GH gh xfl O z L OK HL') as (m1 & S1 & M1 & K1 & H1).
  assert (E1: stepf2 Z_FINISH lenfix_list distfix_list m1 = c_FLAGS2 m1).
  { unfold stepf2, step2, m_mode. rewrite (gm_mode _ _ _ _ _ _ M1). reflexivity. }
  destruct (GF gh xfl O z hd h0 m1 OK M1 K1 H1 HB) as (mT & ET & ST).
  destruct (GT gh xfl O z hd h0 mT OK ST) as (mO & EO & SO).
  destruct (GO gh xfl O z hd h0 mO OK SO) as (mE & EE & SE).
  destruct (GE gh xfl O z hd h0 mE OK SE) as (mX & EX & SX & LX).
  destruct (GX gh xfl O z hd h0 mX OK SX LX) as (mN & EN & SN & LN).
  destruct (GN gh xfl O z hd h0 mN OK SN LN) as (mC & EC & SC & LC).
  destruct (GC gh xfl O z hd h0 mC OK SC LC) as (mH & EH & SH).
  destruct (GK gh xfl O z hd h0 mH OK SH) as (m2 & E2 & M2 & F2 & HH2 & K2).
  split; [exact C|].
  exists m1, m2.
  split; [exact S1|]. split; [exact (gm_leave _ _ _ _ _ _ M1)|].
  split; [exact (gm_mode _ _ _ _ _ _ M1)|].
  split; [rewrite E1, ET, EO, EE, EX, EN, EC, EH; exact E2|].
  split; [exact (gm_leave _ _ _ _ _ _ M2)|].
  split; [exact (KD gh xfl wb bs O z hd h0 m2 Hwb HO C (proj2 (proj2 (proj2 ZC))) M2 F2 HH2 K2)|].
  split; [exact (gm_mode _ _ _ _ _ _ M2)|].
  split; [exact (gm_ow _ _ _ _ _ _ M2)|].
  split; [exact (gm_aout _ _ _ _ _ _ M2)|].
  split; [exact F2|].
  intros Ehd.
  destruct (HH2 Ehd) as (g' & x' & nm' & cm' & Eg' & B' & _ & Hm).
  exists g', x', nm', cm'. auto.
Qed.

Lemma rthi_uw_mode (s: istate) (d: list Z) : i_mode (updatewindow s d) = i_mode s.
Proof.
  unfold updatewindow. cbv zeta.
  destruct (i_wsize s =? 0); cbn [set_i_whave set_i_wnext set_i_wsize i_wsize];
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; reflexivity.
Qed.

(* inf_leave keeps the mode, or sets MEM *)
Lemma rthi_leave_mode flush m res : inf_leave flush m res ->
  m_mode (r_m res) = m_mode m \/ m_mode (r_m res) = MEM.
Proof.
  intros H. inversion H; subst; [right; reflexivity|].
  left. unfold leave_fin. cbv zeta.
  destruct (leave_ok flush m); cbn;
  destruct (negb (Z.land _ 4 =? 0) && _); cbn; rewrite ?rthi_uw_mode; reflexivity.
Qed.

Lemma rthi_kd_mode G pos inp ob m : Kd G pos inp ob m -> Zlib.proof.inflate.Model.TYPE <= m_mode m <= DONE.
Proof.
  intros K. destruct (Zlib.proof.roundtrip.RTIGz.rtig_kd_groups _ _ _ _ _ K) as [M|[M|[M|M]]];
    [unfold md_type in M | unfold md_tab in M | unfold md_dec in M | unfold md_trl in M];
    repeat destruct M as [M|M]; rewrite M; vm_compute; split; discriminate.
Qed.

(* the run: the gz_header after the call is the one after the header passes, and the call ends in a mode
   after the header (TYPE .. DONE) or MEM *)
Lemma rthi_gz_run : Zlib.proof.rfc1951.Decode.decode_parts ->
  forall gh xfl wb bs D O L z res,
  9 <= wb <= 15 -> wf (2 ^ wb) [] bs -> data [] bs = D -> (xfl = 0 \/ xfl = 2 \/ xfl = 4) ->
  O = stream_bytes (WGzip (RF.fhdr_of gh xfl)) [] bs ->
  (forall g, gh = Some g -> RF.rhdr_ok g) ->
  Zlength D <= 1048576 -> Zlength O <= 4194304 ->
  live_ok L -> zcall_ok z O D ->
  (l_s L = init_s 7 0 \/
   (l_s L = set_i_head (init_s 7 0) true /\ h_done (l_h L) = 0 /\
    exists g x nm cm, gh = Some g /\ head_bufs g x nm cm (l_h L))) ->
  run2 Z_FINISH lenfix_list distfix_list (m_init z L O) res ->
  (Zlib.proof.inflate.Model.TYPE <= m_mode (r_m res) <= DONE \/ m_mode (r_m res) = MEM) /\
  (i_head (l_s L) = true -> exists g x nm cm, gh = Some g /\ head_bufs g x nm cm (l_h L) /\
       m_h (r_m res) = gh_at xfl (l_h L) 8 g x nm cm).
Proof.
  intros DP gh xfl wb bs D O L z res Hwb Hwf HD Hx HO Hgh LD LO LV ZC HL RUN.
  pose proof DP as (_ & T & SM & _).
  pose proof (Zlib.proof.roundtrip.RTIGTheory.rtig_parts_ok) as (K & Ty & Ta & De & Fa & Tr & _).
  pose proof (dc_step (Ty K T) (Ta K T SM (De K (Fa K))) (De K (Fa K)) (Tr K)) as ST.
  destruct (rthi_gz_pass gh xfl wb bs D O L z Hwb Hwf HD Hx HO Hgh LD LO LV ZC HL)
    as (C & m1 & m2 & S1 & L1 & _ & S2 & L2 & K2 & M2 & OW2 & A2 & _ & HH).
  set (G := gz_ctx gh xfl wb bs O) in *.
  pose proof C as (_ & _ & _ & _ & _ & CL & CB & _).
  destruct ZC as (ZF & ZI & ZA & ZT).
  assert (SRC: dc_src G = O) by reflexivity.
  assert (MH: i_mode (l_s L) = HEAD).
  { destruct HL as [E | (E & _)]; rewrite E; reflexivity. }
  assert (W0: mwf3 (m_init z L O)).
  { apply rti_mwf3_init; [exact LV | exact ZF | | | | ].
    - rewrite ZA. change Int.max_signed with 2147483647. lia.
    - change Int.max_signed with 2147483647. lia.
    - rewrite SRC in CB. exact CB.
    - rewrite MH. discriminate. }
  pose proof (SM Z_FINISH _ W0 eq_refl) as W1. rewrite S1 in W1.
  pose proof (SM Z_FINISH _ W1 L1) as W2. rewrite S2 in W2.
  destruct RUN as (o & LP & RO).
  pose proof (Zlib.proof.roundtrip.RTIGz.rti_loop2_next _ _ _ _
                (Zlib.proof.roundtrip.RTIGz.rti_loop2_next _ _ _ _ LP S1 L1) S2 L2) as LP2.
  assert (IE: O = sublist 0 (0 + Zlength O) (dc_src G)) by (rewrite SRC, Z.add_0_l, sublist_same; auto).
  assert (H0: m_h (Zlib.proof.roundtrip.RTIGz.iout_m o) = m_h m2)
    by exact (Zlib.proof.roundtrip.RTIGz.rtig_loop_h SM ST G 0 O [] Z_FINISH C ltac:(lia)
                ltac:(rewrite SRC; lia) IE m2 o LP2 K2 W2 L2).
  destruct (dc_loop SM ST G 0 O [] Z_FINISH C ltac:(lia) ltac:(rewrite SRC; lia) IE m2 o LP2 K2 W2 L2)
    as (mE & -> & KE & _).
  cbn in H0, RO.
  split.
  - destruct (rthi_leave_mode _ _ _ RO) as [E|E]; [left | right; exact E].
    rewrite E. exact (rthi_kd_mode _ _ _ _ _ KE).
  - intros Hh. destruct (HH Hh) as (g & x & nm & cm & Eg & B & Hm).
    exists g, x, nm, cm. split; [exact Eg|]. split; [exact B|].
    rewrite (rti_leave_h _ _ _ RO), H0. exact Hm.
Qed.

(* RT-I: deflate_roundtrip's inflation of a gzip stream (RTIIface.if_plain's gzip wrapper and
   if_gzhead): the header passes (RTIGzPass.rti_gz_pass), then the generalized decode theory from the TYPE loop
   head (RTIGTheory.rtig_loop_ok), the gz_header fields kept by the rest of the call (RTIHKeep.rti_hkeep). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import compcert.lib.Integers.
Require Import Zlib.proof.roundtrip.RTIKit.
Require Import Zlib.proof.roundtrip.RTIGDefs.
Require Import Zlib.proof.roundtrip.RTIGDecCall.
Require Zlib.proof.roundtrip.RTIGTheory Zlib.proof.roundtrip.RTIHKeep Zlib.proof.roundtrip.RTIGzPass.
Require Zlib.proof.roundtrip.RTIGDecKit Zlib.proof.roundtrip.RTIGDecType Zlib.proof.roundtrip.RTIGDecTab Zlib.proof.roundtrip.RTIGDecDec Zlib.proof.roundtrip.RTIGDecFast Zlib.proof.roundtrip.RTIGDecTrl.
Import ListNotations.
Local Open Scope Z_scope.

Definition iout_m (o: iout) : mst := match o with IBrk m => m | IRet _ m => m end.

Lemma rtig_kd_groups G pos inp ob m : Kd G pos inp ob m ->
  md_type (m_mode m) \/ md_tab (m_mode m) \/ md_dec (m_mode m) \/ md_trl (m_mode m).
Proof.
  intros K. pose proof (kd_at _ _ _ _ _ K) as A.
  destruct (dc_groups _ _ _ _ _ _ A) as [M|M]; [|exact M].
  exfalso. destruct A as [_ D]. unfold md_hdr in M.
  dc_split D; try exact X; unfold m_mode in M; dc_md.
Qed.

(* the loop keeps the gz_header *)
Lemma rtig_loop_h (SM: stepf2_mwf3_stmt) (ST: dc_all) G pos inp ob flush :
  dctx_ok G -> 0 <= pos -> pos + Zlength inp <= Zlength (dc_src G) ->
  inp = sublist pos (pos + Zlength inp) (dc_src G) ->
  forall m o, loop2 flush lenfix_list distfix_list m o -> Kd G pos inp ob m -> mwf3 m -> m_leave m = 0 ->
  m_h (iout_m o) = m_h m.
Proof.
  intros C P0 PL IE m o LP.
  induction LP as [m r m' E | m m' E L1 | m m' o E L1 LP IH]; intros K W L0.
  - pose proof (ST G pos inp ob flush m C P0 PL IE K W L0) as P. rewrite E in P. destruct P.
  - pose proof (Zlib.proof.roundtrip.RTIHKeep.rti_hkeep flush m (rtig_kd_groups _ _ _ _ _ K)) as H.
    rewrite E in H. exact H.
  - pose proof (Zlib.proof.roundtrip.RTIHKeep.rti_hkeep flush m (rtig_kd_groups _ _ _ _ _ K)) as H.
    rewrite E in H.
    pose proof (ST G pos inp ob flush m C P0 PL IE K W L0) as P. rewrite E in P.
    destruct P as (K' & _ & _).
    pose proof (SM flush m W L0) as W'. rewrite E in W'.
    assert (L': m_leave m' = 0) by (pose proof (mw_leave _ (mwf3_mwf _ W')); lia).
    rewrite (IH K' W' L'). exact H.
Qed.

Lemma rti_expand_nil bs : expand [] bs = data [] bs.
Proof.
  unfold data. rewrite Zlength_nil, sublist_same by lia. reflexivity.
Qed.

Lemma rti_init_s_mode : i_mode (init_s 7 0) = HEAD.
Proof. reflexivity. Qed.

Lemma rti_loop2_next flush m m' o : loop2 flush lenfix_list distfix_list m o ->
  stepf2 flush lenfix_list distfix_list m = IBrk m' -> m_leave m' = 0 -> loop2 flush lenfix_list distfix_list m' o.
Proof.
  intros LP E L. inversion LP as [m0 r m1 E1 | m0 m1 E1 L1 | m0 m1 o1 E1 L1 LP1]; subst;
    rewrite E in E1; try discriminate.
  - injection E1 as <-. lia.
  - injection E1 as <-. exact LP1.
Qed.

Lemma rti_gz_run : Zlib.proof.rfc1951.Decode.decode_parts ->
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
  rdone O D res /\
  (forall g x nm cm, i_head (l_s L) = true -> gh = Some g -> head_bufs g x nm cm (l_h L) ->
     head_ok g x nm cm (m_h (r_m res))).
Proof.
  intros DP gh xfl wb bs D O L z res Hwb Hwf HD Hx HO Hgh LD LO LV ZC HL RUN.
  pose proof DP as (_ & T & SM & _).
  pose proof (Zlib.proof.roundtrip.RTIGTheory.rtig_parts_ok) as (K & Ty & Ta & De & Fa & Tr & _).
  pose proof (dc_step (Ty K T) (Ta K T SM (De K (Fa K))) (De K (Fa K)) (Tr K)) as ST.
  destruct (Zlib.proof.roundtrip.RTIGzPass.rti_gz_pass gh xfl wb bs D O L z Hwb Hwf HD Hx HO Hgh LD LO LV ZC HL)
    as (C & m1 & m2 & S1 & L1 & S2 & L2 & K2 & M2 & OW2 & A2 & HH).
  set (G := gz_ctx gh xfl wb bs O) in *.
  pose proof C as (_ & _ & _ & _ & _ & CL & CB & _).
  destruct ZC as (ZF & ZI & ZA & ZT).
  assert (SRC: dc_src G = O) by reflexivity.
  assert (SL: slen G = Zlength O).
  { unfold slen. cbn [dc_w dc_hist dc_bs G gz_ctx]. rewrite HO. reflexivity. }
  assert (FU: full G = D).
  { unfold full. cbn [dc_hist dc_bs G gz_ctx]. rewrite rti_expand_nil. exact HD. }
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
  pose proof (rti_loop2_next _ _ _ _ (rti_loop2_next _ _ _ _ LP S1 L1) S2 L2) as LP2.
  assert (IE: O = sublist 0 (0 + Zlength O) (dc_src G)) by (rewrite SRC, Z.add_0_l, sublist_same; auto).
  assert (H0: m_h (iout_m o) = m_h m2)
    by exact (rtig_loop_h SM ST G 0 O [] Z_FINISH C ltac:(lia) ltac:(rewrite SRC; lia) IE m2 o LP2 K2 W2 L2).
  assert (HR: m_h (r_m res) = m_h m2).
  { destruct o; cbn in H0; try (subst res; exact H0); rewrite (rti_leave_h _ _ _ RO); exact H0. }
  split.
  - destruct (Zlib.proof.roundtrip.RTIGTheory.rtig_loop_ok DP G 0 O [] Z_FINISH m2 o res C ltac:(lia)
                ltac:(rewrite SRC; lia) IE K2 W2 L2 ltac:(exists []; reflexivity) ltac:(constructor) LP2 RO)
      as [R | (R1 & R2 & R3 & R4 & R5 & R6 & R7)]; [left; exact R|].
    right.
    destruct (Z.eq_dec (r_ret res) Z_STREAM_END) as [EE|NE].
    + destruct (R6 EE) as (E1 & E2). rewrite app_nil_l, FU in E1.
      split; [exact EE|]. split; [rewrite SL in E2; lia|]. split; [exact E1|].
      split; [rewrite R3, E1; reflexivity|]. rewrite R4, A2, ZA. reflexivity.
    + exfalso. destruct (R7 NE) as [(_ & X) | [(X1 & X2) | X]].
      * rewrite SL in X. lia.
      * rewrite app_nil_l, FU in X2. rewrite X1, A2, ZA in X2. lia.
      * unfold Z_FINISH, Z_BLOCK, Z_TREES in X. lia.
  - intros g x nm cm Hh Eg HB. rewrite HR. exact (HH g x nm cm Hh Eg HB).
Qed.

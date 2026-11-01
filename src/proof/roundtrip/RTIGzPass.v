(* RT-I, part rti_gz_pass: the gzip header of deflate_roundtrip's stream, in its one inflate() call
   (Z_FINISH, all of O offered).  inflateInit2(32) (wrap 7, wbits 0), optionally inflateGetHeader (i_head, the
   gz_header with buffers of exactly the fields' sizes, done = 0); the stream O = Format's gzip member with the
   header RTFinal.fhdr_of gh xfl (any FTEXT, MTIME, OS, extra field, name, comment, FHCRC).  Two passes of the
   switch: HEAD (the gzip magic: wbits := 15, check := CRC of 1f 8b, FLAGS) and FLAGS falling through TIME, OS,
   EXLEN, EXTRA, NAME, COMMENT, HCRC to TYPE; at that loop head the generalized decode invariant RTIGDefs.Kd
   holds for the context gz_ctx (dc_iw = 32 + wb: same wrap 7, stored
   by inflateInit2(32) with bit 3 as 15 since fix F8), and with a gz_header its fields are reported. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.roundtrip.RTIKit.
Require Import Zlib.proof.roundtrip.RTIGDefs.
Require Import Zlib.proof.roundtrip.RTIGzPassDefs.
Require Zlib.proof.roundtrip.RTIGzPassHF Zlib.proof.roundtrip.RTIGzPassEx Zlib.proof.roundtrip.RTIGzPassNC Zlib.proof.roundtrip.RTIGzPassHc Zlib.proof.roundtrip.RTIGzPassKd Zlib.proof.roundtrip.RTIGzPassCtx.
Import ListNotations.
Local Open Scope Z_scope.

Lemma rti_gz_pass : forall gh xfl wb bs D O L z,
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
    stepf2 Z_FINISH lenfix_list distfix_list m1 = IBrk m2 /\ m_leave m2 = 0 /\
    Kd G 0 O [] m2 /\ m_mode m2 = Zlib.proof.inflate.Model.TYPE /\ m_ow m2 = [] /\ m_aout m2 = zf_ao z /\
    (forall g x nm cm, i_head (l_s L) = true -> gh = Some g -> head_bufs g x nm cm (l_h L) ->
       head_ok g x nm cm (m_h m2)).
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
  split; [rewrite E1, ET, EO, EE, EX, EN, EC, EH; exact E2|].
  split; [exact (gm_leave _ _ _ _ _ _ M2)|].
  split; [exact (KD gh xfl wb bs O z hd h0 m2 Hwb HO C (proj2 (proj2 (proj2 ZC))) M2 F2 HH2 K2)|].
  split; [exact (gm_mode _ _ _ _ _ _ M2)|].
  split; [exact (gm_ow _ _ _ _ _ _ M2)|].
  split; [exact (gm_aout _ _ _ _ _ _ M2)|].
  intros g x nm cm Ehd Eg B.
  destruct (HH2 Ehd) as (g' & x' & nm' & cm' & Eg' & B' & _ & Hm).
  rewrite Eg in Eg'. injection Eg' as <-.
  destruct B as (X1 & N1 & C1 & _). destruct B' as (X2 & N2 & C2 & _).
  rewrite X1 in X2. injection X2 as <-. rewrite N1 in N2. injection N2 as <-. rewrite C1 in C2. injection C2 as <-.
  rewrite Hm. unfold head_ok, gh_at. cbn. repeat split; reflexivity.
Qed.

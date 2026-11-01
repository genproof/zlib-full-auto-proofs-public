(* Law rt_session, sessions with a gzip header: the start of an inflate() call after the gzip header
   ([sgz_canon_init]) and the rest of a call after the header from a loop head where the decode invariant holds on
   the machine with the small header G2IDefs.g2_mc ([sgz_tail]: rt_gzip_header's G2IDec.g2d_tail for any flush, any
   output space and data): the run of the real machine is the same up to the header model, which it keeps
   (RTH8SimKit), and the decode theory RTIGW.rtigw_loop gives the outcome. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.rt_session.SGzDefs.
Require Import Zlib.proof.harness.rt_gzip_header.G2IBridge.
Require Zlib.proof.roundtrip.RTH8SimKit.
Require Zlib.proof.wide.roundtrip.RTIGDecCallOut.
Import ListNotations.
Local Open Scope Z_scope.

Module SK := Zlib.proof.roundtrip.RTH8SimKit.

(* the output so far, a prefix of the data, is bytes *)
Lemma sgz_out_bytes G ob rest : rtigw_ok G -> full G = ob ++ rest -> bytes_ok ob.
Proof.
  intros OK FR. exact (Zlib.proof.wide.roundtrip.RTIGDecCallOut.dco_bytes_ok_wide ob rest G (rtigw_ok_wide G OK) FR).
Qed.

Lemma sgz_tail G pos inp ob flush m o res :
  rtigw_ok G -> 0 <= pos -> pos + Zlength inp <= Zlength (dc_src G) ->
  inp = sublist pos (pos + Zlength inp) (dc_src G) ->
  Kd G pos inp ob (g2_mc m) -> mwf3W (g2_mc m) -> m_leave m = 0 -> SK.hk m ->
  (exists d0, ob = dc_hist G ++ d0) -> (exists rest, full G = ob ++ rest) ->
  loop2 flush lenfix_list distfix_list m o ->
  match o with IRet r m' => res = Res r m' None | IBrk m' => inf_leave flush m' res end ->
  let m' := r_m res in
  r_ret res = Z_MEM_ERROR \/
  ((r_ret res = Z_OK \/ r_ret res = Z_BUF_ERROR \/ r_ret res = Z_STREAM_END) /\
   0 <= m_snx m' <= Zlength inp /\ m_sow m' = Zlength (m_ow m') /\ m_aout m' = m_aout m /\ m_h m' = m_h m /\
   (exists rest, full G = ob ++ m_ow m' ++ rest) /\
   dinv G (pos + m_snx m') (ob ++ m_ow m') (m_s m') (m_tout m') /\
   (r_ret res = Z_STREAM_END -> ob ++ m_ow m' = full G /\ pos + m_snx m' = slen G)).
Proof.
  intros OK P0 PL IE K W L0 HK HP (rest0 & FR0) LP RO.
  destruct (SK.hs_loop flush lenfix_list distfix_list m g2_hc o HK LP) as [LP' HO].
  assert (RO': match SK.out_hk o g2_hc with
               | IRet r m' => SK.rh g2_hc res = Res r m' None
               | IBrk m' => inf_leave flush m' (SK.rh g2_hc res) end /\ m_h (r_m res) = m_h m).
  { destruct o as [m1|r m1]; cbn [SK.out_hk].
    - destruct HO as [H1 H2]. destruct (SK.hs_leave flush m1 g2_hc res H2 RO) as (A & B & _).
      split; [exact A | congruence].
    - subst res. destruct HO as [H1 _]. split; [reflexivity | exact H1]. }
  destruct RO' as [RO' HH].
  destruct (rtigw_loop G pos inp ob flush (g2_mc m) (SK.out_hk o g2_hc) (SK.rh g2_hc res) OK P0 PL IE K W L0
              HP (sgz_out_bytes G ob rest0 OK FR0) LP' RO')
    as [MEM | (RC & SNX & SOW & AO & FR & DV & EN & _)].
  { left. exact MEM. }
  right. cbn zeta. unfold SK.rh, SK.mh, g2_mc in *. cbn [r_ret r_m] in *.
  cbn [m_snx m_sow m_ow m_aout m_s m_tout set_m_h] in *.
  repeat (split; [eassumption|]). exact EN.
Qed.

(* a call that starts after the header, with any output so far: RTIGW.rtigw_init on the live part whose header is the
   small one (G2IBridge.g2_canon_init for any output) *)
Lemma sgz_canon_init G pos out L z inp :
  rtigw_ok G -> dinv G pos out (l_s L) (zf_tout z) -> live_ok8 L -> zf_ok z ->
  zf_ao z <= 4294967295 -> Zlength inp <= 4294967295 -> bytes_ok inp ->
  Kd G pos inp out (g2_mc (m_init z L inp)) /\ mwf3W (g2_mc (m_init z L inp)).
Proof.
  intros Hok Hd Hl Hz Hao Hinp Hb.
  set (L' := set_l_head L g2_hc (l_headp L) (l_hsh L) (l_xb L) (l_nb L) (l_cb L)).
  assert (E : g2_mc (m_init z L inp) = m_init z L' inp) by reflexivity.
  rewrite E. eapply rtigw_init; [exact Hok | exact Hd | | exact Hz | lia | lia | exact Hb].
  destruct Hl as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
  unfold live_ok; cbn [L' set_l_head l_sp l_s l_h l_hsh l_xb l_nb l_cb].
  split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact g2_hc_hwf|].
  split; [exact A5|]. split; [exact A6|]. split; [exact A7|]. split; [|exact A9].
  intros _. split; [|split]; intros X; discriminate X.
Qed.

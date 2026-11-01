(* Law rfc_stored: the theory, the facts main needs (RSFacts.rs_facts) for an invariant of the inflate loop.

   The invariant: the buffer is the canonical stream's source up to the padding (RSCanon.rs_pad_rel), the
   canonical context is a valid stream of the data with inflateInit2's window (Decode7Step.dctx_ok7a), and
   the stream between calls is where the decode theory says (dinv).  A call: RSSim.rs_sim_call turns the
   call on the buffer into the call on the canonical source, Decode7Step's decode_call7a_stmt says what it
   returns and writes. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.rfc1951.Decode7Step.
Require Import Zlib.proof.harness.rfc_stored.RSCanon Zlib.proof.harness.rfc_stored.RSSim.
Require Export Zlib.proof.harness.rfc_stored.RSFacts.
Require Zlib.proof.uncompr.URunFrame.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* The harness's padding bytes                                                                    *)

Lemma rst_bpos_len p lens : Zlength (rs_bpos p lens) = Zlength lens.
Proof.
  revert p. induction lens as [|l r IH]; intros p; [reflexivity|].
  cbn [rs_bpos]. rewrite !Zlength_cons, IH. reflexivity.
Qed.

(* one per block, and bytes (s0's) *)
Lemma rst_pads wr s0 lens : rs_bytes s0 ->
  Zlength (rs_pads wr s0 lens) = Zlength lens /\ rs_bytes (rs_pads wr s0 lens).
Proof.
  intros B. unfold rs_pads. split; [rewrite Zlength_map; apply rst_bpos_len|].
  unfold rs_bytes. apply Forall_forall. intros x Hx. apply in_map_iff in Hx. destruct Hx as (p & <- & _).
  destruct (zlt p 0); [rewrite Znth_underflow by lia; unfold byte_ok, Inhabitant_Z; lia|].
  destruct (zlt p (Zlength s0)); [unfold rs_bytes in B; rewrite Forall_forall in B; apply B, Znth_In; lia|].
  rewrite Znth_overflow by lia. unfold byte_ok, Inhabitant_Z. lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* A call on the canonical source: the machine's output stays within its output space            *)

(* inf_leave keeps the output and the output space *)
Lemma rst_leave flush m res : inf_leave flush m res ->
  m_ow (r_m res) = m_ow m /\ m_aout (r_m res) = m_aout m.
Proof.
  intros [_ _|]; [split; reflexivity|].
  unfold leave_fin. cbv zeta.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end; split; reflexivity.
Qed.

(* from a loop head with Kd, the loop never returns from inside the switch and keeps mwf3W *)
Lemma rst_loop (S: dc_step7a_stmt) (W: stepf2_mwf3W_stmt) G pos inp ob flush :
  dctx_ok7a G -> 0 <= pos -> pos + Zlength inp <= Zlength (dc_src G) ->
  inp = sublist pos (pos + Zlength inp) (dc_src G) ->
  forall m o, loop2 flush lenfix_list distfix_list m o -> Kd G pos inp ob m -> mwf3W m -> m_leave m = 0 ->
  exists m', o = IBrk m' /\ mwf3W m'.
Proof.
  intros OK P0 PL PI m o LP.
  induction LP as [m r m' E | m m' E L1 | m m' o E L1 LP IH]; intros K M L0.
  - pose proof (S G pos inp ob flush m OK P0 PL PI K M L0) as D. rewrite E in D. destruct D.
  - pose proof (W flush m M L0) as M'. rewrite E in M'. eauto.
  - pose proof (S G pos inp ob flush m OK P0 PL PI K M L0) as D. rewrite E in D. destruct D as (K' & _ & _).
    pose proof (W flush m M L0) as M'. rewrite E in M'.
    apply IH; auto. pose proof (mwW_leave _ (proj1 M')). lia.
Qed.

Lemma rst_run_ow (S: dc_step7a_stmt) (W: stepf2_mwf3W_stmt) G pos inp ob flush m0 res :
  dctx_ok7a G -> 0 <= pos -> pos + Zlength inp <= Zlength (dc_src G) ->
  inp = sublist pos (pos + Zlength inp) (dc_src G) ->
  Kd G pos inp ob m0 -> mwf3W m0 -> m_leave m0 = 0 ->
  run2 flush lenfix_list distfix_list m0 res -> Zlength (m_ow (r_m res)) <= m_aout (r_m res).
Proof.
  intros OK P0 PL PI K M L0 (o & LP & R).
  destruct (rst_loop S W G pos inp ob flush OK P0 PL PI m0 o LP K M L0) as (mE & -> & ME).
  destruct (rst_leave flush mE res R) as [-> ->]. apply (mwW_ow _ (proj1 ME)).
Qed.

(* the modes of the decode theory's positions are inflate()'s valid modes *)
Lemma rst_vmode G s c h b out : at_mode G s c h b out -> URunFrame.vmode (i_mode s).
Proof.
  intros [_ A]. unfold URunFrame.vmode.
  decompose [or and] A; match goal with E: i_mode s = _ |- _ => rewrite E end;
  cbv [HEAD FLAGS TIME OS Zlib.proof.inflate.Model.TYPE TYPEDO STORED COPY_ COPY TABLE LENLENS CODELENS LEN_
       LEN LENEXT DIST DISTEXT MATCH LIT CHECK LENGTH DONE BAD]; lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The invariant                                                                                  *)

(* src is the canonical context's source up to the padding, the context a valid stream of the data d (bytes),
   the stream (z, L) at pos with the output out by the decode theory, out a prefix of d *)
Definition rs_inv (src d: list Z) (pos: Z) (out: list Z) (z: zfields) (L: live) : Prop :=
  exists G, dctx_ok7a G /\ rs_stored_only G /\ rs_pad_rel G src /\ full G = d /\ bytes_ok d /\
    dinv G pos out (l_s L) (zf_tout z) /\ 0 <= pos <= Zlength src /\ (exists rest, d = out ++ rest).

(* after inflateInit2_: the canonical context of the harness's choices *)
Lemma rst_init (DI: decode_init7a_stmt) wr window c s0 lens d sp z :
  rs_ok wr window c s0 lens d -> Zlength s0 <= Ptrofs.max_unsigned -> zf_tout z = 0 ->
  rs_inv (rs_src wr c s0 (rs_pads wr s0 lens) lens d) d 0 [] z (init_live sp (rs_iw wr window)).
Proof.
  intros OK S0 TOUT.
  pose proof (rs_canon wr window c s0 lens d OK) as C. cbv zeta in C.
  set (G := rs_ctx wr window c s0 lens d) in C.
  destruct C as (SO & ST & GZ & SL & LS & BS & PFX & FULL & NB & RAW & ZL & GZW & PAD).
  pose proof OK as (Hwr & Hwin & _ & _ & _ & _ & Hsl & Bs0 & Bd).
  assert (HH : dc_hist G = []) by reflexivity.
  assert (WR : wr = 0 \/ wr = 1 \/ wr = 2) by lia.
  assert (DID : forall wb fl did, dc_w G = WZlib wb fl did -> did = None).
  { intros wb fl did E. destruct WR as [W|[W|W]].
    - destruct (RAW W) as [Ew _]. rewrite Ew in E. discriminate.
    - destruct (ZL W) as ([fl' Ew] & _). rewrite Ew in E. injection E as _ _ <-. reflexivity.
    - destruct (GZW W) as ([h Ew] & _). rewrite Ew in E. discriminate. }
  assert (OKG : dctx_ok7a G).
  { unfold dctx_ok7a. rewrite HH. split; [exact SO|]. split.
    { destruct WR as [W|[W|W]].
      - left. unfold accepts. destruct (RAW W) as [Ew Ei]. rewrite Ew. exact Ei.
      - right. destruct (ZL W) as ([fl Ew] & Ei & Eb). exists (dc_wb G), fl, None.
        split; [exact Ew|]. rewrite Ei. lia.
      - left. unfold accepts. destruct (GZW W) as ([h Ew] & Ei). rewrite Ew. left. exact Ei. }
    split; [exact GZ|]. split; [intros wb fl did E; left; exact (DID wb fl did E)|].
    rewrite SL, LS. split; [exact Hsl|].
    split; [change Ptrofs.max_unsigned with (2 ^ 64 - 1) in S0; lia|].
    split; [exact BS|]. rewrite <- SL. exact PFX. }
  destruct (rst_pads wr s0 lens Bs0) as [PL PB].
  exists G. split; [exact OKG|]. split; [exact ST|]. split; [exact (PAD _ PL PB)|].
  split; [exact FULL|]. split; [apply rsc_bytes_ok, Bd|].
  split.
  { rewrite TOUT. exact (DI G sp OKG HH DID). }
  split; [split; [lia | apply Zlength_nonneg]|].
  exists d. reflexivity.
Qed.

Theorem rs_theory : decode7a_stmt -> rs_theory_stmt.
Proof.
  intros (DI & DC & KI & ST & SW). exists rs_inv. constructor.
  - intros wr window c s0 lens d sp z OK S0 _ _ _ TOUT _. exact (rst_init DI wr window c s0 lens d sp z OK S0 TOUT).
  - intros src d pos out z L (G & _ & _ & _ & _ & _ & (_ & (_ & HD & _) & _) & POS & PFX).
    split; [exact POS|]. split; [exact PFX | exact HD].
  - intros src d pos out z L strmp flush ib o ain aout r z' st' ow
      (G & OKG & SO & PR & FULL & BD & DIv & POS & PFX) LOK ZOK SNN AIN PAIN AOUT OUTD FL IBN REL.
    destruct REL as [(BAD & _) | (_ & L1 & o1 & res & winp & EL & EO & RUN & SNX & ER & EOW & EZ & EW & ES)].
    { exfalso. unfold inflate_bad, is_live in BAD. destruct (eq_dec strmp nullval) as [E|_]; [contradiction|].
      destruct BAD as [E|[E|[E _]]]; [discriminate | discriminate | contradiction]. }
    injection EL as <-. injection EO as <-.
    eexists; split; [exact ES|]. intros NM.
    set (z0 := rs_set_call z (in_ptr ib 0) ain (out_ptr o 0) aout) in *.
    set (inp := sublist pos (pos + ain) src) in *.
    pose proof PR as (PRL & _).
    assert (LI : Zlength inp = ain) by (unfold inp; rewrite Zlength_sublist by lia; lia).
    assert (ZOK0 : zf_ok z0).
    { destruct ZOK as (A & B & C & D & E & F). unfold z0, rs_set_call. repeat split; cbn; rep_lia. }
    assert (A0 : zf_ao z0 <= 2 ^ 32 - 1) by (cbn; change Int.max_unsigned with (2 ^ 32 - 1) in AOUT; lia).
    assert (I0 : Zlength inp <= 2 ^ 32 - 1) by (change Int.max_unsigned with (2 ^ 32 - 1) in AIN; lia).
    assert (IP : inp = sublist pos (pos + Zlength inp) src) by (rewrite LI; reflexivity).
    pose proof (rs_sim_call KI ST SW G src pos out L z0 inp flush res OKG SO PR DIv LOK ZOK0 A0 I0
                  (proj1 POS) ltac:(lia) IP RUN) as SIM.
    cbv zeta in SIM. set (inp' := sublist pos (pos + Zlength inp) (dc_src G)) in SIM.
    assert (LI' : Zlength inp' = Zlength inp) by (unfold inp'; rewrite Zlength_sublist by lia; lia).
    assert (IP' : inp' = sublist pos (pos + Zlength inp') (dc_src G)) by (rewrite LI'; reflexivity).
    assert (BI' : bytes_ok inp') by (unfold inp'; apply Forall_sublist; apply OKG).
    destruct (KI G pos out L z0 inp' OKG DIv LOK ZOK0 A0 ltac:(lia) BI') as [K0 M0].
    (* the canonical call: what it returns and writes *)
    pose proof (DC G pos out L z0 inp' flush _ OKG DIv LOK ZOK0 A0 ltac:(lia) (proj1 POS) ltac:(lia) IP' SIM)
      as D. cbv zeta in D. cbn [r_ret r_m] in D.
    pose proof (rst_run_ow ST SW G pos inp' out flush _ _ OKG (proj1 POS) ltac:(lia) IP' K0 M0
                  eq_refl SIM) as OWB. cbn [r_m] in OWB.
    (* the real call keeps its input *)
    assert (V : URunFrame.vmode (i_mode (m_s (m_init z0 L inp)))) by exact (rst_vmode _ _ _ _ _ _ (kd_at _ _ _ _ _ K0)).
    destruct (URunFrame.run2_frame _ _ _ _ _ V RUN) as (FI & FA & FS & _).
    cbn [m_init m_aout m_inp] in FA, FI.
    destruct D as [M | (R & SNX' & SOW & AOUT' & (rest & FG) & DI' & _ & END & _ & _)].
    { subst r. contradiction. }
    cbn [set_m_inp m_snx m_sow m_ow m_aout m_s m_tout] in SNX', SOW, AOUT', FG, DI', END, OWB.
    subst z' ow r.
    unfold rs_post, z_after. cbv zeta. cbn [zf_ai zf_ao zf_ni zf_no zf_tout l_s].
    rewrite FI, LI. rewrite FA in OWB.
    replace (ain - (ain - m_snx (r_m res))) with (m_snx (r_m res)) by lia.
    assert (BOW : bytes_ok (m_ow (r_m res))).
    { rewrite <- FULL, FG in BD. apply Forall_app in BD. destruct BD as [_ BD]. apply Forall_app in BD. apply BD. }
    split; [exact R|]. split; [lia|]. split; [cbn in OWB; lia|]. split; [rewrite FA, FS; reflexivity|].
    split; [reflexivity|]. split; [rewrite FS; reflexivity|]. split; [exact BOW|].
    split; [exists rest; rewrite <- FULL; exact FG|].
    split; [intros E; rewrite <- FULL; apply (END E)|].
    exists G. split; [exact OKG|]. split; [exact SO|]. split; [exact PR|]. split; [exact FULL|].
    split; [exact BD|]. split; [exact DI'|]. split; [lia|].
    exists rest. rewrite <- app_assoc, <- FULL. exact FG.
Qed.

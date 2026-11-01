(* Law rfc_stored: inflate() on the harness's stream does what it does on Format's canonical stream.

   The two inputs differ only in the high five bits of each stored block's first byte (RSCanon.rs_pad_rel).
   inflate() reads that byte only in TYPEDO, with an empty bit buffer (a stored stream is byte-aligned at a
   block boundary): it takes BFINAL and BTYPE from the three low bits, DROPBITS(3) leaves the padding in hold
   with bits = 5, and STORED, the very next pass of the same call, starts with BYTEBITS, which drops it.  So,
   pass by pass, the machine on the real input is the machine on the canonical input but for the input bytes
   (m_inp) and, between those two passes, hold; the call's result is the same but for m_inp.  The canonical
   machine's place in the stream (the decode theory's Kd at each loop head, Decode7Step's kd_init7a_stmt /
   dc_step7a_stmt) tells which byte each pass reads.

   The passes group by group: RSSimHdr (header), RSSimTy (TYPE / TYPEDO, where hold may differ), RSSimSt
   (STORED, COPY), RSSimTrl (trailer), over the layout of stored blocks (RSSimLay) and the input kit (RSSimKit).
   Here: no other mode occurs, STORED ignores the padding left in hold, the loop by induction, and the exit
   (inf_leave reads only the input's length). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.rfc1951.Decode7Step.
Require Import Zlib.proof.harness.rfc_stored.RSCanon.
Require Import Zlib.proof.harness.rfc_stored.RSSimKit.
Require Import Zlib.proof.harness.rfc_stored.RSSimLay.
Require Import Zlib.proof.harness.rfc_stored.RSSimHdr.
Require Import Zlib.proof.harness.rfc_stored.RSSimSt.
Require Import Zlib.proof.harness.rfc_stored.RSSimTrl.
Require Import Zlib.proof.harness.rfc_stored.RSSimTy.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* The modes of a stream of stored blocks                                                         *)

Lemma rs_dyn_bad (LY: rs_lay_stmt) G s k b : rs_stored_only G -> in_blk G s k -> blk G k = b ->
  (forall l, b <> Stored l) -> False.
Proof.
  intros S [Hk _] E N. destruct (rl_stored LY G k S Hk) as [l El]. rewrite El in E. exact (N l (eq_sym E)).
Qed.

Lemma rs_huff_bad (LY: rs_lay_stmt) G s k j ll dl syms p0 : rs_stored_only G ->
  in_huff G s k j ll dl syms p0 -> False.
Proof.
  intros S (IB & [(E & _)|(a & b & c & d & E & _)] & _);
    (eapply rs_dyn_bad; [exact LY|exact S|exact IB|exact E|intros l; discriminate]).
Qed.

(* at a loop head of a stored stream the mode is a header, TYPE/TYPEDO, stored or trailer one *)
Lemma rs_mode_cases (LY: rs_lay_stmt) G pos inp ob m : rs_stored_only G -> Kd G pos inp ob m ->
  md_hdr (m_mode m) \/ (m_mode m = Zlib.proof.inflate.Model.TYPE \/ m_mode m = TYPEDO) \/
  (m_mode m = STORED \/ m_mode m = COPY_ \/ m_mode m = COPY) \/ md_trl (m_mode m).
Proof.
  intros S K. destruct (kd_at _ _ _ _ _ K) as [_ A]. unfold m_mode, md_hdr, md_trl.
  destruct A as [[E A]|[[E A]|[[E A]|[[E A]|[[E A]|[[E A]|[[E A]|[[E A]|[[E A]|[[E A]|[[E A]|[[E A]|[[E A]|[[E A]|[[E A]|[[E A]|[E A]]]]]]]]]]]]]]]]].
  - left. auto.
  - left. destruct E as [E|[E|E]]; auto.
  - right; left. exact E.
  - right; right; left. auto.
  - right; right; left. destruct E; auto.
  - exfalso. destruct A as (k & a1 & a2 & a3 & a4 & a5 & IB & EB & _).
    eapply rs_dyn_bad; [exact LY|exact S|exact IB|exact EB|intros l; discriminate].
  - exfalso. destruct A as (k & a1 & a2 & a3 & a4 & a5 & IB & EB & _).
    eapply rs_dyn_bad; [exact LY|exact S|exact IB|exact EB|intros l; discriminate].
  - exfalso. destruct A as (k & a1 & a2 & a3 & a4 & a5 & a6 & IB & EB & _).
    eapply rs_dyn_bad; [exact LY|exact S|exact IB|exact EB|intros l; discriminate].
  - exfalso. destruct A as (k & j & ll & dl & syms & p0 & H & _). exact (rs_huff_bad LY G _ _ _ _ _ _ _ S H).
  - exfalso. destruct A as (k & j & ll & dl & syms & p0 & a1 & a2 & H & _). exact (rs_huff_bad LY G _ _ _ _ _ _ _ S H).
  - exfalso. destruct A as (k & j & ll & dl & syms & p0 & a1 & a2 & H & _). exact (rs_huff_bad LY G _ _ _ _ _ _ _ S H).
  - exfalso. destruct A as (k & j & ll & dl & syms & p0 & a1 & a2 & H & _). exact (rs_huff_bad LY G _ _ _ _ _ _ _ S H).
  - exfalso. destruct A as (k & j & ll & dl & syms & p0 & a1 & a2 & H & _). exact (rs_huff_bad LY G _ _ _ _ _ _ _ S H).
  - exfalso. destruct A as (k & j & ll & dl & syms & p0 & a1 & H & _). exact (rs_huff_bad LY G _ _ _ _ _ _ _ S H).
  - right; right; right. auto.
  - right; right; right. auto.
  - right; right; right. auto.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* STORED starts with BYTEBITS: the bits above the byte boundary of hold do not matter            *)

Lemma rs_bytebits_hold m h : Z.shiftr h (m_bits m mod 8) = Z.shiftr (m_hold m) (m_bits m mod 8) ->
  bytebits (set_m_hold m h) = bytebits m.
Proof. intros E. destruct m; unfold bytebits; cbn in *. rewrite E. reflexivity. Qed.

Lemma rs_stored_hold flush fx dx m h : m_mode m = STORED ->
  Z.shiftr h (m_bits m mod 8) = Z.shiftr (m_hold m) (m_bits m mod 8) ->
  stepf2 flush fx dx (set_m_hold m h) = stepf2 flush fx dx m.
Proof.
  intros Md E.
  assert (S : forall m0, m_mode m0 = STORED -> stepf2 flush fx dx m0 = c_STORED flush m0).
  { intros m0 H. unfold stepf2, step2. rewrite H. reflexivity. }
  rewrite (S m Md), S by (destruct m; exact Md).
  unfold c_STORED. rewrite rs_bytebits_hold by exact E. reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* One pass, and the loop                                                                         *)

(* the real machine's hold is the canonical one's, or (just after TYPEDO) it differs only above the bit
   buffer's byte boundary in mode STORED, inside the loop *)
Definition rs_hok (m: mst) (h: Z) : Prop :=
  h = m_hold m \/
  (m_mode m = STORED /\ m_leave m = 0 /\ Z.shiftr h (m_bits m mod 8) = Z.shiftr (m_hold m) (m_bits m mod 8)).

Lemma rs_hold_id m x : set_m_hold (set_m_inp m x) (m_hold m) = set_m_inp m x.
Proof. destruct m; reflexivity. Qed.

Section Sim.
Variables (KI: kd_init7a_stmt) (DS: dc_step7a_stmt) (SM: stepf2_mwf3W_stmt).
Variables (G: dctx) (pos: Z) (x inp' ob: list Z) (flush: Z).
Hypotheses (C: dctx_ok7a G) (S: rs_stored_only G) (P0: 0 <= pos)
           (PL: pos + Zlength inp' <= Zlength (dc_src G)) (IE: inp' = sublist pos (pos + Zlength inp') (dc_src G))
           (XR: rs_xrel G pos x inp').

Let LY := rs_lay.

(* one pass from related machines *)
Lemma rs_pass m' h : Kd G pos inp' ob m' -> mwf3W m' -> m_leave m' = 0 -> rs_hok m' h ->
  exists m1' h1, stepf2 flush lenfix_list distfix_list m' = IBrk m1' /\
    stepf2 flush lenfix_list distfix_list (set_m_hold (set_m_inp m' x) h) = IBrk (set_m_hold (set_m_inp m1' x) h1) /\
    rs_hok m1' h1.
Proof.
  intros K W L0 HK.
  assert (E0 : stepf2 flush lenfix_list distfix_list (set_m_hold (set_m_inp m' x) h) =
               stepf2 flush lenfix_list distfix_list (set_m_inp m' x)).
  { destruct HK as [->|(Md & _ & Sh)]; [rewrite rs_hold_id; reflexivity|].
    apply rs_stored_hold; destruct m'; assumption. }
  rewrite E0. clear E0.
  pose proof (DS G pos inp' ob flush m' C P0 PL IE K W L0) as P.
  destruct (stepf2 flush lenfix_list distfix_list m') as [m1'|r m1'] eqn:E1; [|destruct P].
  assert (Plain : stepf2 flush lenfix_list distfix_list (set_m_inp m' x) = rs_iom x (IBrk m1') ->
                  exists m2' h1, IBrk m1' = IBrk m2' /\
                    stepf2 flush lenfix_list distfix_list (set_m_inp m' x) = IBrk (set_m_hold (set_m_inp m2' x) h1) /\
                    rs_hok m2' h1).
  { intros E. exists m1', (m_hold m1'). split; [reflexivity|]. rewrite rs_hold_id, E.
    split; [reflexivity|left; reflexivity]. }
  destruct (rs_mode_cases LY G pos inp' ob m' S K) as [M|[M|[M|M]]].
  - apply Plain. rewrite <- E1. exact (rs_pass_hdr LY G pos x inp' ob flush m' C S P0 PL IE XR K W L0 M).
  - destruct (rs_pass_type LY DS G pos x inp' ob flush m' C S P0 PL IE XR K W L0 M) as (m2' & h1 & E2 & E3 & H3).
    rewrite E1 in E2. injection E2 as <-. exists m1', h1. auto.
  - apply Plain. rewrite <- E1. exact (rs_pass_st LY G pos x inp' ob flush m' C S P0 PL IE XR K W L0 M).
  - apply Plain. rewrite <- E1. exact (rs_pass_trl LY G pos x inp' ob flush m' C S P0 PL IE XR K W L0 M).
Qed.

(* the loop on the real input ends where the loop on the canonical input ends, but for the input *)
Lemma rs_loop : forall m o, loop2 flush lenfix_list distfix_list m o ->
  forall m' h, m = set_m_hold (set_m_inp m' x) h -> rs_hok m' h ->
    Kd G pos inp' ob m' -> mwf3W m' -> m_leave m' = 0 ->
  exists mE, loop2 flush lenfix_list distfix_list m' (IBrk mE) /\ o = IBrk (set_m_inp mE x) /\ m_inp mE = inp'.
Proof.
  intros m o LP. induction LP as [m r m1 E | m m1 E L1 | m m1 o E L1 LP IH]; intros m' h -> HK K W L0;
    destruct (rs_pass m' h K W L0 HK) as (m1' & h1 & E1 & E2 & H1); rewrite E2 in E; try discriminate E;
    injection E as <-;
    pose proof (DS G pos inp' ob flush m' C P0 PL IE K W L0) as P; rewrite E1 in P;
    destruct P as (K1 & _ & _);
    assert (Lv : m_leave (set_m_hold (set_m_inp m1' x) h1) = m_leave m1') by (destruct m1'; reflexivity).
  - rewrite Lv in L1.
    assert (Eh : h1 = m_hold m1') by (destruct H1 as [?|(_ & L & _)]; [assumption|lia]).
    subst h1. rewrite rs_hold_id. exists m1'. split; [|split; [reflexivity|exact (kd_inp _ _ _ _ _ K1)]].
    apply loop2_leave; assumption.
  - rewrite Lv in L1.
    pose proof (SM flush m' W L0) as W1. rewrite E1 in W1.
    assert (L1' : m_leave m1' = 0) by (pose proof (mwW_leave _ (proj1 W1)); lia).
    destruct (IH m1' h1 eq_refl H1 K1 W1 L1') as (mE & LE & -> & IEq).
    exists mE. split; [|split; [reflexivity|exact IEq]].
    apply loop2_next with m1'; [exact E1|lia|exact LE].
Qed.

End Sim.

(* ---------------------------------------------------------------------------------------------- *)
(* The exit: inf_leave does not read the input (only its length)                                 *)

Lemma rs_leave_ok_inp flush m x : leave_ok flush (set_m_inp m x) = leave_ok flush m.
Proof. destruct m; reflexivity. Qed.

Section Commute.
Variable (x: list Z).
Lemma rs_c_restore m : restore (set_m_inp m x) = set_m_inp (restore m) x.
Proof. destruct m; reflexivity. Qed.
Lemma rs_c_upds m f : upd_s (set_m_inp m x) f = set_m_inp (upd_s m f) x.
Proof. destruct m; reflexivity. Qed.
Lemma rs_c_tin m v : set_m_tin (set_m_inp m x) v = set_m_inp (set_m_tin m v) x.
Proof. destruct m; reflexivity. Qed.
Lemma rs_c_tout m v : set_m_tout (set_m_inp m x) v = set_m_inp (set_m_tout m v) x.
Proof. destruct m; reflexivity. Qed.
Lemma rs_c_adler m v : set_m_adler (set_m_inp m x) v = set_m_inp (set_m_adler m v) x.
Proof. destruct m; reflexivity. Qed.
Lemma rs_g_s m : m_s (set_m_inp m x) = m_s m. Proof. reflexivity. Qed.
Lemma rs_g_ow m : m_ow (set_m_inp m x) = m_ow m. Proof. reflexivity. Qed.
Lemma rs_g_out m : m_out (set_m_inp m x) = m_out m. Proof. reflexivity. Qed.
Lemma rs_g_left m : m_left (set_m_inp m x) = m_left m. Proof. reflexivity. Qed.
Lemma rs_g_in m : m_in (set_m_inp m x) = m_in m. Proof. reflexivity. Qed.
Lemma rs_g_tin m : m_tin (set_m_inp m x) = m_tin m. Proof. reflexivity. Qed.
Lemma rs_g_tout m : m_tout (set_m_inp m x) = m_tout m. Proof. reflexivity. Qed.
Lemma rs_g_bits m : m_bits (set_m_inp m x) = m_bits m. Proof. reflexivity. Qed.
Lemma rs_g_ret m : m_ret (set_m_inp m x) = m_ret m. Proof. reflexivity. Qed.
Lemma rs_g_inp m : m_inp (set_m_inp m x) = x. Proof. reflexivity. Qed.
End Commute.

Lemma rs_if_inp (b: bool) a c x : (if b then set_m_inp a x else set_m_inp c x) = set_m_inp (if b then a else c) x.
Proof. destruct b; reflexivity. Qed.

(* leave_fin after the window update: the counters, the check value, data_type and the return code *)
Definition rs_post (flush: Z) (m: mst) : result :=
  let inn := u32 (m_in m - m_have m) in
  let out := u32 (m_out m - m_left m) in
  let m := set_m_tout (set_m_tin m (u64 (m_tin m + inn))) (u64 (m_tout m + out)) in
  let m := upd_s m (fun s => set_i_total s (u64 (i_total s + out))) in
  let m := if negb (Z.land (i_wrap (m_s m)) 4 =? 0) && negb (out =? 0) then
             let c := update_check (i_flags (m_s m)) (i_check (m_s m))
                        (sublist (Zlength (m_ow m) - out) (Zlength (m_ow m)) (m_ow m)) in
             set_m_adler (upd_s m (fun s => set_i_check s c)) c
           else m in
  let s := m_s m in
  let dt := m_bits m + (if i_last s =? 0 then 0 else 64) + (if i_mode s =? Zlib.proof.inflate.Model.TYPE then 128 else 0)
            + (if (i_mode s =? LEN_) || (i_mode s =? COPY_) then 256 else 0) in
  let r := if (((inn =? 0) && (out =? 0)) || (flush =? Z_FINISH)) && (m_ret m =? Z_OK)
           then Z_BUF_ERROR else m_ret m in
  Res r m (Some dt).

(* the window update *)
Definition rs_win (m: mst) : mst :=
  let copy := u32 (m_out m - m_left m) in
  upd_s m (fun s => set_i_win (updatewindow s (sublist (Zlength (m_ow m) - copy) (Zlength (m_ow m)) (m_ow m))) true).

Lemma rs_leave_fin_eq flush m :
  leave_fin flush m = rs_post flush (if leave_ok flush m then rs_win (restore m) else restore m).
Proof. reflexivity. Qed.

Lemma rs_win_inp m x : rs_win (set_m_inp m x) = set_m_inp (rs_win m) x.
Proof. destruct m; reflexivity. Qed.

Lemma rs_post_inp flush m x : Zlength x = Zlength (m_inp m) ->
  rs_post flush (set_m_inp m x) =
  Res (r_ret (rs_post flush m)) (set_m_inp (r_m (rs_post flush m)) x) (r_dtype (rs_post flush m)).
Proof.
  intros Hl. unfold rs_post. cbv zeta.
  assert (Hv : m_have (set_m_inp m x) = m_have m) by (unfold m_have; rewrite rs_g_inp, Hl; reflexivity).
  rewrite Hv, ?rs_g_in, ?rs_g_out, ?rs_g_left, ?rs_g_tin, ?rs_g_tout, ?rs_c_tin, ?rs_c_tout, ?rs_c_upds,
    ?rs_g_s, ?rs_g_ow, ?rs_c_adler, ?rs_c_upds, ?rs_g_s, ?rs_if_inp, ?rs_g_s, ?rs_g_bits, ?rs_g_ret.
  reflexivity.
Qed.

Lemma rs_leave_fin_inp flush m x : Zlength x = Zlength (m_inp m) ->
  leave_fin flush (set_m_inp m x) =
  Res (r_ret (leave_fin flush m)) (set_m_inp (r_m (leave_fin flush m)) x) (r_dtype (leave_fin flush m)).
Proof.
  intros Hl. rewrite !rs_leave_fin_eq, rs_leave_ok_inp, rs_c_restore, rs_win_inp, rs_if_inp.
  apply rs_post_inp. destruct (leave_ok flush m); destruct m; exact Hl.
Qed.

Lemma rs_leave_fin_back flush m x : Zlength x = Zlength (m_inp m) ->
  Res (r_ret (leave_fin flush (set_m_inp m x))) (set_m_inp (r_m (leave_fin flush (set_m_inp m x))) (m_inp m))
      (r_dtype (leave_fin flush (set_m_inp m x))) = leave_fin flush m.
Proof.
  intros Hl.
  pose proof (rs_leave_fin_inp flush m x Hl) as E1.
  pose proof (rs_leave_fin_inp flush m (m_inp m) eq_refl) as E0. rewrite rs_inp_id in E0.
  (* keep leave_fin folded: the kernel would otherwise unfold it to compare the two sides *)
  revert E0 E1. generalize (leave_fin flush (set_m_inp m x)) as R'. generalize (leave_fin flush m) as R.
  intros R R' E0 ->. cbn [r_ret r_m r_dtype]. rewrite rs_inp_inp. symmetry. exact E0.
Qed.

Lemma rs_inf_leave flush m x y res : Zlength x = Zlength (m_inp m) -> m_inp m = y ->
  inf_leave flush (set_m_inp m x) res ->
  inf_leave flush m (Res (r_ret res) (set_m_inp (r_m res) y) (r_dtype res)).
Proof.
  intros Hl Hy IL. subst y. destruct IL as [Lk Wn|].
  - cbn [r_ret r_m r_dtype]. rewrite rs_leave_ok_inp in Lk.
    replace (set_m_inp (set_mode (restore (set_m_inp m x)) MEM) (m_inp m)) with (set_mode (restore m) MEM)
      by (destruct m; reflexivity).
    apply il_mem; [exact Lk|destruct m; exact Wn].
  - rewrite (rs_leave_fin_back flush m x Hl). apply il_ok.
Qed.

Lemma rs_sim_call : kd_init7a_stmt -> dc_step7a_stmt -> stepf2_mwf3W_stmt ->
  forall G src pos out L z inp flush res,
    dctx_ok7a G -> rs_stored_only G -> rs_pad_rel G src ->
    dinv G pos out (l_s L) (zf_tout z) -> live_ok L -> zf_ok z ->
    zf_ao z <= 2 ^ 32 - 1 -> Zlength inp <= 2 ^ 32 - 1 ->
    0 <= pos -> pos + Zlength inp <= Zlength src -> inp = sublist pos (pos + Zlength inp) src ->
    run2 flush lenfix_list distfix_list (m_init z L inp) res ->
    let inp' := sublist pos (pos + Zlength inp) (dc_src G) in
    run2 flush lenfix_list distfix_list (m_init z L inp') (Res (r_ret res) (set_m_inp (r_m res) inp') (r_dtype res)).
Proof.
  intros KI DS SM G src pos out L z inp flush res C S PR D LO ZO AO IL P0 PL Einp RUN inp'.
  pose proof C as (_ & _ & _ & _ & _ & _ & BS & _).
  destruct PR as (Hsrc & BX & PR).
  assert (Hn : 0 <= Zlength inp) by apply Zlength_nonneg.
  assert (Hl : Zlength inp' = Zlength inp) by (unfold inp'; rewrite Zlength_sublist by lia; lia).
  assert (PL' : pos + Zlength inp' <= Zlength (dc_src G)) by lia.
  assert (IE' : inp' = sublist pos (pos + Zlength inp') (dc_src G)) by (rewrite Hl; reflexivity).
  assert (BI : bytes_ok inp') by (unfold inp', bytes_ok in *; apply Forall_sublist; exact BS).
  assert (XR : rs_xrel G pos inp inp').
  { split; [lia|]. split.
    - rewrite Einp. unfold bytes_ok in *. apply Forall_sublist. exact BX.
    - intros i Hi.
      assert (E1 : Znth i inp = Znth (pos + i) src).
      { rewrite Einp at 1. rewrite Znth_sublist by lia. f_equal; lia. }
      assert (E2 : Znth i inp' = Znth (pos + i) (dc_src G)).
      { unfold inp'. rewrite Znth_sublist by lia. f_equal; lia. }
      rewrite E1, E2. destruct (PR (pos + i) ltac:(lia)) as [A|(k & K1 & K2 & K3 & K4)]; [left; exact A|].
      right. split; [exists k; auto|auto]. }
  destruct (KI G pos out L z inp' C D LO ZO AO ltac:(lia) BI) as [K0 W0].
  assert (E0 : m_init z L inp = set_m_hold (set_m_inp (m_init z L inp') inp) (m_hold (m_init z L inp'))).
  { rewrite rs_hold_id. unfold m_init. cbv zeta. rewrite Hl. reflexivity. }
  destruct RUN as (o & LP & RO).
  destruct (rs_loop DS SM G pos inp inp' out flush C S P0 PL' IE' XR _ _ LP _ _ E0 (or_introl eq_refl) K0 W0
              eq_refl) as (mE & LE & -> & IEq).
  exists (IBrk mE). split; [exact LE|].
  apply rs_inf_leave with inp; [rewrite IEq; lia|exact IEq|exact RO].
Qed.


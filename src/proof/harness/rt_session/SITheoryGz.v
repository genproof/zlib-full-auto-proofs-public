(* Law rt_session: the inflate side's facts for the sessions with a gzip header given to inflateGetHeader: the header
   read in any pieces into the gz_header (rt_gzip_header's G2ITheory: invariant J2 of the header phase), then the
   data decoded by the generalized decode theory with any gzip header (wide RTIG, RTIGW), the header reported
   complete.  The invariant is SGzDefs.sgz_P; the parts: the layout of deflate's stream (SGzLay), a call inside the
   header (SGzCallH), a call after it (SGzCallD) and a call offered nothing after it (SGzIdle). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.harness.rt_session.SIFacts.
Require Import Zlib.proof.harness.rt_session.SGzDefs.
Require Import Zlib.proof.harness.rt_session.SGzLay.
Require Import Zlib.proof.harness.rt_session.SGzCallH.
Require Import Zlib.proof.harness.rt_session.SGzCallD.
Require Import Zlib.proof.harness.rt_session.SGzIdle.
Require Import Zlib.proof.harness.rt_gzip_header.G2ILay.
Require Import Zlib.proof.harness.rt_gzip_header.G2ITheory.
Import ListNotations.
Local Open Scope Z_scope.

(* inflateInit2(16 + wb) accepts the window bits *)
Lemma sgz_wbits_ok wb : 9 <= wb <= 15 -> wbits_ok (16 + wb) = true.
Proof.
  intros W. assert (E: wb = 9 \/ wb = 10 \/ wb = 11 \/ wb = 12 \/ wb = 13 \/ wb = 14 \/ wb = 15) by lia.
  repeat destruct E as [E|E]; subst wb; reflexivity.
Qed.

(* the header reported once the header phase is over *)
Lemma sgz_hdr_out c D O src gh wb xfl bs pos out s h tout :
  sgz_lay_ok c D O src gh wb xfl bs -> sgz_pd (sc_h0 c) gh wb xfl bs src pos out s h tout ->
  g2_hdr_out gh (sc_h0 c) s h.
Proof.
  intros (_ & _ & _ & HOK & BUF & XFL & _) (DV & _ & HD & DN & X1 & X2 & X3).
  pose proof (g2_dinv_mode _ _ _ _ _ DV) as MD.
  destruct DV as (_ & (_ & _ & _ & GF) & _).
  apply (proj2 g2_lay_out gh xfl (sc_h0 c) s h HOK BUF XFL HD); auto.
  - apply g2_hdr_mode_after. lia.
  - apply GF; [reflexivity | unfold HEAD, Zlib.proof.inflate.Model.TYPE in *; lia
              | unfold FLAGS, Zlib.proof.inflate.Model.TYPE in *; lia].
Qed.

(* after inflateInit2(16 + wb) and inflateGetHeader: at HEAD, nothing consumed *)
Lemma sgz_init c D O src sp gh headp hsh xb nb cb wb xfl bs :
  sgz_lay_ok c D O src gh wb xfl bs ->
  live_ok8 (head_live (init_live sp (rts_iw (sc_wbits c))) (sc_h0 c) headp hsh xb nb cb) ->
  Z.land (i_wrap (l_s (init_live sp (rts_iw (sc_wbits c))))) 2 <> 0 /\
  swfW (l_s (head_live (init_live sp (rts_iw (sc_wbits c))) (sc_h0 c) headp hsh xb nb cb)) /\
  sgz_P c D O src 0 [] false (head_live (init_live sp (rts_iw (sc_wbits c))) (sc_h0 c) headp hsh xb nb cb) 0.
Proof.
  intros LAY. pose proof LAY as (GH & IW & W & HOK & BUF & XFL & GOK & LY & NH & NO & RW & FU & SL).
  rewrite IW. intros LV.
  set (L := head_live (init_live sp (16 + wb)) (sc_h0 c) headp hsh xb nb cb) in *.
  destruct (g2t_init_s sp wb (sc_h0 c) headp hsh xb nb cb W)
    as (Sm & Sw & Sh & Sb & Ss & St & Swb & Sl & Shd & Lh).
  fold L in Sm, Sw, Sh, Sb, Ss, St, Swb, Sl, Shd, Lh.
  assert (HW8: hwf8 (set_h_done (sc_h0 c) 0)) by (destruct LV as (_ & _ & _ & H8 & _); rewrite <- Lh; exact H8).
  split; [change (i_wrap (l_s (init_live sp (16 + wb)))) with (i_wrap (l_s L)); rewrite Sw; discriminate|].
  split; [unfold swfW; rewrite Sm; split; intros M; discriminate M|].
  exists gh, wb, xfl, bs. split; [split; assumption|]. split; [reflexivity|]. split; [lia|].
  left. split; [reflexivity|]. split; [reflexivity|].
  split; [|split; [|split]].
  - constructor; rewrite ?Lh; auto.
  - rewrite Lh. apply J2_HEAD; auto; try lia.
    + unfold bb2. rewrite Sh, Sb, sublist_nil. split; reflexivity.
    + unfold hx0; split; reflexivity.
    + unfold hn0; split; reflexivity.
    + unfold hc0; split; reflexivity.
  - destruct LY as [_ L2 L3 _]. unfold ih_xs in L3. destruct (fl (g2_g gh xfl) 4); lia.
  - rewrite Sm. unfold HEAD, Zlib.proof.inflate.Model.TYPE. lia.
Qed.

(* a gzip session never asks for a dictionary *)
Lemma sgz_not_zdict c D O : sc_ok c D O -> sc_gh c <> None -> ~ sk_zdict c /\ ~ sk_raw c.
Proof.
  intros (_ & _ & _ & G2 & _) K. unfold sk_zdict, sk_raw. rewrite (G2 K).
  split; intros (_ & W1); discriminate W1.
Qed.

(* the session's invariant after a call that ends after the header *)
Lemma sgz_P_after c D O src gh wb xfl bs pos out L tout :
  sgz_fix c D O src gh wb xfl bs -> 0 <= pos ->
  sgz_pd (sc_h0 c) gh wb xfl bs src pos out (l_s L) (l_h L) tout ->
  sgz_P c D O src pos out false L tout.
Proof.
  intros FX P0 PD. exists gh, wb, xfl, bs. split; [exact FX|]. split; [reflexivity|]. split; [exact P0|].
  right. exact PD.
Qed.

Theorem ses_itheory_gz : ses_itheory_gz_stmt.
Proof.
  exists sgz_P, sgz_PN. constructor.
  - (* inflateInit2 *)
    intros c D O src sp K OK SR.
    destruct (sc_gh c) as [gh|] eqn:GH; [|congruence].
    destruct (sgz_lay c D O src gh OK SR GH) as (wb & xfl & bs & LAY).
    pose proof LAY as (_ & IW & W & _). rewrite IW.
    split; [exact (sgz_wbits_ok wb W)|]. split; [|intros N; discriminate N].
    unfold swfW. destruct (reset2_wb (16 + wb)) as [[wr wb']|] eqn:E;
      unfold init_live; cbn [l_s]; rewrite E; split; intros M; discriminate M.
  - (* inflateGetHeader *)
    intros c D O src sp gh headp hsh xb nb cb K OK SR GH. cbv zeta. intros LV.
    destruct (sgz_lay c D O src gh OK SR GH) as (wb & xfl & bs & LAY).
    exact (sgz_init c D O src sp gh headp hsh xb nb cb wb xfl bs LAY LV).
  - (* no raw dictionary *)
    intros c D O src sp z alloc_ok winp K OK SR RAW.
    exfalso. exact (proj2 (sgz_not_zdict c D O OK K) RAW).
  - (* the header attached *)
    intros c D O src pos out asked L tout K (gh & wb & xfl & bs & ((GH & _) & _) & _ & _ & PH).
    rewrite GH. destruct PH as [(_ & _ & JC & _) | (_ & _ & HD & _)]; [exact (jc2_head _ _ _ _ JC) | exact HD].
  - (* one call *)
    intros c D O src pos out asked L z inp flush res winp K OK SR HP LC SW ZF AO LI P0 PL IE RUN.
    cbv zeta.
    destruct HP as (gh & wb & xfl & bs & FX & AS & _ & PH).
    pose proof FX as ((GH & IW & W & HOK & BUF & XFL & GOK & LY & NH & NO & RW & FU & SL) & HW8).
    pose proof (proj1 (sgz_not_zdict c D O OK K)) as NZ.
    unfold live_c in LC. rewrite GH in LC. subst asked.
    set (L' := Live (l_sp L) winp (m_s (r_m res)) (m_h (r_m res)) (l_headp L) (l_hsh L) (l_xb L) (l_nb L)
                 (l_cb L)).
    destruct PH as [(-> & TZ & PH) | PD].
    + (* inside the header *)
      destruct (sgz_call_h gh xfl wb bs src (sc_h0 c) pos L z inp flush res W HOK XFL GOK LY NH RW HW8 TZ PH
                  LC SW ZF AO LI (conj P0 (conj PL IE)) RUN)
        as [MEM | (SNX & SOW & AOT & [(R & SN & OW & TO & PH' & ID) | (NE & R & _ & PD' & EN)])];
        [left; exact MEM | |].
      * right. split; [destruct R as [R|R]; rewrite R; auto|].
        split; [exact SNX|]. split; [exact SOW|]. split; [exact AOT|].
        split; [exists D; rewrite OW; reflexivity|].
        split.
        { intros _. exists gh, wb, xfl, bs. split; [exact FX|]. split; [reflexivity|]. split; [lia|].
          left. rewrite OW, SN. split; [reflexivity|]. split; [exact TO|]. exact PH'. }
        split; [intros E; exfalso; destruct R as [R|R]; rewrite R in E; discriminate|].
        split; [intros E; exfalso; destruct R as [R|R]; rewrite R in E; discriminate|].
        intros I0 _. destruct (ID I0) as (R0 & T0). rewrite R0, OW, T0, TO, TZ.
        split; [discriminate|]. auto.
      * right. split; [destruct R as [R|[R|R]]; rewrite R; auto|].
        split; [exact SNX|]. split; [exact SOW|]. split; [exact AOT|].
        cbn [app].
        split; [destruct PD' as (_ & (rest & FR) & _); exists rest; rewrite <- FU; exact FR|].
        split; [intros _; apply (sgz_P_after c D O src gh wb xfl bs); [exact FX | lia | exact PD']|].
        split; [intros E; exfalso; destruct R as [R|[R|R]]; rewrite R in E; discriminate|].
        split; [|intros I0; contradiction].
        intros E. destruct (EN E) as (E1 & E2).
        split; [rewrite E1; exact FU|]. split; [rewrite E2; exact SL|].
        split; [split; [discriminate | intros Z; contradiction]|].
        intros gh' GH'. rewrite GH in GH'. injection GH' as <-.
        exact (sgz_hdr_out c D O src gh wb xfl bs _ _ _ _ _ (proj1 FX) PD').
    + (* after the header *)
      destruct PD as (DV & (rest & FR) & HD & DN & X1 & X2 & X3).
      destruct (sgz_call_d (g2_G gh xfl wb bs src) pos out L z inp flush res RW DV LC ZF AO LI P0 PL IE
                  (ex_intro _ out eq_refl) (ex_intro _ rest FR) RUN)
        as [MEM | (R & SNX & SOW & AOT & MH & IH & (rest' & FR') & DV' & EN)]; [left; exact MEM|].
      assert (PD': sgz_pd (sc_h0 c) gh wb xfl bs src (pos + m_snx (r_m res)) (out ++ m_ow (r_m res))
                     (m_s (r_m res)) (m_h (r_m res)) (m_tout (r_m res))).
      { split; [exact DV'|]. split; [exists rest'; rewrite <- app_assoc; exact FR'|].
        split; [rewrite IH; exact HD|]. rewrite MH. auto. }
      right. split; [destruct R as [R|[R|R]]; rewrite R; auto|].
      split; [exact SNX|]. split; [exact SOW|]. split; [exact AOT|].
      split; [exists rest'; rewrite <- FU; exact FR'|].
      split; [intros _; apply (sgz_P_after c D O src gh wb xfl bs); [exact FX | lia | exact PD']|].
      split; [intros E; exfalso; destruct R as [R|[R|R]]; rewrite R in E; discriminate|].
      split.
      * intros E. destruct (EN E) as (E1 & E2).
        split; [rewrite E1; exact FU|]. split; [rewrite E2; exact SL|].
        split; [split; [discriminate | intros Z; contradiction]|].
        intros gh' GH'. rewrite GH in GH'. injection GH' as <-.
        exact (sgz_hdr_out c D O src gh wb xfl bs _ _ _ _ _ (proj1 FX) PD').
      * intros I0 A0.
        assert (Ei: inp = []) by (apply Zlength_nil_inv; exact I0). subst inp.
        assert (NM: r_ret res <> Z_MEM_ERROR) by (destruct R as [R|[R|R]]; rewrite R; discriminate).
        destruct (sgz_idle_d (g2_G gh xfl wb bs src) pos out L z flush res RW DV LC ZF A0 P0
                    ltac:(rewrite Zlength_nil in PL; cbn; lia) (ex_intro _ out eq_refl) (ex_intro _ rest FR) RUN)
          as (I1 & I2 & I3).
        split; [exact I1|]. split; [exact I2|]. exact (I3 NM).
  - (* never Z_NEED_DICT *)
    intros c D O src pos out L tout K PN. destruct PN.
  - intros c D O src pos out L tout z alloc_ok winp K OK SR PN. destruct PN.
Qed.

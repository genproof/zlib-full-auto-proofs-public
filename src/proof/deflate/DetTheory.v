(** * The model facts of law api_deterministic ([det_theory_stmt], DetFacts.v) from the parts of DetWide.v

    The invariant: [Iapi] of the deflate_api theory (LTApiDefs.v) with no dictionary, the output kept short
    (the header and at most the trailer: the rest of the output is forgotten after each call, [tout] is then
    the length of what is kept, and [tout_shift_stmt] moves each call to the real total_out), no gzip header
    given (deflateSetHeader is not called), strm->adler 32 bits.  deflateParams after Z_FINISH: in FINISH_STATE
    its deflate(strm, Z_BLOCK) returns Z_STREAM_ERROR at once, or (same compression function and strategy) only
    the level changes ([cf_params]). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.DetFacts.
Require Import Zlib.proof.deflate.LTApiInit.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** Keeping the output short *)

(** The output [O] before the pending bytes [P] is the header [H], any body [B] and the end [T]: a shorter [O']
    (at most [H] and [T]) with the same pending bytes is also of that shape. *)
Lemma shrink_list : forall (O P H B T : list Z),
  O ++ P = H ++ B ++ T -> bytes O -> bytes H -> bytes T ->
  exists O' B', O' ++ P = H ++ B' ++ T /\ bytes O' /\ Zlength O' <= Zlength H + Zlength T /\
    (O <> [] -> H <> [] -> O' <> []).
Proof.
  intros O P H B T E BO BH BT.
  destruct (app_eq_app _ _ _ _ E) as (l & [[E1 E2] | [E1 E2]]).
  - destruct (app_eq_app _ _ _ _ (eq_sym E2)) as (m & [[F1 F2] | [F1 F2]]).
    + exists (H ++ m), []. split; [rewrite F2, <- app_assoc; reflexivity|].
      split; [apply Forall_app; split; [exact BH|]; rewrite F2 in BT; apply Forall_app in BT; tauto|].
      split; [rewrite Zlength_app, F2, Zlength_app; pose proof (Zlength_nonneg P); lia|].
      intros _ NH C. apply NH. destruct H; [reflexivity|discriminate].
    + exists H, m. split; [rewrite F2; reflexivity|]. split; [exact BH|].
      split; [pose proof (Zlength_nonneg T); lia|]. intros _ NH. exact NH.
  - exists O, B. split; [exact E|]. split; [exact BO|].
    split; [rewrite E1, Zlength_app; pose proof (Zlength_nonneg l); pose proof (Zlength_nonneg T); lia|].
    intros NO _. exact NO.
Qed.

(** A header of the deflate_api theory without a dictionary has a prefix of at most 10 bytes that is one too. *)
Lemma hdr_good_short : forall wrap H, 0 <= wrap <= 2 -> hdr_good [] wrap H ->
  exists H' R, H = H' ++ R /\ hdr_good [] wrap H' /\ Zlength H' <= 10 /\ (wrap <> 0 -> H' <> []).
Proof.
  intros wrap H Hw G.
  assert (Hc : wrap = 0 \/ wrap = 1 \/ wrap = 2) by lia.
  destruct Hc as [-> | [-> | ->]].
  - exists H, []. rewrite app_nil_r. pose proof G as (_ & G0 & _). pose proof (G0 eq_refl) as E.
    split; [reflexivity|]. split; [exact G|]. split; [rewrite E; cbn; lia|]. tauto.
  - exists H, []. rewrite app_nil_r. split; [reflexivity|]. split; [exact G|].
    destruct G as (_ & _ & G1 & _). destruct (G1 eq_refl) as (L & _). cbn in L.
    split; [lia|]. intros _ C. subst H. cbn in L. discriminate.
  - destruct G as (GB & _ & _ & G2). destruct (G2 eq_refl) as (L & G3).
    exists (sublist 0 10 H), (sublist 10 (Zlength H) H).
    split; [rewrite <- sublist_split by lia; rewrite sublist_same by lia; reflexivity|].
    assert (L10 : Zlength (sublist 0 10 H) = 10) by (rewrite Zlength_sublist by lia; lia).
    split.
    + split; [apply Forall_sublist; exact GB|].
      split; [lia|]. split; [lia|]. intros _. split; [lia|].
      rewrite sublist_sublist by lia. exact G3.
    + split; [lia|]. intros _ C. rewrite C in L10. cbn in L10. discriminate.
Qed.

(** [Iapi] without a dictionary and without a gzip header given only needs the start of the output: the header
    (at most 10 bytes) and, after the trailer was put, the part of the trailer already handed out (at most 8). *)
Lemma Iapi_shrink : forall W HI wrap D O fin s tin tout adler,
  hdr_facts HI -> Iapi W HI [] wrap D O fin s tin tout adler -> d_gzhead s = None ->
  exists O', Iapi W HI [] wrap D O' fin s tin (Zlength O') adler /\ Zlength O' <= 18.
Proof.
  intros W HI wrap D O fin s tin tout adler HF HI' Hgn.
  pose proof HI' as (HW & HO & Hw & Hd & Hbd & Hld & Hlf & Hgz & Ht & HbO & HbD & HtD & Hfin & HD0 & Hph).
  assert (Hph' : exists O', bytes O' /\ Zlength O' <= 18 /\
            (ph0 [] wrap D O' s tin adler \/
             (d_last_flush s <> -2 /\
              (ph1 HI [] wrap D O' s tin adler \/ ph2 [] wrap D O' s tin adler \/ ph3 [] wrap D O' s tin adler)))).
  { destruct Hph as [P0 | (Hl2 & [P1 | [P2 | P3]])].
    - exists O. pose proof P0 as (_ & _ & _ & EO & _). subst O.
      split; [exact HbO|]. split; [cbn; lia|]. left; exact P0.
    - destruct P1 as (_ & _ & _ & _ & _ & H & k & Hh & _).
      destruct (hf_status HI HF s adler H k Hh) as (_ & (h & Eh) & _). congruence.
    - destruct P2 as (St & Dw & Bv & Hne & Chk & H & body & G & E).
      destruct (hdr_good_short wrap H Hw G) as (H' & R & EH & G' & L' & NH').
      rewrite EH, <- app_assoc, <- (app_nil_r (R ++ body)) in E.
      destruct (shrink_list O (pend s) H' (R ++ body) [] E HbO (proj1 G') (Forall_nil _))
        as (O' & B' & E' & BO' & LO' & NO').
      exists O'. split; [exact BO'|]. split; [cbn in LO'; lia|].
      right. split; [exact Hl2|]. right; left.
      split; [exact St|]. split; [exact Dw|]. split; [exact Bv|].
      split; [intros W0; apply NO'; [apply Hne|apply NH']; exact W0|]. split; [exact Chk|].
      exists H', B'. split; [exact G'|]. rewrite app_nil_r in E'. exact E'.
    - destruct P3 as (St & La & Sn & Bv & Hne & Chk & H & body & G & HE).
      destruct (hdr_good_short wrap H Hw G) as (H' & R & EH & G' & L' & NH').
      assert (Hne' : forall O' : list Z, (O <> [] -> H' <> [] -> O' <> []) -> wrap <> 0 -> O' <> [])
        by (intros O' N W0; apply N; [apply Hne|apply NH']; exact W0).
      destruct HE as [(Dw & E) | (Wp & Dw & E)].
      + rewrite EH, <- app_assoc, <- (app_nil_r (R ++ body)) in E.
        destruct (shrink_list O (pend s) H' (R ++ body) [] E HbO (proj1 G') (Forall_nil _))
          as (O' & B' & E' & BO' & LO' & NO').
        exists O'. split; [exact BO'|]. split; [cbn in LO'; lia|].
        right. split; [exact Hl2|]. right; right.
        do 4 (split; [assumption|]). split; [apply Hne'; exact NO'|]. split; [exact Chk|].
        exists H', B'. split; [exact G'|]. left. split; [exact Dw|]. rewrite app_nil_r in E'. exact E'.
      + rewrite EH, <- app_assoc, app_assoc with (l := R) in E.
        destruct (shrink_list O (pend s) H' (R ++ body) (trailer wrap adler tin) E HbO (proj1 G')
                    (trailer_bytes wrap adler tin))
          as (O' & B' & E' & BO' & LO' & NO').
        exists O'. split; [exact BO'|].
        split; [rewrite Zlength_trailer in LO'; destruct (wrap =? 1), (wrap =? 2); lia|].
        right. split; [exact Hl2|]. right; right.
        do 4 (split; [assumption|]). split; [apply Hne'; exact NO'|]. split; [exact Chk|].
        exists H', B'. split; [exact G'|]. right. split; [exact Wp|]. split; [exact Dw|]. exact E'. }
  destruct Hph' as (O' & BO' & LO' & Ph').
  exists O'. split; [|exact LO'].
  unfold Iapi. repeat (split; [assumption|]). split; [reflexivity|]. repeat (split; [assumption|]). exact Ph'.
Qed.

(** [Iapi] mentions [fin] only in FINISH_STATE. *)
Lemma Iapi_fin : forall W HI dict wrap D O fin fin' s tin tout adler,
  Iapi W HI dict wrap D O fin s tin tout adler -> (d_status s = FINISH_STATE -> fin' = Some []) ->
  Iapi W HI dict wrap D O fin' s tin tout adler.
Proof.
  intros W HI dict wrap D O fin fin' s tin tout adler HI' Hf.
  destruct HI' as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15).
  unfold Iapi. tauto.
Qed.

(** ** total_out is any 64-bit value *)

Lemma zcall_shift : forall inb nin ain tin aout t0 tout adler msg, u64r tout ->
  zcall inb nin ain tin aout tout adler msg = zsh (tout - t0) (zcall inb nin ain tin aout t0 adler msg).
Proof.
  intros inb nin ain tin aout t0 tout adler msg Ht. unfold zsh, zcall, set_z_total_out; cbn.
  replace (t0 + (tout - t0)) with tout by lia. unfold u64, u64r in *. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma call_okw_shift : forall inb nin aout tin t0 tout z, call_okw inb nin aout tin t0 z ->
  call_okw inb nin aout tin tout (zsh (tout - t0) z).
Proof.
  intros inb nin aout tin t0 tout z (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8).
  unfold call_okw, zsh, set_z_total_out; cbn. do 6 (split; [assumption|]). split; [|assumption].
  rewrite C7. unfold u64. rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

(** ** deflateInit2 *)

(** deflateInit2 returns Z_OK only when the parameters are accepted and the five allocations succeed. *)
Lemma init_ok : forall level wbits mem strategy a1 a2 a3 a4 a5 z os z' code,
  c_deflateInit2_ true true false level 8 wbits mem strategy a1 a2 a3 a4 a5 z = Some (os, z', code) ->
  code = Z_OK ->
  params_ok level 8 wbits mem strategy = true /\
  c_deflateInit2_ true true false level 8 wbits mem strategy true true true true true z = Some (os, z', code).
Proof.
  intros level wbits mem strategy a1 a2 a3 a4 a5 z os z' code E Hc.
  rewrite init_shape in E.
  destruct (params_ok level 8 wbits mem strategy);
    [|inversion E; subst; unfold Z_OK, Z_STREAM_ERROR in *; lia].
  destruct a1; [|inversion E; subst; unfold Z_OK, Z_MEM_ERROR in *; lia].
  destruct (a2 && a3 && a4 && a5); [auto|inversion E; subst; unfold Z_OK, Z_MEM_ERROR in *; lia].
Qed.

(** ** deflateParams after Z_FINISH *)

(** deflate(strm, Z_BLOCK) in FINISH_STATE: Z_STREAM_ERROR at entry, only msg set. *)
Lemma deflate_block_finish : forall s z,
  bad_state s = false -> d_status s = FINISH_STATE ->
  c_deflate s z Z_BLOCK = Some (s, set_z_msg z (Some Z_STREAM_ERROR), Z_STREAM_ERROR).
Proof.
  intros s z Hb Hs. rewrite c_deflate_stages, Hb. cbn [orb].
  unfold c_deflate_entry. rewrite Hs. cbn. reflexivity.
Qed.

Lemma set_strategy_bind : forall (o : option dstate) st (z : strm) s2,
  (let* s := o in Some (set_d_strategy s st)) = Some s2 ->
  (let* s := o in Some (set_d_strategy s st, z, Z_OK)) = Some (s2, z, Z_OK).
Proof. intros [s|] st z s2 H; cbn in *; congruence. Qed.

(** deflateParams in FINISH_STATE (last_flush is not -2 there): either its deflate(strm, Z_BLOCK) fails at entry,
    or the compression function and the strategy are unchanged and only the level changes. *)
Lemma params_in_finish : forall W HI dict wrap D O fin s tin tout adler z level strategy,
  core_facts W -> hdr_facts HI -> Iapi W HI dict wrap D O fin s tin tout adler -> d_status s = FINISH_STATE ->
  exists s' z' code, c_deflateParams s z level strategy = Some (s', z', code) /\
    (z' = z \/ z' = set_z_msg z (Some Z_STREAM_ERROR)) /\ d_gzhead s' = d_gzhead s /\
    Iapi W HI dict wrap D O fin s' tin tout adler.
Proof.
  intros W HI dict wrap D O fin s tin tout adler z level strategy CF HF HI' Hst.
  assert (Hbad := Iapi_bad_state W HI dict wrap D O fin s tin tout adler HF HI').
  pose proof HI' as HI0. destruct HI0 as (HW & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hph).
  assert (Hlf : d_last_flush s <> -2).
  { destruct Hph as [P0 | (L & _)]; [|exact L].
    destruct P0 as [[[E _] | [E _]] _]; rewrite Hst in E; unfold FINISH_STATE, INIT_STATE, GZIP_STATE in E;
      discriminate. }
  pose proof (cf_prm W CF s HW) as Hprm.
  unfold c_deflateParams. rewrite Hbad. cbv zeta.
  set (lv := if level =? Z_DEFAULT_COMPRESSION then 6 else level).
  destruct ((lv <? 0) || (lv >? 9) || (strategy <? 0) || (strategy >? Z_FIXED)) eqn:Er.
  { exists s, z, Z_STREAM_ERROR. split; [reflexivity|]. split; [left; reflexivity|]. split; [reflexivity|].
    exact HI'. }
  assert (Hrange : 0 <= lv <= 9 /\ 0 <= strategy <= 4).
  { unfold Z_FIXED in Er. rewrite !orb_false_iff, Z.ltb_ge, Z.gtb_ltb, Z.ltb_ge, Z.ltb_ge, Z.gtb_ltb, Z.ltb_ge in Er.
    lia. }
  assert (Hlvl : 0 <= d_level s <= 9)
    by (destruct Hprm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & L & _); exact L).
  assert (Hcf : cfg_func (d_level s) = Some (cfg_f (d_level s))).
  { unfold cfg_func, cfg_f. replace ((0 <=? d_level s) && (d_level s <=? 9)) with true
      by (symmetry; apply andb_true_iff; split; apply Z.leb_le; lia).
    destruct (Znth (d_level s) config_table) as [[[[? ?] ?] ?] ?]. reflexivity. }
  rewrite Hcf. cbn [bind].
  destruct ((negb (strategy =? d_strategy s) || negb (cfg_f (d_level s) =? cfg_f lv)) && negb (d_last_flush s =? -2))
    eqn:Ec.
  - rewrite (deflate_block_finish s z Hbad Hst). cbn [bind]. rewrite Z.eqb_refl.
    exists s, (set_z_msg z (Some Z_STREAM_ERROR)), Z_STREAM_ERROR.
    split; [reflexivity|]. split; [right; reflexivity|]. split; [reflexivity|]. exact HI'.
  - assert (Hc : cfg_f lv = cfg_f (d_level s) /\ strategy = d_strategy s).
    { apply andb_false_iff in Ec. destruct Ec as [Ec|Ec].
      - apply orb_false_iff in Ec. destruct Ec as [E1 E2].
        apply negb_false_iff, Z.eqb_eq in E1. apply negb_false_iff, Z.eqb_eq in E2. auto.
      - apply negb_false_iff, Z.eqb_eq in Ec. contradiction. }
    destruct (cf_params W CF s lv strategy HW (proj1 Hrange) (proj2 Hrange) (or_introl Hc))
      as (s2 & Hpt & HW2 & Hapi & Hout & _ & _ & Hwb & Hhb & Hss & Hla & Hbs & Hsn).
    exists s2, z, Z_OK. split; [apply set_strategy_bind; exact Hpt|].
    split; [left; reflexivity|]. split; [apply Hapi|].
    apply (Iapi_frame W HI dict wrap D O fin s s2 tin tout adler HF HI' HW2 Hapi Hout); auto.
    pose proof (cf_prm W CF s2 HW2) as P2. destruct Hout as (Ho1 & _).
    destruct Hprm as (_ & _ & _ & _ & _ & _ & _ & _ & A1 & A2 & _).
    destruct P2 as (_ & _ & _ & _ & _ & _ & _ & _ & B1 & B2 & _).
    rewrite Ho1 in B2. lia.
Qed.

(** Without a dictionary total_in counts the data consumed. *)
Lemma Iapi_tin : forall W HI wrap D O fin s tin tout adler,
  Iapi W HI [] wrap D O fin s tin tout adler -> tin = Zlength D.
Proof.
  intros W HI wrap D O fin s tin tout adler HI'.
  destruct HI' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & T & _). cbn in T. lia.
Qed.

(** A call that only sets msg (or nothing). *)
Lemma call_okw_none : forall inb nin aout tin tout adler msg m,
  0 <= nin <= Zlength inb -> 0 <= aout -> u64r tout ->
  call_okw inb nin aout tin tout (zcall inb nin (Zlength inb - nin) tin aout tout adler msg) /\
  call_okw inb nin aout tin tout (set_z_msg (zcall inb nin (Zlength inb - nin) tin aout tout adler msg) m).
Proof.
  intros inb nin aout tin tout adler msg m Hn Ha Ht.
  assert (U : tout = u64 (tout + (aout - aout))) by (unfold u64, u64r in *; rewrite Z.mod_small; lia).
  unfold call_okw, zcall, set_z_msg; cbn.
  split; (split; [reflexivity|]; split; [lia|]; split; [lia|]; split; [lia|]; split; [lia|];
          split; [cbn; lia|]; split; [exact U|constructor]).
Qed.

Theorem det_theory :
  Zlib.proof.huffman.Overlay.overlay_statement -> core_wide_stmt -> hdr_wide_stmt -> tout_shift_stmt ->
  api_wide_stmt -> det_theory_stmt.
Proof.
  intros OV CW HW TS AW.
  destruct (CW OV) as (W & CF & CC & CS).
  destruct HW as (HI & HF & HR).
  destruct (AW W HI CF CC CS HF HR) as [AD AP].
  destruct TS as [TSD TSP].
  exists (fun fin s tin adler => exists wrap D O,
            Iapi W HI [] wrap D O fin s tin (Zlength O) adler /\ Zlength O <= 18 /\ d_gzhead s = None /\
            0 <= adler < 4294967296).
  constructor.
  - (* deflateInit2 *)
    intros level wbits mem strategy a1 a2 a3 a4 a5 z Hl Hw Hm Hs.
    assert (Hmeth : s32 8) by (unfold s32; lia).
    destruct (api_init W HI level 8 wbits mem strategy a1 a2 a3 a4 a5 z CF HF Hl Hmeth Hw Hm Hs) as [Ex Hpost].
    split; [exact Ex|]. intros os z' code E.
    destruct (Hpost os z' code E) as (C1 & C2 & C3). split; [exact C1|]. split; [exact C2|]. intros Hok.
    destruct (init_ok level wbits mem strategy a1 a2 a3 a4 a5 z os z' code E Hok) as [Pok E1].
    destruct (cf_init W CF level 8 wbits mem strategy z Pok)
      as (s0 & z0 & E0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hz0).
    rewrite E0 in E1. injection E1 as Eos Ez Ec. subst os z' code.
    split.
    + destruct (C3 eq_refl) as (s & Es & Hgz & _ & HIs). exists s. split; [exact Es|].
      rewrite Hz0 in HIs |- *. cbn [z_total_in z_total_out z_adler] in HIs |- *.
      split; [reflexivity|]. split; [reflexivity|].
      exists (wrap_of wbits), [], []. split; [exact HIs|]. split; [cbn; lia|]. split; [exact Hgz|].
      destruct (wrap_of wbits =? 2); lia.
    + intros b1 b2 b3 b4 b5 os2 z2 code2 E2 Hok2.
      destruct (init_ok level wbits mem strategy b1 b2 b3 b4 b5 z os2 z2 code2 E2 Hok2) as [_ E3].
      rewrite E0 in E3. injection E3 as <- <- _. auto.
  - (* strm->adler *)
    intros fin s tin adler (wrap & D & O & _ & _ & _ & A). exact A.
  - (* deflate *)
    intros fin s tin adler inb nin aout tout flush msg (wrap & D & O & HI' & LO & Hgz & Ha)
      Hfl Hb Hn Hin Hao Ht Hfin.
    pose proof (Iapi_tin W HI wrap D O fin s tin (Zlength O) adler HI') as Htin.
    destruct (AD [] wrap D O fin s tin (Zlength O) adler inb nin aout flush msg HI' Hfl Hb Hn ltac:(lia) Hao
                ltac:(lia) Hfin) as (s' & z' & code & E & G & C & A' & Post).
    rewrite (zcall_shift inb nin (Zlength inb - nin) tin aout (Zlength O) tout adler msg Ht), TSD, E.
    cbn [option_map]. exists s', (zsh (tout - Zlength O) z'), code. unfold rsh; cbn [fst snd].
    split; [reflexivity|]. split; [apply call_okw_shift; exact C|].
    intros Hne. specialize (Post Hne).
    destruct (Iapi_shrink W HI wrap _ _ _ s' _ _ _ HF Post) as (O' & HO' & LO'); [rewrite G; exact Hgz|].
    unfold zsh, set_z_total_out; cbn [z_total_in z_adler z_next_in].
    exists wrap, (D ++ sublist nin (z_next_in z') inb), O'.
    split; [exact HO'|]. split; [exact LO'|]. split; [rewrite G; exact Hgz|]. apply A'; exact Ha.
  - (* deflateParams *)
    intros fin s tin adler inb nin aout tout level strategy msg (wrap & D & O & HI' & LO & Hgz & Ha)
      Hl Hs Hb Hn Hin Hao Ht Hfin.
    pose proof (Iapi_tin W HI wrap D O fin s tin (Zlength O) adler HI') as Htin.
    destruct (Z.eq_dec (d_status s) FINISH_STATE) as [Hst | Hst].
    + pose proof HI' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hf & _).
      specialize (Hf Hst). subst fin. pose proof (Hfin [] eq_refl) as Hr.
      destruct (params_in_finish W HI [] wrap D O (Some []) s tin (Zlength O) adler
                  (zcall inb nin (Zlength inb - nin) tin aout tout adler msg) level strategy CF HF HI' Hst)
        as (s' & z' & code & E & Ez & G & HI2).
      destruct (call_okw_none inb nin aout tin tout adler msg (Some Z_STREAM_ERROR) Hn (proj1 Hao) Ht)
        as [K1 K2].
      exists s', z', code. split; [exact E|].
      assert (Hz : z_next_in z' = nin /\ z_total_in z' = tin /\ z_adler z' = adler)
        by (destruct Ez as [-> | ->]; cbn; auto).
      destruct Hz as (Z1 & Z2 & Z3).
      split; [destruct Ez as [-> | ->]; assumption|].
      rewrite Z1, Z2, Z3, <- Hr. exists wrap, D, O.
      split; [exact HI2|]. split; [exact LO|]. split; [rewrite G; exact Hgz|exact Ha].
    + assert (HI0 : Iapi W HI [] wrap D O None s tin (Zlength O) adler)
        by (apply (Iapi_fin W HI [] wrap D O fin None s tin (Zlength O) adler HI'); intros E; contradiction).
      destruct (AP [] wrap D O s tin (Zlength O) adler inb nin aout level strategy msg HI0 Hl Hs Hb Hn ltac:(lia)
                  Hao ltac:(lia)) as (s' & z' & code & E & G & C & A' & Post).
      rewrite (zcall_shift inb nin (Zlength inb - nin) tin aout (Zlength O) tout adler msg Ht), TSP, E.
      cbn [option_map]. exists s', (zsh (tout - Zlength O) z'), code. unfold rsh; cbn [fst snd].
      split; [reflexivity|]. split; [apply call_okw_shift; exact C|].
      pose proof Post as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hf' & _).
      apply (Iapi_fin W HI [] wrap _ _ None
               (match fin with None => None | Some _ => Some (sublist (z_next_in z') (Zlength inb) inb) end))
        in Post; [|intros E'; specialize (Hf' E'); discriminate].
      destruct (Iapi_shrink W HI wrap _ _ _ s' _ _ _ HF Post) as (O' & HO' & LO'); [rewrite G; exact Hgz|].
      unfold zsh, set_z_total_out; cbn [z_total_in z_adler z_next_in].
      exists wrap, (D ++ sublist nin (z_next_in z') inb), O'.
      split; [exact HO'|]. split; [exact LO'|]. split; [rewrite G; exact Hgz|]. apply A'; exact Ha.
Qed.

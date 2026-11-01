(* Law inflate_header, theory: the invariant of the harness's loop (ih_I), one inflate() call from the cases
   (the pass by the mode, Model2.loop2 from Spec5.m_init, inf_leave), and the facts of IHFacts.ih_facts. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.inflate_header.IHTDefs.
Require Import Zlib.proof.inflate_api.ResetFacts.
Import ListNotations.
Local Open Scope Z_scope.

(* the invariant at a call boundary: pos bytes of src consumed *)
Definition ih_I (g: ihg) (w: Z) (h0: hstate) (pos: Z) (z: zfields) (L: live) : Prop :=
  hwf h0 /\ 0 <= pos <= Zlength (ih_src g) /\ zf_tout z = 0 /\ Jc h0 (l_s L) (l_h L) /\
  J g h0 pos (l_s L) (l_h L) (i_hold (l_s L)) (i_bits (l_s L)).

(* all the cases *)
Definition ih_cases : Prop :=
  case_ok HEAD c_HEAD2 /\ case_ok FLAGS c_FLAGS2 /\ case_ok TIME c_TIME2 /\ case_ok OS c_OS2 /\
  case_ok EXLEN c_EXLEN2 /\ case_ok EXTRA c_EXTRA2 /\ case_ok NAME c_NAME2 /\ case_ok COMMENT c_COMMENT2 /\
  case_ok HCRC c_HCRC /\
  (forall flush, case_ok Zlib.proof.inflate.Model.TYPE (c_TYPE flush)) /\
  (forall flush, case_ok TYPEDO (c_TYPEDO flush)) /\
  (forall flush, case_ok STORED (c_STORED flush)) /\
  case_ok COPY_ c_COPY_ /\ case_ok COPY c_COPY /\ case_ok CHECK c_CHECK /\ case_ok LENGTH c_LENGTH /\
  case_ok DONE c_DONE /\ case_ok BAD c_BAD.

(* ---------------------------------------------------------------------------------------------- *)
(* Transfers                                                                                      *)

Lemma ihl_J_proj g h0 P s s' h hold bits :
  J g h0 P s h hold bits ->
  i_mode s' = i_mode s -> i_last s' = i_last s -> i_check s' = i_check s -> i_flags s' = i_flags s ->
  i_length s' = i_length s ->
  J g h0 P s' h hold bits.
Proof.
  intros H Em El Ec Ef En.
  assert (Ck: forall k, ck g s k -> ck g s' k) by (unfold ck; intros k C F; rewrite Ec; auto).
  assert (Fg: fg g s -> fg g s') by (unfold fg; rewrite Ef; auto).
  destruct H;
    [ eapply J_HEAD | eapply J_FLAGS | eapply J_TIME | eapply J_OS | eapply J_EXLEN | eapply J_EXTRA
    | eapply J_NAME | eapply J_COMMENT | eapply J_HCRC | eapply J_TYPE | eapply J_STORED | eapply J_COPY
    | eapply J_CHECK | eapply J_LENGTH | eapply J_DONE | eapply J_BAD ];
    rewrite ?Em, ?El, ?Ec, ?En; eauto.
Qed.

Lemma ihl_Jc_proj h0 s s' h :
  Jc h0 s h -> i_wrap s' = i_wrap s -> i_head s' = i_head s -> i_wsize s' = i_wsize s -> i_total s' = i_total s ->
  Jc h0 s' h.
Proof. intros [A B C D E F G] W Hd Ws T. constructor; rewrite ?W, ?Hd, ?Ws, ?T; auto. Qed.

(* the mode of J *)
Lemma ihl_J_done g h0 P s h hold bits :
  J g h0 P s h hold bits -> i_mode s = DONE ->
  P = ih_nh g + 13 /\ ih_reserved g = false /\ ih_badcrc g = false /\ ih_done_ok g h0 h.
Proof.
  intros H E. destruct H; auto;
  exfalso; repeat match goal with H: _ \/ _ |- _ => destruct H end;
  rewrite E in *;
  unfold DONE, HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC, Zlib.proof.inflate.Model.TYPE, TYPEDO,
    STORED, COPY_, COPY, CHECK, LENGTH, BAD in *; lia.
Qed.

Lemma ihl_J_bad g h0 P s h hold bits :
  J g h0 P s h hold bits -> i_mode s = BAD -> h_done h = 0 /\ orb (ih_reserved g) (ih_badcrc g) = true.
Proof.
  intros H E. destruct H; auto;
  exfalso; repeat match goal with H: _ \/ _ |- _ => destruct H end;
  rewrite E in *;
  unfold DONE, HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC, Zlib.proof.inflate.Model.TYPE, TYPEDO,
    STORED, COPY_, COPY, CHECK, LENGTH, BAD in *; lia.
Qed.

(* head->done is 0 before the end of the header, then the fields are complete *)
Lemma ihl_J_hdone g h0 P s h hold bits :
  J g h0 P s h hold bits -> h_done h <> 0 -> ih_done_ok g h0 h.
Proof. intros H N. destruct H; auto; contradiction. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* One pass, the loop                                                                             *)

Ltac ihl_stepto c :=
  match goal with |- ok_out _ _ _ _ (stepf2 ?f ?fx ?dx ?m) =>
    replace (stepf2 f fx dx m) with (c m) by (unfold stepf2, step2; unfold m_mode in *;
      match goal with E: i_mode (m_s m) = _ |- _ => rewrite E end; reflexivity) end.

Lemma ihl_step : ih_cases -> forall g h0 pos inp flush m,
  ih_ok g -> hwf h0 -> ih_ctx g pos inp -> Km g h0 pos inp m -> m_leave m = 0 ->
  ok_out g h0 pos inp (stepf2 flush lenfix_list distfix_list m).
Proof.
  intros C g h0 pos inp flush m G W X K L.
  destruct C as (CHE & CFL & CTI & COS & CEL & CEX & CNA & CCO & CHC & CTY & CTD & CST & CC_ & CCP & CCK & CLN & CDN & CBD).
  pose proof (km_j _ _ _ _ _ K) as JJ.
  destruct JJ;
    repeat match goal with H: i_mode _ = _ \/ i_mode _ = _ |- _ => destruct H end;
    match goal with E: i_mode (m_s m) = ?md |- _ => assert (Em: m_mode m = md) by exact E end;
    first
    [ solve [ihl_stepto c_HEAD2; apply CHE; auto] | solve [ihl_stepto c_FLAGS2; apply CFL; auto]
    | solve [ihl_stepto c_TIME2; apply CTI; auto] | solve [ihl_stepto c_OS2; apply COS; auto]
    | solve [ihl_stepto c_EXLEN2; apply CEL; auto] | solve [ihl_stepto c_EXTRA2; apply CEX; auto]
    | solve [ihl_stepto c_NAME2; apply CNA; auto] | solve [ihl_stepto c_COMMENT2; apply CCO; auto]
    | solve [ihl_stepto c_HCRC; apply CHC; auto] | solve [ihl_stepto (c_TYPE flush); apply CTY; auto]
    | solve [ihl_stepto (c_TYPEDO flush); apply CTD; auto] | solve [ihl_stepto (c_STORED flush); apply CST; auto]
    | solve [ihl_stepto c_COPY_; apply CC_; auto] | solve [ihl_stepto c_COPY; apply CCP; auto]
    | solve [ihl_stepto c_CHECK; apply CCK; auto] | solve [ihl_stepto c_LENGTH; apply CLN; auto]
    | solve [ihl_stepto c_DONE; apply CDN; auto] | solve [ihl_stepto c_BAD; apply CBD; auto] ].
Qed.

Lemma ihl_loop : ih_cases -> forall g h0 pos inp flush m o,
  ih_ok g -> hwf h0 -> ih_ctx g pos inp ->
  loop2 flush lenfix_list distfix_list m o -> Km g h0 pos inp m -> m_leave m = 0 ->
  exists m', o = IBrk m' /\ Km g h0 pos inp m' /\ m_leave m' = 1.
Proof.
  intros C g h0 pos inp flush m o G W X LP.
  induction LP as [m r m' E | m m' E L1 | m m' o E L1 LP IH]; intros K L0.
  - pose proof (ihl_step C g h0 pos inp flush m G W X K L0) as S. rewrite E in S. destruct S.
  - pose proof (ihl_step C g h0 pos inp flush m G W X K L0) as S. rewrite E in S. cbn in S.
    exists m'. auto.
  - pose proof (ihl_step C g h0 pos inp flush m G W X K L0) as S. rewrite E in S. cbn in S.
    apply IH; auto. destruct (km_lv _ _ _ _ _ S); [auto | contradiction].
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* inf_leave                                                                                      *)

Lemma ihl_leave_ok flush m : i_wsize (m_s m) = 0 -> m_out m = m_aout m -> m_ow m = [] ->
  leave_ok flush m = false.
Proof.
  intros Ws O W. unfold leave_ok, m_left. rewrite Ws, O, W, Zlength_nil, Z.sub_0_r, !Z.eqb_refl. reflexivity.
Qed.

Lemma ihl_fin flush m : i_wsize (m_s m) = 0 -> m_out m = m_aout m -> m_ow m = [] -> m_tout m = 0 ->
  i_total (m_s m) = 0 ->
  let res := leave_fin flush m in
  (r_ret res = Z_BUF_ERROR \/ r_ret res = m_ret m) /\
  m_snx (r_m res) = m_nx m /\ m_inp (r_m res) = m_inp m /\ m_tout (r_m res) = 0 /\ m_h (r_m res) = m_h m /\
  i_mode (m_s (r_m res)) = m_mode m /\ i_last (m_s (r_m res)) = i_last (m_s m) /\
  i_check (m_s (r_m res)) = i_check (m_s m) /\ i_flags (m_s (r_m res)) = i_flags (m_s m) /\
  i_length (m_s (r_m res)) = i_length (m_s m) /\ i_wrap (m_s (r_m res)) = i_wrap (m_s m) /\
  i_head (m_s (r_m res)) = i_head (m_s m) /\ i_wsize (m_s (r_m res)) = 0 /\ i_total (m_s (r_m res)) = 0 /\
  i_hold (m_s (r_m res)) = m_hold m /\ i_bits (m_s (r_m res)) = m_bits m.
Proof.
  intros Ws O W T Tt. cbv zeta. unfold leave_fin. rewrite (ihl_leave_ok flush m Ws O W).
  cbv zeta.
  assert (Eo: u32 (m_out (restore m) - m_left (restore m)) = 0).
  { unfold m_left. cbn. rewrite O, W, Zlength_nil, Z.sub_0_r, Z.sub_diag. reflexivity. }
  rewrite Eo. rewrite andb_false_r.
  cbn. unfold m_mode. rewrite Ws, Tt, T. cbn.
  repeat split; auto.
  destruct (andb _ _); auto.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* inflateInit2_ and the loop head of a call                                                      *)

Lemma ihl_wrap_val w wrap wb : reset2_wb w = Some (wrap, wb) ->
  (w < 0 /\ wrap = 0) \/ (0 <= w < 16 /\ wrap = 5) \/ (16 <= w < 32 /\ wrap = 6) \/ (32 <= w < 48 /\ wrap = 7).
Proof.
  unfold reset2_wb. intros E.
  destruct (Z.ltb_spec w 0) as [N|N].
  - destruct (w <? -15); [discriminate|]. destruct (_ && _)%bool; inversion E; subst. left; auto.
  - destruct (Z.ltb_spec w 48) as [H48|H48].
    + destruct (_ || _)%bool; [|discriminate]. inversion E; subst wrap.
      rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
      pose proof (Z.div_mod w 16 ltac:(lia)) as D. pose proof (Z.mod_pos_bound w 16 ltac:(lia)) as M.
      assert (0 <= w / 16 <= 2) by lia.
      assert (w / 16 = 0 \/ w / 16 = 1 \/ w / 16 = 2) as [Q|[Q|Q]] by lia; rewrite Q in *; lia.
    + exfalso. destruct ((w =? 0) || (8 <=? w) && (w <=? 15))%bool eqn:C; [|discriminate].
      apply orb_true_iff in C. rewrite andb_true_iff, Z.eqb_eq, Z.leb_le, Z.leb_le in C. lia.
Qed.

(* the state after inflateInit2_ on the wrap and wbits of reset2_wb (wrap 0..7): with fix F8 its wrap has bit 3
   set when wb = 0 (the window size comes from the header) *)
Lemma ihl_init_s wrap wb : 0 <= wrap <= 7 ->
  let s := init_s wrap wb in
  i_wrap s = reset2_wrap wrap wb /\ i_mode s = HEAD /\ i_hold s = 0 /\ i_bits s = 0 /\ i_wsize s = 0 /\
  i_total s = 0 /\ i_last s = 0.
Proof.
  intros R. cbv zeta.
  destruct (init_s_fields wrap wb R) as (? & _ & _ & ? & _ & ? & _ & _ & _ & _ & _ & ? & ? & ? & _ & ?).
  repeat split; assumption.
Qed.

Lemma ihl_J_typedo g h0 P s h hold bits :
  J g h0 P s h hold bits -> i_mode s = Zlib.proof.inflate.Model.TYPE -> J g h0 P (set_i_mode s TYPEDO) h hold bits.
Proof.
  intros H E. destruct H;
  try solve [exfalso; repeat match goal with H: _ \/ _ |- _ => destruct H end; rewrite E in *;
    unfold DONE, HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC, Zlib.proof.inflate.Model.TYPE, TYPEDO,
      STORED, COPY_, COPY, CHECK, LENGTH, BAD in *; lia].
  apply J_TYPE; cbn; auto.
Qed.

Lemma ihl_init_km g w h0 pos z L inp ni ai no ao :
  ih_I g w h0 pos z L -> ih_ctx g pos inp ->
  Km g h0 pos inp (m_init (ih_zcall z ni ai no ao) L inp) /\ m_leave (m_init (ih_zcall z ni ai no ao) L inp) = 0.
Proof.
  intros (HW & PR & TZ & JC & JJ) C. unfold m_init. cbn [ih_zcall zf_ao zf_adler zf_msg zf_tin zf_tout].
  split; [|reflexivity].
  destruct (Z.eqb_spec (i_mode (l_s L)) Zlib.proof.inflate.Model.TYPE) as [E|E].
  - constructor; cbn [m_s m_h m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave m_tout]; auto.
    + split; [lia | apply Zlength_nonneg].
    + apply (ihl_Jc_proj _ (l_s L)); auto.
    + rewrite Z.add_0_r. apply ihl_J_typedo; auto.
  - constructor; cbn [m_s m_h m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave m_tout]; auto.
    + split; [lia | apply Zlength_nonneg].
    + rewrite Z.add_0_r. auto.
Qed.

Ltac ihl_cst := unfold Z_OK, Z_BUF_ERROR, Z_STREAM_END, Z_DATA_ERROR, Z_MEM_ERROR in *; lia.

Lemma ihl_wrap : forall w sp, wbits_ok w = true ->
    (Z.land (i_wrap (l_s (init_live sp w))) 2 =? 0) = (w <? 16).
Proof.
  intros w sp W. unfold init_live, wbits_ok in *.
  destruct (reset2_wb w) as [[wrap wb]|] eqn:E; [|discriminate].
  cbn [l_s]. destruct (ihl_wrap_val _ _ _ E) as [(A & Ew)|[(A & Ew)|[(A & Ew)|(A & Ew)]]];
    destruct (ihl_init_s wrap wb ltac:(lia)) as (-> & _); subst wrap; unfold reset2_wrap;
    destruct (wb =? 0); cbn; symmetry; apply Z.ltb_lt || apply Z.ltb_ge; lia.
Qed.

Lemma ihl_init : forall g w h0 z sp headp hsh xb nb cb,
    ih_ok g -> wbits_ok w = true -> 16 <= w -> Int.min_signed <= w <= Int.max_signed ->
    isptr sp -> zf_ok z -> zf_msg z = None -> zf_tout z = 0 ->
    hwf h0 -> writable_share hsh ->
    (h_xp h0 = true -> xb <> nullval) -> (h_np h0 = true -> nb <> nullval) -> (h_cp h0 = true -> cb <> nullval) ->
    ih_I g w h0 0 z (ih_L0 sp w h0 headp hsh xb nb cb).
Proof.
  intros g w h0 z sp headp hsh xb nb cb G W L16 _ _ _ _ TZ HW _ _ _ _.
  unfold wbits_ok in W. destruct (reset2_wb w) as [[wrap wb]|] eqn:E; [|discriminate].
  assert (Wr: wrap = 6 \/ wrap = 7)
    by (destruct (ihl_wrap_val _ _ _ E) as [(A & ->)|[(A & ->)|[(A & ->)|(A & ->)]]]; lia).
  destruct (ihl_init_s wrap wb ltac:(lia)) as (Ew & Em & Eh & Eb & Es & Et & El).
  unfold ih_L0, init_live. rewrite E. cbn [l_s l_h set_l_head set_l_s].
  revert Ew Em Eh Eb Es Et El. generalize (init_s wrap wb). intros s0 Ew Em Eh Eb Es Et El.
  split; [auto|]. split; [pose proof (Zlength_nonneg (ih_src g)); lia|]. split; [auto|].
  cbn [l_s l_h set_l_head set_l_s]. split.
  + constructor; cbn [i_wrap i_head i_wsize i_total set_i_head h_extra_max h_name_max h_comm_max set_h_done];
      rewrite ?Ew, ?Es, ?Et; auto.
    unfold reset2_wrap. destruct (wb =? 0), Wr as [-> | ->]; cbn; auto.
  + assert (Hh: i_hold (set_i_head s0 true) = 0) by (cbn [i_hold set_i_head]; exact Eh).
    assert (Hb: i_bits (set_i_head s0 true) = 0) by (cbn [i_bits set_i_head]; exact Eb).
    rewrite Hh, Hb.
    apply J_HEAD; cbn [i_mode i_last set_i_head]; auto; try lia.
    * unfold bb. rewrite sublist_nil. cbn. lia.
    * unfold hx0; cbn; auto.
    * unfold hn0; cbn; auto.
    * unfold hc0; cbn; auto.
Qed.

Lemma ihl_live : forall g w h0 pos z L,
    ih_I g w h0 pos z L ->
    i_head (l_s L) = true /\ h_extra_max (l_h L) = h_extra_max h0 /\ h_name_max (l_h L) = h_name_max h0 /\
    h_comm_max (l_h L) = h_comm_max h0.
Proof.
  intros g w h0 pos z L (_ & _ & _ & JC & _).
  destruct JC as [_ A _ _ B1 B2 B3]. auto.
Qed.

Lemma ihl_inflate : ih_kit -> ih_cases -> forall g w h0 pos z L strmp flush ib inp o ain aout r z' st' ow,
    ih_ok g -> ih_I g w h0 pos z L -> live_ok L -> zf_ok z -> strmp <> nullval ->
    0 <= pos -> 0 <= ain -> pos + ain <= Zlength (ih_src g) -> 0 <= aout <= 2 ^ 20 ->
    Int.min_signed <= flush <= Int.max_signed ->
    ib <> InNull -> inp = sublist pos (pos + ain) (ih_src g) ->
    inflate_rel flush strmp (ih_zcall z (in_ptr ib 0) ain (out_ptr o 0) aout) (Some L) ib inp (Some o)
      r z' st' ow ->
    exists L', st' = Some L' /\ ih_post ih_I g w h0 pos ain r z' L'.
Proof.
  intros KIT C.
  intros g w h0 pos z L strmp flush ib inp o ain aout r z' st' ow G IV LV ZF SN P0 A0 PA AO FL IB EI R.
  pose proof IV as (HW & PR & TZ & JC & JJ).
  pose proof (ly_len _ (k_lay KIT g G)) as LEN.
  assert (CTX: ih_ctx g pos inp).
  { assert (Zlength inp = ain) by (subst inp; rewrite Zlength_sublist; lia).
    split; [lia|]. split; [lia|]. rewrite H. exact EI. }
  assert (ZI: Zlength inp = ain) by (subst inp; rewrite Zlength_sublist; lia).
  destruct R as [(Hbad & _) | (NB & L1 & o1 & res & winp & E1 & E2 & RUN & SNX & ER & EOW & EZ & EW & EST)].
  + exfalso. unfold inflate_bad, is_live in Hbad. destruct (eq_dec strmp nullval); [contradiction|].
    destruct Hbad as [B|[B|[B _]]]; [discriminate | discriminate | contradiction].
  + inversion E1; subst L1. inversion E2; subst o1.
    destruct RUN as (io & LP & RES).
    destruct (ihl_init_km g w h0 pos z L inp (in_ptr ib 0) ain (out_ptr o 0) aout IV CTX) as [K0 L0].
    destruct (ihl_loop C g h0 pos inp flush _ io G HW CTX LP K0 L0) as (m' & -> & K' & L').
    pose proof K' as [Ki Kn Kw Ko Kt Kr Kl Kc Kj].
    assert (Ws: i_wsize (m_s m') = 0) by apply (jc_wsize _ _ _ Kc).
    assert (Tt: i_total (m_s m') = 0) by apply (jc_total _ _ _ Kc).
    inversion RES as [LO _ | ]; subst res.
    { rewrite (ihl_leave_ok flush m' Ws Ko Kw) in LO. discriminate. }
    destruct (ihl_fin flush m' Ws Ko Kw Kt Tt) as (Rr & Fnx & Finp & Ftout & Fh & Fmd & Fla & Fck & Ffl & Fln & Fwr & Fhd & Fws & Ftt & Fho & Fbi).
    set (res := leave_fin flush m') in *.
    exists (Live (l_sp L) winp (m_s (r_m res)) (m_h (r_m res)) (l_headp L) (l_hsh L) (l_xb L) (l_nb L) (l_cb L)).
    split; [exact EST|].
    assert (Eai: zf_ai z' = ain - m_nx m').
    { rewrite EZ. unfold z_after. cbn [zf_ai]. rewrite Finp, Fnx, Ki, ZI. reflexivity. }
    assert (Eto: zf_tout z' = 0) by (rewrite EZ; unfold z_after; cbn [zf_tout]; exact Ftout).
    assert (Eused: ain - zf_ai z' = m_nx m') by lia.
    unfold ih_post. cbv zeta. rewrite Eused. cbn [l_h l_s].
    rewrite Fh.
    assert (RET: r = Z_BUF_ERROR \/ r = m_ret m') by (subst r; exact Rr).
    split.
    { destruct RET as [ ->| ->]; [tauto|]. destruct Kr as [ ->|[(-> & _)|(-> & _)]]; tauto. }
    split; [lia|].
    split.
    { intros RB E. assert (E2': m_ret m' = Z_STREAM_END) by (destruct RET as [X|X]; [exfalso; rewrite X in E; ihl_cst | rewrite <- X; exact E]).
      destruct Kr as [X|[(_ & D)|(X & _)]]; try (exfalso; rewrite X in E2'; ihl_cst).
      destruct (ihl_J_done _ _ _ _ _ _ _ Kj D) as (_ & N1 & N2 & _). rewrite N1, N2 in RB. discriminate. }
    split.
    { intros RB E. assert (E2': m_ret m' = Z_DATA_ERROR) by (destruct RET as [X|X]; [exfalso; rewrite X in E; ihl_cst | rewrite <- X; exact E]).
      destruct Kr as [X|[(X & _)|(_ & D)]]; try (exfalso; rewrite X in E2'; ihl_cst).
      destruct (ihl_J_bad _ _ _ _ _ _ _ Kj D) as (_ & N). rewrite N in RB. discriminate. }
    split.
    { intros _ E. assert (E2': m_ret m' = Z_DATA_ERROR) by (destruct RET as [X|X]; [exfalso; rewrite X in E; ihl_cst | rewrite <- X; exact E]).
      destruct Kr as [X|[(X & _)|(_ & D)]]; try (exfalso; rewrite X in E2'; ihl_cst).
      destruct (ihl_J_bad _ _ _ _ _ _ _ Kj D) as (N & _). exact N. }
    split.
    { intros _ N. apply (ihl_J_hdone _ _ _ _ _ _ _ Kj N). }
    split.
    { intros E. assert (E2': m_ret m' = Z_STREAM_END) by (destruct RET as [X|X]; [exfalso; rewrite X in E; ihl_cst | rewrite <- X; exact E]).
      destruct Kr as [X|[(_ & D)|(X & _)]]; try (exfalso; rewrite X in E2'; ihl_cst).
      destruct (ihl_J_done _ _ _ _ _ _ _ Kj D) as (Pp & _ & _ & (Dn & _)).
      split; [exact Dn|]. split; [lia | exact Eto]. }
    intros _. split; [exact HW|]. split; [lia|]. split; [exact Eto|]. cbn [l_s l_h]. split.
    * apply (ihl_Jc_proj _ (m_s m')); auto; congruence.
    * rewrite Fho, Fbi. apply (ihl_J_proj _ _ _ (m_s m')); auto.
Qed.

Lemma ih_call : ih_kit -> ih_cases -> ih_facts ih_I.
Proof.
  intros KIT C. constructor.
  - exact ihl_wrap.
  - exact ihl_init.
  - exact ihl_live.
  - exact (ihl_inflate KIT C).
Qed.

(* One inflate() call (Model2.run2) from a boundary state: the loop moves the abstract state within the call's limits, inf_leave restores the boundary relation (window, check, total). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.api_split_invariant.SIDefs.
Require Zlib.proof.harness.inflate_buffers.IBStepKit.
Require Zlib.proof.rfc1951.DecCallWkeepKit.
Require Zlib.proof.crc32.Combine.
Require Zlib.proof.harness.api_split_invariant.SICallLeave.
Require Zlib.proof.harness.api_split_invariant.SICallWin.
Import ListNotations.
Local Open Scope Z_scope.

Ltac sic_md := cbv [HEAD FLAGS TIME OS EXLEN EXTRA NAME COMMENT HCRC DICTID DICT Zlib.proof.inflate.Model.TYPE TYPEDO
  STORED COPY_ COPY TABLE LENLENS CODELENS LEN_ LEN LENEXT DIST DISTEXT MATCH LIT CHECK LENGTH DONE BAD MEM SYNC
  Z_OK Z_STREAM_END Z_NEED_DICT Z_STREAM_ERROR Z_DATA_ERROR Z_MEM_ERROR Z_BUF_ERROR Z_FINISH Z_BLOCK Z_TREES
  hdr_mode data_mode post_mode win_mode decode_mode len_live off_live ext_live] in *; lia.

(* ---------------------------------------------------------------------------------------------- *)
(* Traces                                                                                         *)

Lemma sic_areach_trans src I R a b c : areach src I R a b -> areach src I R b c -> areach src I R a c.
Proof.
  intros H; revert c; induction H as [a | a n w a1 a' E N H IH]; intros c Hc; [exact Hc|].
  eapply ar_step; [exact E | exact N | apply IH; exact Hc].
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The prologue: TYPE -> TYPEDO is the abstract free step a_TYPE                                  *)

Lemma sic_astep_type src a : a_mode a = Zlib.proof.inflate.Model.TYPE ->
  astep lenfix_list distfix_list src a = AGo (a_q a) false (AS (set_i_mode (a_s a) TYPEDO) (a_q a) (a_O a)).
Proof. intros E. unfold astep. rewrite E. reflexivity. Qed.

Lemma sic_seq_typedo s t : seq s t -> i_mode t = Zlib.proof.inflate.Model.TYPE ->
  seq (set_i_mode s TYPEDO) (set_i_mode t TYPEDO).
Proof.
  intros H E. destruct H; constructor; cbn; auto; intros L; exfalso; sic_md.
Qed.

(* the abstract state at the first loop head *)
Definition sic_a0 (a: ast) : ast :=
  if a_mode a =? Zlib.proof.inflate.Model.TYPE then AS (set_i_mode (a_s a) TYPEDO) (a_q a) (a_O a) else a.

Lemma sic_init src P O z L inp a :
  awf src a -> brel src P O (l_s L) a -> zf_ok z -> zf_tout z = u64 (Zlength O) ->
  0 <= P -> P + Zlength inp <= Zlength src -> inp = sublist P (P + Zlength inp) src ->
  areach src (P + Zlength inp) (Zlength O + zf_ao z) a (sic_a0 a) /\ rel src P O (m_init z L inp) (sic_a0 a).
Proof.
  intros W B Z T P0 PL IE.
  destruct B as [BP BB BM BQ BK BH BO BS BC BT BW BHd].
  destruct Z as (Z1 & Z2 & _).
  pose proof (aw_src _ _ W) as Src. pose proof (aw_mode _ _ W) as Md.
  unfold sic_a0, m_init. rewrite <- BM.
  destruct (Z.eqb_spec (i_mode (l_s L)) Zlib.proof.inflate.Model.TYPE) as [Ty|Ty].
  - split.
    + eapply ar_step; [apply sic_astep_type; congruence| |apply ar_refl].
      cbn. intros [X|[X _]]; [|discriminate].
      rewrite BQ in X by (rewrite Ty; sic_md). pose proof (Zlength_nonneg inp); lia.
    + constructor; cbn [m_s m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave m_tout a_s a_q a_O].
      * constructor; cbn; auto; try lia.
        -- pose proof (Zlength_nonneg inp); lia.
        -- unfold mq; cbn. rewrite BH. f_equal; lia.
      * unfold m_mode, a_mode; cbn. reflexivity.
      * intros _. unfold mq; cbn. rewrite BQ by (rewrite Ty; sic_md). lia.
      * unfold bits_ok; cbn. repeat split; intros; exfalso; sic_md.
      * rewrite app_nil_r. exact BO.
      * rewrite ?Zlength_nil. lia.
      * reflexivity.
      * unfold m_left; cbn. rewrite ?Zlength_nil. repeat split; try lia.
      * reflexivity.
      * intros _. apply sic_seq_typedo; [apply BS; rewrite Ty; sic_md | unfold a_mode in BM; congruence].
      * unfold m_mode; cbn. split; [intros; exfalso; sic_md|].
        intros _ Wr. apply BC; [rewrite Ty; sic_md | exact Wr].
      * unfold m_mode; cbn. split; [intros; apply BT; rewrite Ty; sic_md | intros; exfalso; sic_md].
      * unfold m_left; cbn. rewrite T, ?Zlength_nil. f_equal; lia.
      * intros _. specialize (BW ltac:(rewrite Ty; sic_md)). exact BW.
      * exact BHd.
  - split; [apply ar_refl|].
    constructor; cbn [m_s m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave m_tout a_s a_q a_O].
    + constructor; cbn; auto; try lia.
      * pose proof (Zlength_nonneg inp); lia.
      * unfold mq; cbn. rewrite BH. f_equal; lia.
    + unfold m_mode, a_mode; cbn. exact BM.
    + intros N. unfold mq; cbn. rewrite BQ by exact N. lia.
    + exact BK.
    + rewrite app_nil_r. exact BO.
    + rewrite ?Zlength_nil. lia.
    + reflexivity.
    + unfold m_left; cbn. rewrite ?Zlength_nil. repeat split; try lia.
    + reflexivity.
    + exact BS.
    + exact BC.
    + unfold m_mode; cbn. split; [intros; apply BT; intros E; rewrite E in *; sic_md|].
      intros; rewrite BO; apply BT; intros E; rewrite E in *; sic_md.
    + unfold m_left; cbn. rewrite T, ?Zlength_nil. f_equal; lia.
    + exact BW.
    + exact BHd.
Qed.

Lemma sic_awf_reach (AW: awf_stmt) src I R a a' : areach src I R a a' -> awf src a -> awf src a'.
Proof.
  intros H; induction H as [a | a n w a1 a' E N H IH]; intros W; [exact W|].
  apply IH. destruct AW as (_ & AW2 & _). eapply AW2; [exact W | exact E].
Qed.

Lemma sic_init_awf (AW: awf_stmt) src a : awf src a -> awf src (sic_a0 a).
Proof.
  intros W. unfold sic_a0. destruct (Z.eqb_spec (a_mode a) Zlib.proof.inflate.Model.TYPE) as [Ty|Ty]; [|exact W].
  destruct AW as (_ & AW2 & _). eapply AW2; [exact W | apply (sic_astep_type src a Ty)].
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The loop                                                                                       *)

Ltac sic_dsolve := first [reflexivity | left; sic_dsolve | right; sic_dsolve].

(* every mode of the abstract trace is in one group of the simulation *)
Lemma sic_cover md : HEAD <= md <= BAD -> md_hdr md \/ md_block md \/ md_tab md \/ decode_mode md.
Proof.
  intros H.
  assert (exists n, (n < 30)%nat /\ md = 16180 + Z.of_nat n) as (n & Hn & ->)
    by (exists (Z.to_nat (md - 16180)); cbv [HEAD BAD] in H; lia).
  unfold md_hdr, hdr_mode, md_block, md_tab, decode_mode.
  do 30 (destruct n as [|n]; [cbv; sic_dsolve|]). exfalso; clear -Hn; lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The only return from the loop: DICT's Z_NEED_DICT, after RESTORE                                *)

Ltac sic_brk := repeat (cbv beta iota zeta; match goal with
  | |- context [if ?c then _ else _] => destruct c
  | |- context [match ?x with pair _ _ => _ end] => destruct x
  end).

Lemma sic_hcrc_brk m : exists m', c_HCRC m = IBrk m'.
Proof. unfold c_HCRC. sic_brk; eexists; reflexivity. Qed.
Lemma sic_comment_brk m : exists m', c_COMMENT2 m = IBrk m'.
Proof. unfold c_COMMENT2. sic_brk; first [eexists; reflexivity | apply sic_hcrc_brk]. Qed.
Lemma sic_name_brk m : exists m', c_NAME2 m = IBrk m'.
Proof. unfold c_NAME2. sic_brk; first [eexists; reflexivity | apply sic_comment_brk]. Qed.
Lemma sic_extra_brk m : exists m', c_EXTRA2 m = IBrk m'.
Proof. unfold c_EXTRA2. sic_brk; first [eexists; reflexivity | apply sic_name_brk]. Qed.
Lemma sic_exlen_brk m : exists m', c_EXLEN2 m = IBrk m'.
Proof. unfold c_EXLEN2. sic_brk; first [eexists; reflexivity | apply sic_extra_brk]. Qed.
Lemma sic_os_brk m : exists m', c_OS2 m = IBrk m'.
Proof. unfold c_OS2. sic_brk; first [eexists; reflexivity | apply sic_exlen_brk]. Qed.
Lemma sic_time_brk m : exists m', c_TIME2 m = IBrk m'.
Proof. unfold c_TIME2. sic_brk; first [eexists; reflexivity | apply sic_os_brk]. Qed.
Lemma sic_flags_brk m : exists m', c_FLAGS2 m = IBrk m'.
Proof. unfold c_FLAGS2. sic_brk; first [eexists; reflexivity | apply sic_time_brk]. Qed.
Lemma sic_head_brk m : exists m', c_HEAD2 m = IBrk m'.
Proof. unfold c_HEAD2. sic_brk; eexists; reflexivity. Qed.
Lemma sic_type_brk flush m : exists m', c_TYPE flush m = IBrk m'.
Proof. unfold c_TYPE, c_TYPEDO. sic_brk; eexists; reflexivity. Qed.

Lemma sic_dict_ret flush m r m' : c_DICT flush m = IRet r m' ->
  i_bits (m_s m') = m_bits m' /\ i_hold (m_s m') = m_hold m' /\ m_mode m' = m_mode m.
Proof.
  unfold c_DICT. destruct (i_havedict (m_s m) =? 0).
  - intros E; inversion E; subst. split; [|split]; reflexivity.
  - destruct (sic_type_brk flush (set_mode (set_m_adler (upd_s m (fun s => set_i_check s 1)) 1) Zlib.proof.inflate.Model.TYPE))
      as [m2 E2]. rewrite E2. discriminate.
Qed.

Lemma sic_ret_restore flush m r m' : HEAD <= m_mode m <= DICT ->
  stepf2 flush lenfix_list distfix_list m = IRet r m' ->
  i_bits (m_s m') = m_bits m' /\ i_hold (m_s m') = m_hold m' /\ m_mode m' = DICT.
Proof.
  intros H.
  assert (exists n, (n < 11)%nat /\ m_mode m = 16180 + Z.of_nat n) as (n & Hn & E)
    by (exists (Z.to_nat (m_mode m - 16180)); cbv [HEAD DICT] in H; lia).
  unfold stepf2, step2. rewrite E.
  destruct n as [|[|[|[|[|[|[|[|[|[|[|n]]]]]]]]]]];
    [ .. | exfalso; clear -Hn; lia];
    cbn -[c_HEAD2 c_FLAGS2 c_TIME2 c_OS2 c_EXLEN2 c_EXTRA2 c_NAME2 c_COMMENT2 c_HCRC c_DICTID c_DICT];
    [ destruct (sic_head_brk m) as [? ->]; discriminate
    | destruct (sic_flags_brk m) as [? ->]; discriminate
    | destruct (sic_time_brk m) as [? ->]; discriminate
    | destruct (sic_os_brk m) as [? ->]; discriminate
    | destruct (sic_exlen_brk m) as [? ->]; discriminate
    | destruct (sic_extra_brk m) as [? ->]; discriminate
    | destruct (sic_name_brk m) as [? ->]; discriminate
    | destruct (sic_comment_brk m) as [? ->]; discriminate
    | destruct (sic_hcrc_brk m) as [? ->]; discriminate
    | unfold c_DICTID; destruct (m_leave _ =? 1); [discriminate|];
      intros E'; destruct (sic_dict_ret _ _ _ _ E') as (A1 & A2 & A3); rewrite A3; auto
    | intros E'; destruct (sic_dict_ret _ _ _ _ E') as (A1 & A2 & A3); rewrite A3, E; auto ].
Qed.

Section Loop.
Variables (AW: awf_stmt) (S1: sim_ok md_hdr) (S2: sim_ok md_block) (S3: sim_ok md_tab) (S4: sim_ok decode_mode).
Variables (flush: Z) (src: list Z) (P: Z) (O inp: list Z) (ao: Z).

(* the facts kept at every loop head *)
Definition sic_head (m: mst) (a: ast) : Prop :=
  rel src P O m a /\ awf src a /\ m_inp m = inp /\ m_aout m = ao /\ (i_wsize (m_s m) = 0 -> i_wdata (m_s m) = []).

(* where the loop ends *)
Definition sic_end (a: ast) (o: iout) : Prop :=
  match o with
  | IRet r m' => r = Z_NEED_DICT /\ sic_head m' a /\ astep lenfix_list distfix_list src a = AEnd Z_NEED_DICT /\
                 m_snx m' = m_nx m' /\ m_sow m' = Zlength (m_ow m') /\
                 i_bits (m_s m') = m_bits m' /\ i_hold (m_s m') = m_hold m' /\ m_mode m' = DICT
  | IBrk m' => m_leave m' = 1 /\ sic_head m' a /\ stop_ok flush src (P + Zlength inp) (Zlength O + ao) m' a
  end.

Lemma sic_loop m o : loop2 flush lenfix_list distfix_list m o -> forall a, sic_head m a -> m_leave m = 0 ->
  exists a', areach src (P + Zlength inp) (Zlength O + ao) a a' /\ sic_end a' o.
Proof.
  intros LP. induction LP as [m r m' E | m m' E L1 | m m' o E L1 LP IH]; intros a (R & W & Hi & Ha & Hw) L0.
  all: pose proof (aw_mode _ _ W) as Md.
  all: assert (Sim: forall Q, sim_ok Q -> Q (m_mode m) ->
         match stepf2 flush lenfix_list distfix_list m with
         | IBrk m' => exists a', areach src (P + Zlength inp) (Zlength O + ao) a a' /\
                   rel src P O m' a' /\ (m_leave m' = 1 -> stop_ok flush src (P + Zlength inp) (Zlength O + ao) m' a')
         | IRet r m' => r = Z_NEED_DICT /\
                   exists a', areach src (P + Zlength inp) (Zlength O + ao) a a' /\
                   rel src P O m' a' /\ astep lenfix_list distfix_list src a' = AEnd Z_NEED_DICT
         end) by (intros Q SQ HQ; rewrite <- Hi, <- Ha; apply SQ; auto).
  all: assert (Step: match stepf2 flush lenfix_list distfix_list m with
         | IBrk m' => exists a', areach src (P + Zlength inp) (Zlength O + ao) a a' /\
                   rel src P O m' a' /\ (m_leave m' = 1 -> stop_ok flush src (P + Zlength inp) (Zlength O + ao) m' a')
         | IRet r m' => r = Z_NEED_DICT /\
                   exists a', areach src (P + Zlength inp) (Zlength O + ao) a a' /\
                   rel src P O m' a' /\ astep lenfix_list distfix_list src a' = AEnd Z_NEED_DICT
         end)
       by (rewrite (rl_mode _ _ _ _ _ R) in Sim;
           destruct (sic_cover (a_mode a) Md) as [G|[G|[G|G]]]; [apply (Sim _ S1) | apply (Sim _ S2) | apply (Sim _ S3) | apply (Sim _ S4)];
           exact G).
  all: assert (Fr: IBStepKit.tgood m (stepf2 flush lenfix_list distfix_list m))
         by (destruct (rl_bb _ _ _ _ _ R); destruct (rl_out _ _ _ _ _ R) as (O1 & _); pose proof (rl_aout _ _ _ _ _ R);
             apply IBStepKit.stepf2_tgood; unfold IBStepKit.md_rng, m_left in *;
             [rewrite (rl_mode _ _ _ _ _ R); exact Md | lia | cbv [Int.max_unsigned Int.modulus Int.wordsize Wordsize_32.wordsize two_power_nat] in *; cbn in *; lia]).
  all: pose proof (DecCallWkeepKit.stepf2_wkrel flush lenfix_list distfix_list m) as Wk.
  all: pose proof (SICallLeave.si_call_leave flush lenfix_list distfix_list m) as Lv.
  all: rewrite E in Step, Fr, Wk, Lv.
  - destruct Step as (-> & a' & Ra & R' & Ae). destruct Fr as (_ & Fr).
    destruct Fr as (Hd & F1 & F2 & _ & F4 & F5 & _).
    pose proof (sic_ret_restore flush m _ m' Hd E) as (Rb & Rh & Rm).
    exists a'. split; [exact Ra|]. split; [reflexivity|].
    split; [|split; [exact Ae | split; [exact F4 | split; [exact F5 | split; [exact Rb | split; [exact Rh | exact Rm]]]]]].
    split; [exact R'|]. split; [eapply sic_awf_reach; eauto|]. split; [congruence|]. split; [congruence|].
    unfold DecCallWkeepKit.wkrel, DecCallWkeepKit.wf5 in Wk. intros Z0. destruct Wk as (K1 & _ & _ & K4 & _).
    rewrite K4. apply Hw. congruence.
  - destruct Step as (a' & Ra & R' & St). destruct Fr as (F1 & F2 & _).
    exists a'. split; [exact Ra|]. split; [exact L1|]. split; [|apply St; exact L1].
    split; [exact R'|]. split; [eapply sic_awf_reach; eauto|]. split; [congruence|]. split; [congruence|].
    unfold DecCallWkeepKit.wkrel, DecCallWkeepKit.wf5 in Wk. intros Z0. destruct Wk as (K1 & _ & _ & K4 & _).
    rewrite K4. apply Hw. congruence.
  - destruct Step as (a1 & Ra & R' & _). destruct Fr as (F1 & F2 & _).
    assert (L': m_leave m' = 0) by (destruct Lv as [Lv|Lv]; congruence).
    destruct (IH a1) as (a' & Ra' & En); [|exact L'|].
    + split; [exact R'|]. split; [eapply sic_awf_reach; eauto|]. split; [congruence|]. split; [congruence|].
      unfold DecCallWkeepKit.wkrel, DecCallWkeepKit.wf5 in Wk. intros Z0. destruct Wk as (K1 & _ & _ & K4 & _).
      rewrite K4. apply Hw. congruence.
    + exists a'. split; [eapply sic_areach_trans; eauto | exact En].
Qed.

End Loop.

(* ---------------------------------------------------------------------------------------------- *)
(* inf_leave                                                                                      *)

(* the istate without the fields inf_leave writes (window, total, check, hold, bits) *)
Definition sic_core (s: istate) : istate :=
  IS (i_mode s) (i_last s) (i_wrap s) (i_havedict s) (i_flags s) (i_dmax s) 0 0 (i_head s) (i_wbits s)
     0 0 0 false [] 0 0 (i_length s) (i_offset s) (i_extra s) (i_lencode s) (i_distcode s) (i_lenbits s)
     (i_distbits s) (i_ncode s) (i_nlen s) (i_ndist s) (i_have s) (i_next s) (i_lens s) (i_codes s)
     (i_sane s) (i_back s) (i_was s).

(* the window fields *)
Definition sic_win (s: istate) : Z * Z * Z * list Z * bool := (i_wsize s, i_whave s, i_wnext s, i_wdata s, i_win s).

Lemma sic_uw_core s d : sic_core (updatewindow s d) = sic_core s.
Proof. unfold updatewindow. cbv zeta. repeat match goal with |- context [if ?c then _ else _] => destruct c end; reflexivity. Qed.

Lemma sic_uw_keep s d : i_check (updatewindow s d) = i_check s /\ i_total (updatewindow s d) = i_total s /\
  i_hold (updatewindow s d) = i_hold s /\ i_bits (updatewindow s d) = i_bits s.
Proof. unfold updatewindow. cbv zeta. repeat match goal with |- context [if ?c then _ else _] => destruct c end; repeat split. Qed.

Lemma sic_swin_ext s t O : swin_ok s O -> sic_win s = sic_win t -> swin_ok t O.
Proof.
  unfold sic_win. intros H E. inversion E as [[E1 E2 E3 E4 E5]].
  unfold swin_ok, swin_at in *. rewrite <- E1, <- E2, <- E3, <- E4, <- E5. exact H.
Qed.

(* the bytes inf_leave adds to the window and the check *)
Definition sic_data (m: mst) : list Z :=
  sublist (Zlength (m_ow m) - u32 (m_out m - m_left m)) (Zlength (m_ow m)) (m_ow m).

(* leave_fin in three stages: RESTORE and the window, the counters, the check value *)
Definition sic_w (flush: Z) (m: mst) : mst :=
  let m1 := restore m in
  if leave_ok flush m then
    upd_s m1 (fun s => set_i_win (updatewindow s (sublist (Zlength (m_ow m1) - u32 (m_out m1 - m_left m1))
                                                     (Zlength (m_ow m1)) (m_ow m1))) true)
  else m1.

Definition sic_t (m: mst) : mst :=
  let inn := u32 (m_in m - m_have m) in
  let out := u32 (m_out m - m_left m) in
  let m := set_m_tout (set_m_tin m (u64 (m_tin m + inn))) (u64 (m_tout m + out)) in
  upd_s m (fun s => set_i_total s (u64 (i_total s + out))).

Definition sic_c (out: Z) (m: mst) : mst :=
  if (negb (Z.land (i_wrap (m_s m)) 4 =? 0) && negb (out =? 0))%bool then
    let c := update_check (i_flags (m_s m)) (i_check (m_s m))
               (sublist (Zlength (m_ow m) - out) (Zlength (m_ow m)) (m_ow m)) in
    set_m_adler (upd_s m (fun s => set_i_check s c)) c
  else m.

Lemma sic_fin_eq flush m :
  r_m (leave_fin flush m) = sic_c (u32 (m_out (sic_w flush m) - m_left (sic_w flush m))) (sic_t (sic_w flush m)).
Proof. reflexivity. Qed.

Lemma sic_fin_ret flush m :
  r_ret (leave_fin flush m) =
    (let mw := sic_w flush m in let mc := sic_c (u32 (m_out mw - m_left mw)) (sic_t mw) in
     if ((((u32 (m_in mw - m_have mw) =? 0) && (u32 (m_out mw - m_left mw) =? 0)) || (flush =? Z_FINISH)) &&
         (m_ret mc =? Z_OK))%bool
     then Z_BUF_ERROR else m_ret mc).
Proof. reflexivity. Qed.

Lemma sic_w_fields flush m : let m' := sic_w flush m in
  m_inp m' = m_inp m /\ m_aout m' = m_aout m /\ m_ow m' = m_ow m /\ m_nx m' = m_nx m /\ m_bits m' = m_bits m /\
  m_in m' = m_in m /\ m_out m' = m_out m /\ m_tin m' = m_tin m /\ m_tout m' = m_tout m /\ m_ret m' = m_ret m /\
  m_snx m' = m_nx m /\ m_sow m' = Zlength (m_ow m) /\
  sic_core (m_s m') = sic_core (m_s m) /\ i_bits (m_s m') = m_bits m /\ i_hold (m_s m') = m_hold m /\
  i_total (m_s m') = i_total (m_s m) /\ i_check (m_s m') = i_check (m_s m) /\
  (leave_ok flush m = true -> sic_win (m_s m') =
     sic_win (set_i_win (updatewindow (set_i_bits (set_i_hold (m_s m) (m_hold m)) (m_bits m)) (sic_data m)) true)) /\
  (leave_ok flush m = false -> sic_win (m_s m') = sic_win (m_s m)).
Proof.
  unfold sic_w. cbv zeta. destruct (leave_ok flush m) eqn:U.
  - set (d := sublist _ _ _).
    set (s1 := set_i_bits (set_i_hold (m_s m) (m_hold m)) (m_bits m)).
    pose proof (sic_uw_core s1 d) as UC. destruct (sic_uw_keep s1 d) as (K1 & K2 & K3 & K4).
    cbn [m_inp m_aout m_ow m_nx m_bits m_in m_out m_tin m_tout m_snx m_sow m_s restore upd_s set_m_s set_m_sow set_m_snx].
    fold s1. cbn [i_bits i_hold i_total i_check set_i_win].
    rewrite K1, K2, K3, K4. unfold sic_win, sic_data. cbn [i_wsize i_whave i_wnext i_wdata i_win set_i_win].
    repeat split; try reflexivity; try discriminate.
    transitivity (sic_core s1); [exact UC | reflexivity].
  - cbn. repeat split; try reflexivity; discriminate.
Qed.

Lemma sic_t_fields m : let m' := sic_t m in
  m_inp m' = m_inp m /\ m_aout m' = m_aout m /\ m_ow m' = m_ow m /\ m_nx m' = m_nx m /\ m_bits m' = m_bits m /\
  m_out m' = m_out m /\ m_snx m' = m_snx m /\ m_sow m' = m_sow m /\ m_ret m' = m_ret m /\
  m_tout m' = u64 (m_tout m + u32 (m_out m - m_left m)) /\
  sic_core (m_s m') = sic_core (m_s m) /\ i_bits (m_s m') = i_bits (m_s m) /\ i_hold (m_s m') = i_hold (m_s m) /\
  i_total (m_s m') = u64 (i_total (m_s m) + u32 (m_out m - m_left m)) /\ i_check (m_s m') = i_check (m_s m) /\
  sic_win (m_s m') = sic_win (m_s m).
Proof. cbn. repeat split; reflexivity. Qed.

Lemma sic_c_fields out m : let m' := sic_c out m in
  m_inp m' = m_inp m /\ m_aout m' = m_aout m /\ m_ow m' = m_ow m /\ m_nx m' = m_nx m /\ m_bits m' = m_bits m /\
  m_snx m' = m_snx m /\ m_sow m' = m_sow m /\ m_tout m' = m_tout m /\ m_ret m' = m_ret m /\
  sic_core (m_s m') = sic_core (m_s m) /\ i_bits (m_s m') = i_bits (m_s m) /\ i_hold (m_s m') = i_hold (m_s m) /\
  i_total (m_s m') = i_total (m_s m) /\
  i_check (m_s m') = (if (negb (Z.land (i_wrap (m_s m)) 4 =? 0) && negb (out =? 0))%bool
                      then update_check (i_flags (m_s m)) (i_check (m_s m))
                             (sublist (Zlength (m_ow m) - out) (Zlength (m_ow m)) (m_ow m))
                      else i_check (m_s m)) /\
  sic_win (m_s m') = sic_win (m_s m).
Proof. unfold sic_c. destruct (_ && _)%bool; cbn; repeat split; reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The boundary relation after the call                                                           *)

Lemma sic_seq_core s s' t : sic_core s' = sic_core s -> seq s t -> seq s' t.
Proof.
  intros E H. destruct H; constructor;
    repeat match goal with
    | |- ?f s' = ?g => transitivity (f s); [exact (f_equal f E) | assumption]
    | |- _ -> ?f s' = ?g => intros X; transitivity (f s); [exact (f_equal f E) | auto]
    end.
Qed.

Lemma sic_bits_ok_core s s' b : sic_core s' = sic_core s -> bits_ok s b -> bits_ok s' b.
Proof.
  intros E. unfold bits_ok.
  rewrite (f_equal i_mode E : i_mode s' = i_mode s), (f_equal i_flags E : i_flags s' = i_flags s). auto.
Qed.

Lemma sic_brel src P O m a s' : rel src P O m a ->
  sic_core s' = sic_core (m_s m) -> i_bits s' = m_bits m -> i_hold s' = m_hold m ->
  (i_mode s' <> BAD -> i_total s' = u64 (Zlength (O ++ m_ow m))) ->
  (hdr_mode (i_mode s') -> i_check s' = i_check (a_s a)) ->
  (data_mode (i_mode s') -> i_wrap s' <> 0 -> i_check s' = update_check (i_flags (a_s a)) (i_check (a_s a)) (O ++ m_ow m)) ->
  (win_mode (i_mode s') -> swin_ok s' (O ++ m_ow m)) ->
  brel src (P + m_nx m) (O ++ m_ow m) s' a.
Proof.
  intros R C Bi Ho Tt Ch Cd Wn.
  pose proof (f_equal i_mode C : i_mode s' = i_mode (m_s m)) as Md.
  destruct (rl_bb _ _ _ _ _ R) as [Src HP [HI _] HN [HB1 HB2] HH].
  constructor.
  - lia.
  - rewrite Bi. lia.
  - rewrite Md. exact (rl_mode _ _ _ _ _ R).
  - intros N. rewrite Bi. rewrite Md in N. rewrite (rl_q _ _ _ _ _ R N). unfold mq. lia.
  - rewrite Bi. eapply sic_bits_ok_core; [exact C | exact (rl_bits _ _ _ _ _ R)].
  - rewrite Bi, Ho, HH. unfold mq. f_equal; lia.
  - exact (rl_O _ _ _ _ _ R).
  - intros N. rewrite Md in N. eapply sic_seq_core; [exact C | exact (rl_s _ _ _ _ _ R N)].
  - split; [exact Ch | exact Cd].
  - exact Tt.
  - exact Wn.
  - rewrite (f_equal i_head C : i_head s' = i_head (m_s m)). exact (rl_head _ _ _ _ _ R).
Qed.

(* the modes of the trace but BAD: header, data or trailer *)
Lemma sic_modes md : HEAD <= md <= BAD -> md <> BAD -> hdr_mode md \/ data_mode md \/ post_mode md.
Proof.
  intros H N.
  assert (exists n, (n < 30)%nat /\ md = 16180 + Z.of_nat n) as (n & Hn & ->)
    by (exists (Z.to_nat (md - 16180)); cbv [HEAD BAD] in H; lia).
  unfold hdr_mode, data_mode, post_mode, decode_mode.
  do 30 (destruct n as [|n]; [cbv in N |- *; first [sic_dsolve | exfalso; apply N; reflexivity]|]).
  exfalso; clear -Hn; lia.
Qed.

Lemma sic_adler_valid1 : Zlib.proof.adler32.Model.adler_valid 1.
Proof. unfold Zlib.proof.adler32.Model.adler_valid. vm_compute. repeat split; discriminate. Qed.

(* the check of the call's bytes continues the check of the earlier output *)
Lemma sic_upd_app f c O d : (f = 0 /\ c = 1) \/ (f <> 0 /\ c = 0) -> bytes_ok O ->
  update_check f (update_check f c O) d = update_check f c (O ++ d).
Proof.
  intros [[-> ->]|[F ->]] B; unfold update_check.
  - rewrite Z.eqb_refl.
    rewrite (Zlib.proof.adler32.Model.adler32_z_val_ref 1 O sic_adler_valid1).
    rewrite (Zlib.proof.adler32.Model.adler32_z_val_ref 1 (O ++ d) sic_adler_valid1).
    rewrite Zlib.proof.adler32.Model.adler32_z_val_ref
      by (apply Zlib.proof.adler32.Model.ref_adler32_valid; exact sic_adler_valid1).
    apply Zlib.proof.adler32.Model.ref_adler32_app. exact sic_adler_valid1.
  - destruct (Z.eqb_spec f 0); [contradiction|].
    apply Zlib.proof.crc32.Combine.ref_crc32_app. exact B.
Qed.

Lemma sic_u64_back X d : u64 (u64 (X - d) + d) = u64 X.
Proof. unfold u64. rewrite Zplus_mod_idemp_l. f_equal. lia. Qed.

Lemma sic_u32_small x : 0 <= x <= Int.max_unsigned -> u32 x = x.
Proof. intros H. unfold u32. apply Z.mod_small. change Int.max_unsigned with (2 ^ 32 - 1) in H. lia. Qed.

(* the conclusion of call_stmt for a final machine m and return value r *)
Definition sic_post (src: list Z) (flush P: Z) (O inp: list Z) (ao: Z) (a: ast) (r: Z) (m: mst) : Prop :=
  let I := P + Zlength inp in let R := Zlength O + ao in
  m_inp m = inp /\ m_aout m = ao /\ 0 <= m_snx m <= Zlength inp /\ m_sow m = Zlength (m_ow m) /\
  Zlength (m_ow m) <= ao /\ m_tout m = u64 (Zlength O + Zlength (m_ow m)) /\
  exists a', areach src I R a a' /\ awf src a' /\ brel src (P + m_snx m) (O ++ m_ow m) (m_s m) a' /\
    (final_code r = true -> astep lenfix_list distfix_list src a' = AEnd r) /\
    (final_code r = false -> (r = Z_OK \/ r = Z_BUF_ERROR) /\
       (flush = Z_BLOCK \/ flush = Z_TREES \/ ablocked src I R a' (astep lenfix_list distfix_list src a'))).

(* DICT's return: the header is all the output so far, nothing was written *)
Lemma sic_ret_case src flush P O inp ao a a' m :
  areach src (P + Zlength inp) (Zlength O + ao) a a' -> sic_head src P O inp ao m a' ->
  astep lenfix_list distfix_list src a' = AEnd Z_NEED_DICT ->
  m_snx m = m_nx m -> m_sow m = Zlength (m_ow m) -> i_bits (m_s m) = m_bits m -> i_hold (m_s m) = m_hold m ->
  m_mode m = DICT -> sic_post src flush P O inp ao a Z_NEED_DICT m.
Proof.
  intros Ra (R & W & Hi & Ha & _) Ae Sx Sw Bi Ho Md.
  assert (Hd: hdr_mode (m_mode m)) by (rewrite Md; unfold hdr_mode; tauto).
  pose proof (rl_O _ _ _ _ _ R) as RO. rewrite (aw_hdrO _ _ W) in RO by (rewrite <- (rl_mode _ _ _ _ _ R); exact Hd).
  symmetry in RO. apply app_eq_nil in RO as [O0 Ow].
  destruct (rl_out _ _ _ _ _ R) as (_ & _ & Ou). specialize (Ou (or_introl Hd)).
  pose proof (rl_aout _ _ _ _ _ R) as Ao. destruct (rl_bb _ _ _ _ _ R) as [_ _ _ HN _ _].
  unfold sic_post. split; [exact Hi|]. split; [exact Ha|]. split; [rewrite Sx, <- Hi; lia|].
  split; [exact Sw|]. split; [rewrite <- Ha; lia|].
  split; [rewrite (rl_tout _ _ _ _ _ R); unfold m_left; rewrite Ou, Ow, O0; f_equal; rewrite Zlength_nil; lia|].
  exists a'. split; [exact Ra|]. split; [exact W|]. split.
  - rewrite Sx. apply sic_brel; auto.
    + intros _. destruct (rl_tot _ _ _ _ _ R) as (T1 & _). rewrite (T1 (or_introl Hd)), Ow, app_nil_r. reflexivity.
    + intros H. exact (proj1 (rl_chk _ _ _ _ _ R) H).
    + intros H. exfalso. fold (m_mode m) in H. rewrite Md in H. sic_md.
    + intros H. rewrite Ow, app_nil_r. exact (rl_win _ _ _ _ _ R H).
  - split; [intros _; exact Ae | intros F; discriminate F].
Qed.

Lemma sic_astep_done src a : a_mode a = DONE -> astep lenfix_list distfix_list src a = AEnd Z_STREAM_END.
Proof. intros E. unfold astep. rewrite E. reflexivity. Qed.
Lemma sic_astep_bad src a : a_mode a = BAD -> astep lenfix_list distfix_list src a = AEnd Z_DATA_ERROR.
Proof. intros E. unfold astep. rewrite E. reflexivity. Qed.

(* the wrap values of the trace (raw, zlib, gzip, auto) have bit 2 set unless raw *)
Lemma sic_wrap4 w : w = 0 \/ w = 5 \/ w = 6 \/ w = 7 -> w <> 0 -> Z.land w 4 <> 0.
Proof. intros [-> | [-> | [-> | ->]]] N; [contradiction | discriminate | discriminate | discriminate]. Qed.

(* the end of the call at a stop: inf_leave's restore, window, counters and check *)
Lemma sic_leave_case src flush P O inp ao a a' m :
  areach src (P + Zlength inp) (Zlength O + ao) a a' -> sic_head src P O inp ao m a' ->
  stop_ok flush src (P + Zlength inp) (Zlength O + ao) m a' ->
  sic_post src flush P O inp ao a (r_ret (leave_fin flush m)) (r_m (leave_fin flush m)).
Proof.
  intros Ra (R & W & Hi & Ha & Hw) St.
  destruct (sic_w_fields flush m)
    as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11 & W12 & W13 & W14 & W15 & W16 & W17 & W18 & W19).
  set (mw := sic_w flush m) in *.
  destruct (sic_t_fields mw) as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9 & T10 & T11 & T12 & T13 & T14 & T15 & T16).
  set (dd := u32 (m_out mw - m_left mw)) in *.
  destruct (sic_c_fields dd (sic_t mw)) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14 & C15).
  rewrite sic_fin_ret, sic_fin_eq. cbv zeta. fold mw dd.
  set (mc := sic_c dd (sic_t mw)) in *.
  (* the numbers *)
  destruct (rl_out _ _ _ _ _ R) as (Ou1 & Ou2 & Ou3).
  pose proof (rl_aout _ _ _ _ _ R) as Ao.
  destruct (rl_bb _ _ _ _ _ R) as [Src HP [HI _] HN HB HH].
  assert (Lw: m_left mw = m_left m) by (unfold m_left; rewrite W2, W3; reflexivity).
  assert (Dd: dd = m_out m - m_left m)
    by (unfold dd; rewrite W7, Lw; apply sic_u32_small; unfold m_left in *; pose proof (Zlength_nonneg (m_ow m)); lia).
  assert (Mc: i_mode (m_s mc) = m_mode m) by (exact (f_equal i_mode (eq_trans C10 (eq_trans T11 W13)))).
  assert (Fc: i_flags (m_s (sic_t mw)) = i_flags (m_s m)) by (exact (f_equal i_flags (eq_trans T11 W13))).
  assert (Wc: i_wrap (m_s (sic_t mw)) = i_wrap (m_s m)) by (exact (f_equal i_wrap (eq_trans T11 W13))).
  assert (Wc': i_wrap (m_s mc) = i_wrap (m_s m)) by (exact (f_equal i_wrap (eq_trans C10 (eq_trans T11 W13)))).
  pose proof (aw_mode _ _ W) as AM. rewrite <- (rl_mode _ _ _ _ _ R) in AM.
  (* in the header and data modes (and a raw trailer) the call wrote |ow| bytes since the last update *)
  assert (Dow: hdr_mode (m_mode m) \/ data_mode (m_mode m) \/ (post_mode (m_mode m) /\ i_wrap (m_s m) = 0) ->
               m_out m - m_left m = Zlength (m_ow m))
    by (intros X; rewrite (Ou3 X); unfold m_left; lia).
  assert (Ob: bytes_ok O /\ bytes_ok (m_ow m)).
  { pose proof (aw_O _ _ W) as B. rewrite (rl_O _ _ _ _ _ R) in B. unfold bytes_ok in B. apply Forall_app in B. exact B. }
  unfold sic_post. split; [rewrite C1, T1, W1; exact Hi|]. split; [rewrite C2, T2, W2; exact Ha|].
  split; [rewrite C6, T7, W11; rewrite <- Hi; lia|].
  split; [rewrite C7, T8, W12, C3, T3, W3; reflexivity|].
  split; [rewrite C3, T3, W3, <- Ha; lia|].
  split.
  { rewrite C8, T10, C3, T3, W3, W9. fold dd. rewrite Dd, (rl_tout _ _ _ _ _ R). apply sic_u64_back. }
  exists a'. split; [exact Ra|]. split; [exact W|]. split.
  - rewrite C6, T7, W11, C3, T3, W3. apply sic_brel.
    + exact R.
    + exact (eq_trans C10 (eq_trans T11 W13)).
    + rewrite C11, T12. exact W14.
    + rewrite C12, T13. exact W15.
    + (* total *)
      intros N. rewrite Mc in N. rewrite C13, T14. fold dd. rewrite W16, Dd.
      destruct (rl_tot _ _ _ _ _ R) as (Tt1 & Tt2).
      destruct (sic_modes (m_mode m) AM N) as [X|[X|X]].
      * rewrite Tt1, Dow by tauto. rewrite Zlength_app. unfold u64. rewrite Zplus_mod_idemp_l. reflexivity.
      * rewrite Tt1, Dow by tauto. rewrite Zlength_app. unfold u64. rewrite Zplus_mod_idemp_l. reflexivity.
      * destruct (Z.eq_dec (i_wrap (m_s m)) 0) as [Wr|Wr].
        -- rewrite Tt1, Dow by tauto. rewrite Zlength_app. unfold u64. rewrite Zplus_mod_idemp_l. reflexivity.
        -- rewrite (Tt2 X Wr), (Ou2 X Wr), (rl_O _ _ _ _ _ R), Z.sub_diag, Z.add_0_r. unfold u64. apply Zmod_mod.
    + (* check, header *)
      intros X. rewrite Mc in X. rewrite C14. fold dd.
      assert (Ow: m_ow m = []).
      { pose proof (rl_O _ _ _ _ _ R) as RO. rewrite (aw_hdrO _ _ W) in RO by (rewrite <- (rl_mode _ _ _ _ _ R); exact X).
        symmetry in RO. apply app_eq_nil in RO. tauto. }
      assert (D0: dd = 0) by (rewrite Dd, Dow by tauto; rewrite Ow; reflexivity).
      rewrite D0, Bool.andb_false_r, T15, W17. exact (proj1 (rl_chk _ _ _ _ _ R) X).
    + (* check, data *)
      intros X Wr. rewrite Mc in X. rewrite Wc' in Wr. rewrite C14. fold dd. rewrite Wc, Fc, T15, W17, T3, W3.
      assert (N: m_mode m <> BAD) by (intros E; rewrite E in X; sic_md).
      pose proof (rl_s _ _ _ _ _ R N) as Sq.
      assert (Wr': i_wrap (a_s a') <> 0) by (rewrite <- (se_wrap _ _ Sq); exact Wr).
      rewrite (proj2 (rl_chk _ _ _ _ _ R) X Wr). rewrite (se_flags _ _ Sq).
      rewrite Dd, Dow by tauto.
      assert (L4: Z.land (i_wrap (m_s m)) 4 <> 0)
        by (apply sic_wrap4; [rewrite (se_wrap _ _ Sq); exact (aw_wrap _ _ W) | exact Wr]).
      destruct (Z.eqb_spec (Zlength (m_ow m)) 0) as [Z0|Z0].
      * apply Zlength_nil_inv in Z0. rewrite Z0, app_nil_r, Bool.andb_false_r. reflexivity.
      * destruct (Z.eqb_spec (Z.land (i_wrap (m_s m)) 4) 0) as [E4|E4]; [contradiction|]. cbn.
        rewrite Z.sub_diag, sublist_same by reflexivity.
        apply sic_upd_app; [|exact (proj1 Ob)].
        apply (aw_chk _ _ W); [rewrite <- (rl_mode _ _ _ _ _ R); exact X | exact Wr'].
    + (* window *)
      intros X. rewrite Mc in X.
      assert (Wm: hdr_mode (m_mode m) \/ data_mode (m_mode m)) by (destruct X as [X|[X _]]; tauto).
      assert (N: m_mode m <> BAD) by (intros E; rewrite E in X; sic_md).
      pose proof (rl_s _ _ _ _ _ R N) as Sq.
      pose proof (rl_win _ _ _ _ _ R X) as Sw.
      assert (Ew: sic_win (m_s mc) = sic_win (m_s mw)) by (rewrite C15, T16; reflexivity).
      destruct (leave_ok flush m) eqn:U.
      * assert (Ed: sic_data m = m_ow m).
        { unfold sic_data. rewrite sic_u32_small, Dow by (try tauto; unfold m_left in *; lia).
          rewrite Z.sub_diag. apply sublist_same; reflexivity. }
        rewrite Ed in W18. specialize (W18 eq_refl).
        apply (sic_swin_ext (set_i_win (updatewindow (set_i_bits (set_i_hold (m_s m) (m_hold m)) (m_bits m)) (m_ow m)) true));
          [| rewrite Ew, W18; reflexivity].
        apply SICallWin.si_call_win.
        -- exact Sw.
        -- exact Hw.
        -- cbn. rewrite (se_wbits _ _ Sq). exact (aw_wbits _ _ W).
      * assert (Ow: m_ow m = []).
        { unfold leave_ok in U. cbv zeta in U.
          destruct (Z.eqb_spec (m_out m) (m_left m)) as [E|E].
          - apply Zlength_nil_inv. rewrite <- (Dow (or_ind (fun H => or_introl H) (fun H => or_intror (or_introl H)) Wm)). lia.
          - exfalso. apply Bool.orb_false_iff in U as [_ U].
            assert (B1: (m_mode m <? BAD) = true) by (apply Z.ltb_lt; unfold m_mode in *; destruct X as [X|[X _]]; sic_md).
            assert (B2: (m_mode m <? CHECK) = true) by (apply Z.ltb_lt; unfold m_mode in *; destruct X as [X|[X Y]]; sic_md).
            rewrite B1, B2 in U. cbn in U. discriminate. }
        rewrite Ow, app_nil_r. eapply sic_swin_ext; [exact Sw|]. rewrite Ew. exact (eq_sym (W19 eq_refl)).
  - (* the return code *)
    rewrite C9, T9, W10.
    assert (Hv: m_have mw = m_have m) by (unfold m_have; rewrite W1, W4; reflexivity).
    rewrite W6, Hv.
    unfold stop_ok in St.
    destruct (astep lenfix_list distfix_list src a') as [n w a1 | r0] eqn:A.
    + destruct St as (Rk & St). rewrite Rk.
      destruct (((u32 (m_in m - m_have m) =? 0) && (dd =? 0) || (flush =? Z_FINISH)) && (Z_OK =? Z_OK))%bool.
      * split; [intros F; discriminate F | intros _; split; [right; reflexivity | exact St]].
      * split; [intros F; discriminate F | intros _; split; [left; reflexivity | exact St]].
    + destruct St as (Rk & St). rewrite Rk.
      assert (Rv: r0 = Z_STREAM_END \/ r0 = Z_DATA_ERROR).
      { rewrite (rl_mode _ _ _ _ _ R) in St. destruct St as [D|D].
        - left. rewrite (sic_astep_done src a' D) in A. inversion A; reflexivity.
        - right. rewrite (sic_astep_bad src a' D) in A. inversion A; reflexivity. }
      assert (Rn: (r0 =? Z_OK) = false) by (destruct Rv as [->| ->]; reflexivity).
      rewrite Rn, Bool.andb_false_r.
      assert (Fc0: final_code r0 = true) by (destruct Rv as [->| ->]; reflexivity).
      split; [intros _; reflexivity | intros F; rewrite Fc0 in F; discriminate F].
Qed.

Lemma si_call : call_part_stmt.
Proof.
  intros KIT AW S1 S2 S3 S4 src flush P O z L inp res a W B LV Z T P0 PL IE IL RUN. cbv zeta.
  destruct RUN as (o & LP & Ro).
  destruct (sic_init src P O z L inp a W B Z T P0 PL IE) as (Ra0 & R0).
  assert (H0: sic_head src P O inp (zf_ao z) (m_init z L inp) (sic_a0 a)).
  { split; [exact R0|]. split; [apply sic_init_awf; auto|]. split; [reflexivity|]. split; [reflexivity|].
    destruct LV as (_ & SW & _). pose proof (sw_whave _ SW). destruct (sw_wdata _ SW) as [Wd _].
    unfold m_init. destruct (_ =? _); cbn; intros Z0; apply Zlength_nil_inv; lia. }
  destruct (sic_loop AW S1 S2 S3 S4 flush src P O inp (zf_ao z) _ _ LP _ H0 eq_refl) as (a' & Ra & En).
  pose proof (sic_areach_trans _ _ _ _ _ _ Ra0 Ra) as RA.
  destruct o as [mE | r mE].
  - destruct En as (L1 & Hd & St). inversion Ro; subst.
    + left. reflexivity.
    + right. exact (sic_leave_case src flush P O inp (zf_ao z) a a' mE RA Hd St).
  - destruct En as (-> & Hd & Ae & Sx & Sw & Bi & Ho & Md). subst res. right.
    exact (sic_ret_case src flush P O inp (zf_ao z) a a' mE RA Hd Ae Sx Sw Bi Ho Md).
Qed.

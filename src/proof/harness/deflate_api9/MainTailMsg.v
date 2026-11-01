(* Law deflate_api, main: the calls after Z_STREAM_END and after deflateEnd, and return 0 (MainKit.v).
   main_tail_ok' = MainTail.main_tail_ok with the premise is_pointer_or_null (rf_msgv rf) (kit v3 puts it in rf_ok):
   deflate's PRE needs msg_ok for strm->msg, which the v1 rf_ok does not give. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.HarnessRef.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec Zlib.proof.deflate.DSpec9.
Require Zlib.proof.deflate.Obligations.
Require Import Zlib.proof.deflate.LawFacts Zlib.proof.deflate.HarnessLib Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.harness.deflate_api.ApiCS Zlib.proof.harness.deflate_api9.RunSpec
               Zlib.proof.harness.deflate_api9.ApiConv Zlib.proof.harness.deflate_api9.RunKit
               Zlib.proof.harness.deflate_api9.MainKit.
Require Import Zlib.harness.x_deflate_api.code.
#[local] Existing Instance ApiCS.CS.
Local Open Scope logic.

(** ** The kit of the parts (continuation-passing, as RunKit.v): main's statements after msuf4's cuts
     tsuf 8  (deflate(&s, Z_SYNC_FLUSH)),  tsuf 10 (the first deflateEnd),  tsuf 13 (deflateReset), and
     mt_live1 : msuf4 (MA)  -> tsuf8 (MT8)      bad = ..; b[0] = 0; the fields; deflate(Z_FINISH); avail_out == 1
     mt_live2 : tsuf8 (MT8) -> tsuf10 (MT10)    deflate(Z_SYNC_FLUSH); if (bad ..) deflate(bad); R given back
     mt_end1  : tsuf10      -> tsuf13 (MT13)    deflateEnd; deflate(Z_FINISH); deflateEnd on the ended stream
     mt_end2  : tsuf13      -> return 0         deflateReset, deflateParams, deflateSetDictionary, deflatePrime *)
Ltac get_tsuf k := let x := eval cbv beta iota zeta delta [suf msuf4] in (suf k msuf4) in exact x.
Definition tsuf8 : statement := ltac:(get_tsuf 8%nat).
Definition tsuf10 : statement := ltac:(get_tsuf 10%nat).
Definition tsuf13 : statement := ltac:(get_tsuf 13%nat).

(* R's fields (R->h included) as run_ok_at holds them *)
Definition rrest (rf : rfinal) (vR : val) : mpred :=
  let rs := rf_rs rf in
  drun_rest rs (vi 0) (vi (rf_wrap rf)) (vi (wb_of (rs_wbits rs))) (rf_nf rf) (rf_dset rf) (rf_hset rf)
    (Zlength (rf_O rf)) 1 vR * hpart (rf_hset rf) vR.

(* at tsuf8: deflate(Z_FINISH) returned Z_STREAM_END on the empty input at b, b's byte unchanged *)
Definition MT8 (I : api_inv) (Iend : dstate -> Prop) (rf : rfinal) (vR vs vb : val) (gv : globals)
    (s1 : dstate) (bad tin tout adler : Z) (msgv : val) : environ -> mpred :=
  PROP (rf_ok Iend vR rf; api_facts I Iend; Iend s1; d_gzhead s1 = d_gzhead (rf_s rf); s32 bad;
        is_pointer_or_null msgv)
  LOCAL (temp _bad (vi bad); lvar _R t_drun vR; lvar _s t_strmL vs; lvar _b (tarray tuchar 1) vb; gvars gv)
  SEP (dstream 2 (Some s1) vs (rf_ghp rf) gv; api_fields vs vb 0 tin vb 1 tout msgv adler; strm_pad vs;
       hdr_at (Some s1) (rf_ghp rf) (hx_of (rf_rs rf)); rrest rf vR;
       data_at Tsh (tarray tuchar 1) [vi 0] vb; mem_mgr gv; deflate_globals gv;
       data_at_ (Share.comp Ews) t_drun vR; data_at_ (Share.comp Ews) t_strmL vs; TT).

(* at tsuf10: the live stream after Z_STREAM_END, R given back (Tsh) *)
Definition MT10 (I : api_inv) (Iend : dstate -> Prop) (vR vs vb : val) (gv : globals)
    (s2 : dstate) (ghp : val) (tin tout adler : Z) (msgv : val) : environ -> mpred :=
  PROP (api_facts I Iend; Iend s2; is_pointer_or_null msgv)
  LOCAL (lvar _R t_drun vR; lvar _s t_strmL vs; lvar _b (tarray tuchar 1) vb; gvars gv)
  SEP (dstream 2 (Some s2) vs ghp gv; api_fields vs vb 0 tin vb 1 tout msgv adler; strm_pad vs;
       data_at Tsh (tarray tuchar 1) [vi 0] vb; data_at_ Tsh t_drun vR; mem_mgr gv; deflate_globals gv;
       data_at_ (Share.comp Ews) t_strmL vs; TT).

(* at tsuf13: the ended stream *)
Definition MT13 (vR vs vb : val) (gv : globals) (tin tout adler : Z) (msgv : val) : environ -> mpred :=
  PROP (is_pointer_or_null msgv)
  LOCAL (lvar _R t_drun vR; lvar _s t_strmL vs; lvar _b (tarray tuchar 1) vb; gvars gv)
  SEP (dstream 2 None vs nullval gv; api_fields vs vb 0 tin vb 1 tout msgv adler; strm_pad vs;
       data_at Tsh (tarray tuchar 1) [vi 0] vb; data_at_ Tsh t_drun vR; mem_mgr gv; deflate_globals gv;
       data_at_ (Share.comp Ews) t_strmL vs; TT).

(** Helpers of [c_deflate_err_z]: no stage of deflate() but the entry returns Z_STREAM_ERROR. *)
Definition dno_err (r : option dres) : Prop := forall s z c, r = Some (s, z, Some c) -> c <> -2.

Ltac errz_crunch :=
  repeat match goal with
  | H : None = Some _ |- _ => discriminate H
  | H : (match _ with _ => _ end) = Some _ |- _ => revert H
  | |- Some _ = Some _ -> _ => let E := fresh "E" in intro E; injection E as; subst
  | |- None = Some _ -> _ => let E := fresh "E" in intro E; discriminate E
  | |- context [bind _ _] => unfold bind; cbv beta iota zeta
  | |- context [then_stage _ _] => unfold then_stage; cbv beta iota zeta
  | |- context [c_flush_or_return _ _] => unfold c_flush_or_return; cbv beta iota zeta
  | |- context [match ?x with _ => _ end] =>
      lazymatch x with
      | Some _ => fail
      | None => fail
      | (_, _) => fail
      | inl _ => fail
      | inr _ => fail
      | true => fail
      | false => fail
      | _ => destruct x eqn:?
      end; cbv beta iota
  | |- _ = _ -> _ => intro
  end.

Ltac errz_stage :=
  intros ? ? ?; cbv beta iota zeta; errz_crunch; cbv [Z_OK Z_BUF_ERROR Z_STREAM_END]; try discriminate.

Lemma then_stage_dno_err r k : dno_err r -> (forall s z, dno_err (k s z)) -> dno_err (then_stage r k).
Proof.
  unfold dno_err, then_stage, bind; intros Hr Hk s z c H.
  destruct r as [[[s0 z0] [o|]]|]; [| |discriminate].
  - injection H as -> -> ->; eapply Hr; reflexivity.
  - eapply Hk; exact H.
Qed.

Lemma dno_err_zlib s z : dno_err (c_deflate_zlib_header s z).
Proof. unfold c_deflate_zlib_header; errz_stage. Qed.

Lemma dno_err_gzip s z : dno_err (c_deflate_gzip_header s z).
Proof. unfold c_deflate_gzip_header; errz_stage. Qed.

Lemma dno_err_extra s z : dno_err (c_deflate_extra s z).
Proof. unfold c_deflate_extra; errz_stage. Qed.

Lemma dno_err_str h o b s z : dno_err (c_deflate_str h o b s z).
Proof. unfold c_deflate_str; errz_stage. Qed.

Lemma dno_err_name s z : dno_err (c_deflate_name s z).
Proof.
  unfold c_deflate_name, bind; destruct (d_status s =? NAME_STATE); [|intros ? ? ? H; discriminate H || (injection H as; discriminate)].
  destruct (c_gzhead s) as [h|]; [|intros ? ? ? H; discriminate H].
  apply then_stage_dno_err; [apply dno_err_str|]. intros ? ? ? ? ? H; injection H as; discriminate.
Qed.

Lemma dno_err_comment s z : dno_err (c_deflate_comment s z).
Proof.
  unfold c_deflate_comment, bind; destruct (d_status s =? COMMENT_STATE); [|intros ? ? ? H; discriminate H || (injection H as; discriminate)].
  destruct (c_gzhead s) as [h|]; [|intros ? ? ? H; discriminate H].
  apply then_stage_dno_err; [apply dno_err_str|]. intros ? ? ? ? ? H; injection H as; discriminate.
Qed.

Lemma dno_err_hcrc s z : dno_err (c_deflate_hcrc s z).
Proof. unfold c_deflate_hcrc; errz_stage. Qed.

Lemma dno_err_compress s z f : dno_err (c_deflate_compress s z f).
Proof. unfold c_deflate_compress; errz_stage. Qed.

Lemma trailer_no_err s z f s1 z1 c : c_deflate_trailer s z f = Some (s1, z1, c) -> c <> -2.
Proof.
  unfold c_deflate_trailer; cbv beta iota zeta; errz_crunch; cbv [Z_OK Z_BUF_ERROR Z_STREAM_END]; try discriminate.
Qed.

Lemma entry_err s z f s1 z1 c :
  c_deflate_entry s z f = Some (s1, z1, Some c) -> c = -2 -> exists m, z1 = set_z_msg z m.
Proof.
  intros Hst Hc; revert Hst; unfold c_deflate_entry; cbv beta iota zeta; errz_crunch; eauto;
    match goal with H : _ = _ |- _ => cbv [Z_OK Z_BUF_ERROR Z_STREAM_END] in H; discriminate H end.
Qed.

(** The model: deflate() returning Z_STREAM_ERROR changes no field of the stream but msg. *)
Lemma c_deflate_err_z s z flush s' z' :
  c_deflate s z flush = Some (s', z', Z_STREAM_ERROR) ->
  z_in z' = z_in z /\ z_next_in z' = z_next_in z /\ z_avail_in z' = z_avail_in z /\
  z_total_in z' = z_total_in z /\ z_out z' = z_out z /\ z_avail_out z' = z_avail_out z /\
  z_total_out z' = z_total_out z /\ z_adler z' = z_adler z.
Proof.
  intros H.
  assert (Hm : exists m, z' = set_z_msg z m).
  { unfold c_deflate in H.
    destruct (bad_state s || (flush >? Z_BLOCK) || (flush <? 0))%bool.
    { injection H as Hs Hz; subst s' z'; exists (z_msg z); destruct z; reflexivity. }
    unfold bind at 1 in H.
    match type of H with match ?x with _ => _ end = _ => destruct x as [[[s0 z0] [o|]]|] eqn:E end;
      [| |discriminate H].
    - injection H as -> -> ->.
      unfold then_stage at 1, bind at 1 in E.
      destruct (c_deflate_entry s z flush) as [[[sa za] [oa|]]|] eqn:Ee; [| |discriminate E].
      + injection E as -> -> ->. eapply entry_err; [exact Ee|reflexivity].
      + exfalso. revert E.
        match goal with |- ?r = _ -> _ => assert (Hn : dno_err r) end.
        { repeat (apply then_stage_dno_err; [first [apply dno_err_zlib | apply dno_err_gzip | apply dno_err_extra
            | apply dno_err_name | apply dno_err_comment | apply dno_err_hcrc] | intros ? ?]).
          apply dno_err_compress. }
        intros E; exact (Hn _ _ _ E eq_refl).
    - exfalso. eapply trailer_no_err; [exact H|reflexivity]. }
  destruct Hm as [m ->]; repeat split.
Qed.

(* run_ok_at without the objects (they go into TT) *)
Lemma mt_run_ok_at rf vR vs gv :
  run_ok_at rf vR vs gv |--
  rrest rf vR * dstream 2 (Some (rf_s rf)) vs (rf_ghp rf) gv *
  api_fields vs (rf_nin rf) (rf_ain rf) (rf_tin rf) (rf_nout rf) (rf_aout rf) (rf_tout rf) (rf_msgv rf)
    (rf_adler rf) * strm_pad vs *
  hdr_at (Some (rf_s rf)) (rf_ghp rf) (hx_of (rf_rs rf)) * TT.
Proof. unfold run_ok_at, rrest. cancel. Qed.

Lemma mt_dstream_sp_fold lvl os strmp ghp sp gv :
  dstream_sp lvl os strmp ghp sp gv |-- dstream lvl os strmp ghp gv.
Proof. rewrite dstream_sp_eq. Exists sp. cancel. Qed.

Lemma mt_hdr_at_gz s s' ghp hx :
  d_gzhead s' = d_gzhead s -> hdr_at (Some s) ghp hx = hdr_at (Some s') ghp hx.
Proof. intros E. unfold hdr_at. rewrite E. reflexivity. Qed.

(** v5/v9: the caller's fields as strm->next_in, reset_fields and avail_in, next_out, avail_out *)
Definition af_rest (sp : val) (ain tin : Z) (nout : val) (aout tout : Z) (msgv : val) (adler : Z) : mpred :=
  !! (u32_ok ain /\ u64_ok tin /\ u32_ok aout /\ u64_ok tout /\ u64_ok adler) &&
  (reset_fields sp (vl tin) (vl tout) msgv (vl adler) *
   @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._avail_in) (vi ain) sp *
   @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._next_out) nout sp *
   @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._avail_out) (vi aout) sp).

Lemma af_split (sp nin : val) (ain tin : Z) (nout : val) (aout tout : Z) (msgv : val) (adler : Z) :
  api_fields sp nin ain tin nout aout tout msgv adler =
  @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._next_in) nin sp * af_rest sp ain tin nout aout tout msgv adler.
Proof. unfold api_fields, af_rest, reset_fields. apply pred_ext; entailer!. Qed.

Lemma af_join (sp nin : val) (ain tin : Z) (nout : val) (aout tout : Z) (msgv : val) (adler : Z) :
  @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._next_in) nin sp * af_rest sp ain tin nout aout tout msgv adler
  |-- api_fields sp nin ain tin nout aout tout msgv adler.
Proof. rewrite af_split. apply derives_refl. Qed.

Lemma af_rest_fold (sp : val) (ain tin : Z) (nout : val) (aout tout : Z) (msgv : val) (adler : Z) :
  u32_ok ain -> u64_ok tin -> u32_ok aout -> u64_ok tout -> u64_ok adler ->
  reset_fields sp (vl tin) (vl tout) msgv (vl adler) *
  @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._avail_in) (vi ain) sp *
  @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._next_out) nout sp *
  @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._avail_out) (vi aout) sp
  |-- af_rest sp ain tin nout aout tout msgv adler.
Proof. intros. unfold af_rest. entailer!. Qed.

(* deflateSetDictionary's dictionary object (v7) *)
Lemma mt_opt_obj0 (q : val) :
  @data_at DCS.CS Ews (tarray tuchar (Zlength [0])) (map vi [0]) q = opt_obj Ews (Some [0]) q.
Proof.
  unfold opt_obj. rewrite prop_true_andp by (repeat constructor; lia).
  change (Zlength [0] =? 0) with false. cbv iota. rewrite sepcon_emp. reflexivity.
Qed.

Lemma mt_live1_ok {Espec : OracleKind} I Iend rf vR vs vb gv :
  is_pointer_or_null (rf_msgv rf) ->
  (forall s1 bad tin tout adler msgv,
     semax (Delta_m I Iend) (MT8 I Iend rf vR vs vb gv s1 bad tin tout adler msgv) tsuf8 POST_m) ->
  semax (Delta_m I Iend) (MA I Iend rf vR vs vb gv) msuf4 POST_m.
Proof.
  intros Hmsg HK. unfold Delta_m, MA, msuf4, POST_m. simplify_func_tycontext. Intros.
  sep_apply mt_run_ok_at.
  pose proof H as HR. destruct HR as (RS & HIend & _ & _ & _ & _ & _ & Hh).
  destruct (af_end_finish _ _ H0 (rf_s rf) [] 0 (rf_tin rf) (rf_tout rf) (rf_adler rf) (Some 0))
    as (s' & z' & Hrun & Hout & Haout & Hain & Hnin & Hgz & HI'); auto; try (rewrite Zlength_nil; lia).
  forward_call tt. Intros n. forward.
  assert_PROP (u32_ok (rf_ain rf) /\ u64_ok (rf_tin rf) /\ u32_ok (rf_aout rf) /\
               u64_ok (rf_tout rf) /\ u64_ok (rf_adler rf)) as HAF.
  { unfold api_fields. entailer!. }
  assert_PROP (field_compatible (tarray tuchar 1) [] vb) as FCb by entailer!.
  rewrite api_fields_L. unfold api_fieldsL. Intros.
  forward. forward. forward. forward.
  assert (Pvb : isptr vb) by (destruct FCb; auto).
  assert (FA : field_at Ews t_strmL (DOT _next_in) vb vs *
               field_at Ews t_strmL (DOT _avail_in) (Vint (Int.repr 0)) vs *
               field_at Ews t_strmL (DOT _total_in) (vl (rf_tin rf)) vs *
               field_at Ews t_strmL (DOT _next_out) vb vs *
               field_at Ews t_strmL (DOT _avail_out) (Vint (Int.repr 1)) vs *
               field_at Ews t_strmL (DOT _total_out) (vl (rf_tout rf)) vs *
               field_at Ews t_strmL (DOT _msg) (rf_msgv rf) vs *
               field_at Ews t_strmL (DOT _adler) (vl (rf_adler rf)) vs |--
               api_fields vs (offset_val 0 vb) (Zlength (@nil Z)) (rf_tin rf) vb (Zlength [vi 0]) (rf_tout rf)
                 (rf_msgv rf) (rf_adler rf)).
  { rewrite api_fields_L. unfold api_fieldsL. rewrite isptr_offset_val_zero by auto.
    rewrite Zlength_nil. change (Zlength [vi 0]) with 1.
    apply andp_right; [apply prop_right; unfold u32_ok, u64_ok in *; repeat split; auto; try rep_lia | unfold vi; cancel]. }
  sep_apply FA.
  replace (upd_Znth 0 (default_val (tarray tuchar 1)) (Vint (Int.zero_ext 8 (Int.repr 0)))) with [vi 0]
    by reflexivity.
  rewrite <- (data_at_share_join Ews (Share.comp Ews) Tsh) by apply join_comp_Tsh.
  rewrite (bytes_cs CS DCS.CS Ews 1).
  change (@data_at DCS.CS Ews (tarray tuchar 1)) with (@data_at DCS.CS Ews (tarray tuchar (Zlength [vi 0]))).
  rewrite dstream_sp_eq. Intros sp'.
  forward_call (Some (rf_s rf), vs, rf_ghp rf, sp', hx_of (rf_rs rf), vb, Ews, @nil Z, 0, 0, rf_tin rf, vb,
                [vi 0], WVnone, rf_tout rf, rf_msgv rf, Some 0, rf_adler rf, 4, (Some s', z', Z_STREAM_END), gv).
  { rewrite Zlength_nil. simpl map. rewrite (@data_at_tuchar_zero_array_eq DCS.CS) by auto.
    unfold wv_at. rewrite !sepcon_assoc. cancel. }
  { split; [| split; [| split]].
    - intros X. inversion X.
    - unfold s32_ok. rep_lia.
    - unfold strm_ranges, zmk; simpl. unfold u32_ok, u64_ok in *.
      change (Zlength [vi 0]) with 1. rewrite Zlength_nil.
      repeat split; auto; try rep_lia.
    - exists (fun f => f). split; [ apply ef_ok_id | ].
      unfold on_state, c_on_state. rewrite c_deflate_g_id. change (Zlength [vi 0]) with 1.
      change (zmk ?a ?b ?c ?d ?e ?f ?g ?h) with (zcall a b c d e f g h). change 4 with Z_FINISH. rewrite Hrun. reflexivity. }
  simpl fst; simpl snd. Intros msgv'.
  rewrite Hnin, Hout, Haout, Hain. rewrite Zlength_nil.
  forward_call (Int.one).
  rewrite api_fields_L. unfold api_fieldsL. Intros.
  forward.
  forward_call (Int.one).
  rewrite isptr_offset_val_zero by auto.
  change (map vi []) with (@nil val).
  rewrite (@data_at_tuchar_zero_array_eq DCS.CS) by auto.
  change ([] ++ sublist 0 (Zlength [vi 0]) [vi 0]) with [vi 0].
  change (Zlength [vi 0]) with 1.
  rewrite <- (bytes_cs CS DCS.CS Ews 1).
  change (upd_Znth 0 (default_val (tarray tuchar 1)) (Vint (Int.zero_ext 8 (Int.repr 0)))) with [vi 0].
  rewrite (mt_hdr_at_gz (rf_s rf) s' _ _ Hgz).
  sep_apply (mt_dstream_sp_fold 2 (Some s') vs (rf_ghp rf) sp' gv).
  unfold wv_at.
  assert (Pm : is_pointer_or_null msgv') 
    by (destruct (z_msg z'); unfold msg_ok in H7; [auto | subst; simpl; auto]).
  eapply semax_pre; [| apply (HK s' (Int.signed (Int.repr n)) (z_total_in z') (z_total_out z') (z_adler z') msgv')].
  unfold MT8.
  rewrite <- (data_at_share_join Ews (Share.comp Ews) Tsh _ _ _ (join_comp_Tsh Ews)).
  rewrite api_fields_L. unfold api_fieldsL.
  replace (vi (Int.signed (Int.repr n))) with (Vint (Int.repr n)) by (unfold vi; rewrite Int.repr_signed; reflexivity).
  entailer!.
  unfold s32. apply Int.signed_range.
Qed.

(** mt_live2_ok's copy of c_deflate_err_z (proved above), and its helpers: no stage of deflate() but the entry returns Z_STREAM_ERROR. *)
Definition ml2_dno_err (r : option dres) : Prop := forall s z c, r = Some (s, z, Some c) -> c <> -2.

Ltac ml2_errz_crunch :=
  repeat match goal with
  | H : None = Some _ |- _ => discriminate H
  | H : (match _ with _ => _ end) = Some _ |- _ => revert H
  | |- Some _ = Some _ -> _ => let E := fresh "E" in intro E; injection E as; subst
  | |- None = Some _ -> _ => let E := fresh "E" in intro E; discriminate E
  | |- context [bind _ _] => unfold bind; cbv beta iota zeta
  | |- context [then_stage _ _] => unfold then_stage; cbv beta iota zeta
  | |- context [c_flush_or_return _ _] => unfold c_flush_or_return; cbv beta iota zeta
  | |- context [match ?x with _ => _ end] =>
      lazymatch x with
      | Some _ => fail
      | None => fail
      | (_, _) => fail
      | inl _ => fail
      | inr _ => fail
      | true => fail
      | false => fail
      | _ => destruct x eqn:?
      end; cbv beta iota
  | |- _ = _ -> _ => intro
  end.

Ltac ml2_errz_stage :=
  intros ? ? ?; cbv beta iota zeta; ml2_errz_crunch; cbv [Z_OK Z_BUF_ERROR Z_STREAM_END]; try discriminate.

Lemma ml2_then_stage_dno_err r k : ml2_dno_err r -> (forall s z, ml2_dno_err (k s z)) -> ml2_dno_err (then_stage r k).
Proof.
  unfold ml2_dno_err, then_stage, bind; intros Hr Hk s z c H.
  destruct r as [[[s0 z0] [o|]]|]; [| |discriminate].
  - injection H as -> -> ->; eapply Hr; reflexivity.
  - eapply Hk; exact H.
Qed.

Lemma ml2_dno_err_zlib s z : ml2_dno_err (c_deflate_zlib_header s z).
Proof. unfold c_deflate_zlib_header; ml2_errz_stage. Qed.

Lemma ml2_dno_err_gzip s z : ml2_dno_err (c_deflate_gzip_header s z).
Proof. unfold c_deflate_gzip_header; ml2_errz_stage. Qed.

Lemma ml2_dno_err_extra s z : ml2_dno_err (c_deflate_extra s z).
Proof. unfold c_deflate_extra; ml2_errz_stage. Qed.

Lemma ml2_dno_err_str h o b s z : ml2_dno_err (c_deflate_str h o b s z).
Proof. unfold c_deflate_str; ml2_errz_stage. Qed.

Lemma ml2_dno_err_name s z : ml2_dno_err (c_deflate_name s z).
Proof.
  unfold c_deflate_name, bind; destruct (d_status s =? NAME_STATE); [|intros ? ? ? H; discriminate H || (injection H as; discriminate)].
  destruct (c_gzhead s) as [h|]; [|intros ? ? ? H; discriminate H].
  apply ml2_then_stage_dno_err; [apply ml2_dno_err_str|]. intros ? ? ? ? ? H; injection H as; discriminate.
Qed.

Lemma ml2_dno_err_comment s z : ml2_dno_err (c_deflate_comment s z).
Proof.
  unfold c_deflate_comment, bind; destruct (d_status s =? COMMENT_STATE); [|intros ? ? ? H; discriminate H || (injection H as; discriminate)].
  destruct (c_gzhead s) as [h|]; [|intros ? ? ? H; discriminate H].
  apply ml2_then_stage_dno_err; [apply ml2_dno_err_str|]. intros ? ? ? ? ? H; injection H as; discriminate.
Qed.

Lemma ml2_dno_err_hcrc s z : ml2_dno_err (c_deflate_hcrc s z).
Proof. unfold c_deflate_hcrc; ml2_errz_stage. Qed.

Lemma ml2_dno_err_compress s z f : ml2_dno_err (c_deflate_compress s z f).
Proof. unfold c_deflate_compress; ml2_errz_stage. Qed.

Lemma ml2_trailer_no_err s z f s1 z1 c : c_deflate_trailer s z f = Some (s1, z1, c) -> c <> -2.
Proof.
  unfold c_deflate_trailer; cbv beta iota zeta; ml2_errz_crunch; cbv [Z_OK Z_BUF_ERROR Z_STREAM_END]; try discriminate.
Qed.

Lemma ml2_entry_err s z f s1 z1 c :
  c_deflate_entry s z f = Some (s1, z1, Some c) -> c = -2 -> exists m, z1 = set_z_msg z m.
Proof.
  intros Hst Hc; revert Hst; unfold c_deflate_entry; cbv beta iota zeta; ml2_errz_crunch; eauto;
    match goal with H : _ = _ |- _ => cbv [Z_OK Z_BUF_ERROR Z_STREAM_END] in H; discriminate H end.
Qed.

Lemma ml2_c_deflate_err_z s z flush s' z' :
  c_deflate s z flush = Some (s', z', Z_STREAM_ERROR) ->
  z_in z' = z_in z /\ z_next_in z' = z_next_in z /\ z_avail_in z' = z_avail_in z /\
  z_total_in z' = z_total_in z /\ z_out z' = z_out z /\ z_avail_out z' = z_avail_out z /\
  z_total_out z' = z_total_out z /\ z_adler z' = z_adler z.
Proof.
  intros H.
  assert (Hm : exists m, z' = set_z_msg z m).
  { unfold c_deflate in H.
    destruct (bad_state s || (flush >? Z_BLOCK) || (flush <? 0))%bool.
    { injection H as Hs Hz; subst s' z'; exists (z_msg z); destruct z; reflexivity. }
    unfold bind at 1 in H.
    match type of H with match ?x with _ => _ end = _ => destruct x as [[[s0 z0] [o|]]|] eqn:E end;
      [| |discriminate H].
    - injection H as -> -> ->.
      unfold then_stage at 1, bind at 1 in E.
      destruct (c_deflate_entry s z flush) as [[[sa za] [oa|]]|] eqn:Ee; [| |discriminate E].
      + injection E as -> -> ->. eapply ml2_entry_err; [exact Ee|reflexivity].
      + exfalso. revert E.
        match goal with |- ?r = _ -> _ => assert (Hn : ml2_dno_err r) end.
        { repeat (apply ml2_then_stage_dno_err; [first [apply ml2_dno_err_zlib | apply ml2_dno_err_gzip | apply ml2_dno_err_extra
            | apply ml2_dno_err_name | apply ml2_dno_err_comment | apply ml2_dno_err_hcrc] | intros ? ?]).
          apply ml2_dno_err_compress. }
        intros E; exact (Hn _ _ _ E eq_refl).
    - exfalso. eapply ml2_trailer_no_err; [exact H|reflexivity]. }
  destruct Hm as [m ->]; repeat split.
Qed.

(* hdr_at depends on the state's gzhead only *)
Lemma ml2_hdr_at_gz s s' ghp hx :
  d_gzhead s' = d_gzhead s -> hdr_at (Some s) ghp hx = hdr_at (Some s') ghp hx.
Proof. intros E. unfold hdr_at. rewrite E. reflexivity. Qed.

Lemma ml2_dstream_sp_fold lvl os strmp ghp sp gv :
  dstream_sp lvl os strmp ghp sp gv |-- dstream lvl os strmp ghp gv.
Proof. rewrite dstream_sp_eq. Exists sp. cancel. Qed.

Lemma mt_live2_ok {Espec : OracleKind} I Iend rf vR vs vb gv s1 bad tin tout adler msgv :
  run_mem_ok ->
  (forall s2 ghp tin' tout' adler' msgv',
     semax (Delta_m I Iend) (MT10 I Iend vR vs vb gv s2 ghp tin' tout' adler' msgv') tsuf10 POST_m) ->
  semax (Delta_m I Iend) (MT8 I Iend rf vR vs vb gv s1 bad tin tout adler msgv) tsuf8 POST_m.
Proof.
  intros HM HK. unfold Delta_m, MT8, tsuf8, POST_m. simplify_func_tycontext. Intros.
  pose proof H as HR. destruct HR as (RS & HIend & _ & _ & _ & _ & _ & Hh).
  destruct (af_end_other _ _ H0 s1 (zmk [] 0 0 tin 1 tout adler (Some 0)) 2) as [z1 Hrun1];
    auto; try (unfold Z_FINISH; lia).
  destruct (ml2_c_deflate_err_z _ _ _ _ _ Hrun1) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
  unfold zmk in E1, E2, E3, E4, E5, E6, E7, E8. cbn [z_in z_next_in z_avail_in z_total_in z_out z_avail_out
    z_total_out z_adler] in E1, E2, E3, E4, E5, E6, E7, E8.
  assert_PROP (u32_ok 0 /\ u64_ok tin /\ u32_ok 1 /\ u64_ok tout /\ u64_ok adler) as HAF.
  { unfold api_fields. entailer!. }
  assert_PROP (field_compatible (tarray tuchar 1) [] vb) as FCb by entailer!.
  assert (Pvb : isptr vb) by (destruct FCb; auto).
  replace (api_fields vs vb 0 tin vb 1 tout msgv adler)
    with (api_fields vs (offset_val 0 vb) (Zlength (@nil Z)) tin vb (Zlength [vi 0]) tout msgv adler)
    by (rewrite isptr_offset_val_zero by auto; reflexivity).
  rewrite <- (data_at_share_join Ews (Share.comp Ews) Tsh) by apply join_comp_Tsh.
  rewrite (bytes_cs CS DCS.CS Ews 1).
  change (@data_at DCS.CS Ews (tarray tuchar 1)) with (@data_at DCS.CS Ews (tarray tuchar (Zlength [vi 0]))).
  rewrite dstream_sp_eq. Intros sp'.
  forward_call (Some s1, vs, rf_ghp rf, sp', hx_of (rf_rs rf), vb, Ews, @nil Z, 0, 0, tin, vb,
                [vi 0], WVnone, tout, msgv, Some 0, adler, 2, (Some s1, z1, Z_STREAM_ERROR), gv).
  { rewrite Zlength_nil. simpl map. rewrite (@data_at_tuchar_zero_array_eq DCS.CS) by auto.
    unfold wv_at. rewrite !sepcon_assoc. cancel. }
  { split; [| split; [| split]].
    - intros X. inversion X.
    - unfold s32_ok. rep_lia.
    - unfold strm_ranges, zmk; simpl. unfold u32_ok, u64_ok in *.
      change (Zlength [vi 0]) with 1. rewrite Zlength_nil.
      repeat split; auto; try rep_lia.
    - exists (fun f => f). split; [ apply ef_ok_id | ].
      unfold on_state, c_on_state. rewrite c_deflate_g_id. change (Zlength [vi 0]) with 1.
      rewrite Hrun1. reflexivity. }
  simpl fst; simpl snd. Intros msgv1.
  rewrite E2, E3, E4, E5, E6, E7, E8.
  forward_call (Int.one).
  rewrite !isptr_offset_val_zero by auto. rewrite Zlength_nil.
  change (map vi []) with (@nil val).
  rewrite (@data_at_tuchar_zero_array_eq DCS.CS) by auto.
  change ([] ++ sublist 0 (Zlength [vi 0]) [vi 0]) with [vi 0].
  change (Zlength [vi 0]) with 1.
  rewrite <- (bytes_cs CS DCS.CS Ews 1).
  sep_apply (ml2_dstream_sp_fold 2 (Some s1) vs (rf_ghp rf) sp' gv).
  unfold wv_at.
  gather_SEP (data_at Ews (tarray tuchar 1) _ vb) (data_at (Share.comp Ews) (tarray tuchar 1) _ vb).
  rewrite (data_at_share_join Ews (Share.comp Ews) Tsh) by apply join_comp_Tsh.
  assert (Pm1 : is_pointer_or_null msgv1)
    by (destruct (z_msg z1); unfold msg_ok in H4; [auto | subst; simpl; auto]).
  assert (Hb : Int.min_signed <= bad <= Int.max_signed) by (unfold s32 in H3; rep_lia).
  forward_if (temp _t'20 (Val.of_bool ((bad <? 0) || (5 <? bad))%bool)).
  { forward. try rewrite Int.signed_repr in H5 by auto. entailer!.
    replace (bad <? 0) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
  { forward. try rewrite Int.signed_repr in H5 by auto. entailer!.
    replace (bad <? 0) with false by (symmetry; apply Z.ltb_ge; lia). simpl orb.
    unfold Val.of_bool, bool2val; destruct (zlt 5 bad) as [L|L];
      [rewrite (proj2 (Z.ltb_lt 5 bad) L) | rewrite (proj2 (Z.ltb_ge 5 bad) ltac:(lia))]; reflexivity. }
  forward_if (EX m : val,
    PROP (is_pointer_or_null m)
    LOCAL (lvar _R t_drun vR; lvar _s t_strmL vs; lvar _b (tarray tuchar 1) vb; gvars gv)
    SEP (data_at Tsh (tarray tuchar 1) [vi 0] vb; dstream 2 (Some s1) vs (rf_ghp rf) gv;
         api_fields vs vb 0 tin vb 1 tout m adler; strm_pad vs; hdr_at (Some s1) (rf_ghp rf) (hx_of (rf_rs rf));
         deflate_globals gv; rrest rf vR; mem_mgr gv; data_at_ (Share.comp Ews) t_drun vR;
         data_at_ (Share.comp Ews) t_strmL vs; TT)).
  { assert (Hbad : bad < 0 \/ 5 < bad).
    { destruct (bad <? 0) eqn:L1; [left; apply Z.ltb_lt; auto|].
      destruct (5 <? bad) eqn:L2; [right; apply Z.ltb_lt; auto|].
      cbv in H5. discriminate H5. }
    pose proof (af_end_bad _ _ H0 s1 (zmk [] 0 0 tin 1 tout adler (z_msg z1)) bad H1 Hbad) as Hrun2.
    replace (api_fields vs vb 0 tin vb 1 tout msgv1 adler)
      with (api_fields vs (offset_val 0 vb) (Zlength (@nil Z)) tin vb (Zlength [vi 0]) tout msgv1 adler)
      by (rewrite isptr_offset_val_zero by auto; reflexivity).
    rewrite <- (data_at_share_join Ews (Share.comp Ews) Tsh) by apply join_comp_Tsh.
    rewrite (bytes_cs CS DCS.CS Ews 1).
    change (@data_at DCS.CS Ews (tarray tuchar 1)) with (@data_at DCS.CS Ews (tarray tuchar (Zlength [vi 0]))).
    rewrite dstream_sp_eq. Intros sp2.
    forward_call (Some s1, vs, rf_ghp rf, sp2, hx_of (rf_rs rf), vb, Ews, @nil Z, 0, 0, tin, vb,
                  [vi 0], WVnone, tout, msgv1, z_msg z1, adler, bad,
                  (Some s1, zmk [] 0 0 tin 1 tout adler (z_msg z1), Z_STREAM_ERROR), gv).
    { rewrite Zlength_nil. simpl map. rewrite (@data_at_tuchar_zero_array_eq DCS.CS) by auto.
      unfold wv_at. rewrite !sepcon_assoc. cancel. }
    { split; [| split].
      - intros X. inversion X.
      - unfold strm_ranges, zmk; simpl. unfold u32_ok, u64_ok in *.
        change (Zlength [vi 0]) with 1. rewrite Zlength_nil.
        repeat split; auto; try rep_lia.
      - exists (fun f => f). split; [ apply ef_ok_id | ].
        unfold on_state, c_on_state. rewrite c_deflate_g_id. change (Zlength [vi 0]) with 1.
        rewrite Hrun2. reflexivity. }
    simpl fst; simpl snd. Intros msgv2.
    unfold zmk. cbn [z_in z_next_in z_avail_in z_total_in z_out z_avail_out z_total_out z_adler z_msg].
    cbn [z_msg] in *.
    forward_call (Int.one).
    rewrite !isptr_offset_val_zero by auto. rewrite Zlength_nil.
    change (map vi []) with (@nil val).
    rewrite (@data_at_tuchar_zero_array_eq DCS.CS) by auto.
    change ([] ++ sublist 0 (Zlength [vi 0]) [vi 0]) with [vi 0].
    change (Zlength [vi 0]) with 1.
    rewrite <- (bytes_cs CS DCS.CS Ews 1).
    sep_apply (ml2_dstream_sp_fold 2 (Some s1) vs (rf_ghp rf) sp2 gv).
    unfold wv_at.
    gather_SEP (data_at Ews (tarray tuchar 1) _ vb) (data_at (Share.comp Ews) (tarray tuchar 1) _ vb).
    rewrite (data_at_share_join Ews (Share.comp Ews) Tsh) by apply join_comp_Tsh.
    assert (Pm2 : is_pointer_or_null msgv2)
      by (unfold zmk in H6; cbn [z_msg] in H6; destruct (z_msg z1); unfold msg_ok in H6;
          [auto | subst; simpl; auto]).
    Exists msgv2. entailer!. }
  { forward. Exists msgv1. entailer!. }
  Intros m.
  destruct HM as [_ [HM2 _]].
  assert (Hh' : (rf_hset rf = 1 /\ rf_ghp rf = hp_of vR /\ d_gzhead s1 = Some (hdr_of (rf_rs rf))) \/
                (rf_hset rf = 0 /\ d_gzhead s1 = None)) by (rewrite H2; exact Hh).
  unfold rrest.
  sep_apply (HM2 (rf_rs rf) (vi 0) (vi (rf_wrap rf)) (vi (wb_of (rs_wbits (rf_rs rf)))) (rf_nf rf) (rf_dset rf)
               (rf_hset rf) (Zlength (rf_O rf)) 1 vR s1 (rf_ghp rf) Hh').
  Intros.
  gather_SEP (data_at_ Ews t_drun vR) (data_at_ (Share.comp Ews) t_drun vR).
  rewrite (data_at__share_join Ews (Share.comp Ews) Tsh) by apply join_comp_Tsh.
  eapply semax_pre; [| apply (HK s1 (rf_ghp rf) tin tout adler m)].
  unfold MT10. entailer!.
Qed.

Lemma mt_end1_ok {Espec : OracleKind} I Iend vR vs vb gv s2 ghp tin tout adler msgv :
  Zlib.proof.deflate.Obligations.ob_dstream_to_end ->
  (forall tin' tout' adler' msgv',
     semax (Delta_m I Iend) (MT13 vR vs vb gv tin' tout' adler' msgv') tsuf13 POST_m) ->
  semax (Delta_m I Iend) (MT10 I Iend vR vs vb gv s2 ghp tin tout adler msgv) tsuf10 POST_m.
Proof.
  intros HE HK. unfold MT10, tsuf10. Intros.
  unfold Delta_m, POST_m. simplify_func_tycontext.
  sep_apply (HE (Some s2) vs ghp gv).
  rewrite af_split.
  forward_call (Some s2, vs, vb, zmk [] 0 0 tin 1 tout adler (Some 0),
                (@None dstate, zmk [] 0 0 tin 1 tout adler (Some 0), Z_OK), gv).
  all: try (cancel; fail).
  { apply (af_end_end _ _ H); auto. }
  cbn [fst snd].
  sep_apply (af_join vs vb 0 tin vb 1 tout msgv adler).
  forward_call (Int.one).
  assert_PROP (isptr vb) as Hvb by entailer!.
  assert_PROP (u64_ok tin /\ u64_ok tout /\ u64_ok adler) as HAF.
  { unfold api_fields. entailer!. }
  rewrite dstream_sp_eq. Intros sp'.
  rewrite <- (data_at_share_join Ews (Share.comp Ews) Tsh (tarray tuchar 1) [vi 0] vb) by (apply join_comp_Tsh).
  rewrite (bytes_cs CS DCS.CS Ews 1).
  replace (api_fields vs vb 0 tin vb 1 tout msgv adler)
    with (api_fields vs (offset_val 0 vb) (Zlength (@nil Z)) tin vb (Zlength [vi 0]) tout msgv adler)
    by (rewrite isptr_offset_val_zero by auto; reflexivity).
  flatten_sepcon_in_SEP.
  forward_call (@None dstate, vs, nullval, sp', (Ews, nullval, nullval, nullval), vb, Ews, @nil Z, 0, 0, tin,
                vb, [vi 0], WVnone, tout, msgv, Some 0, adler, 4,
                (@None dstate, zmk [] 0 0 tin 1 tout adler (Some 0), Z_STREAM_ERROR), gv).
  { rewrite Zlength_nil. cbn [map hdr_at wv_at].
    rewrite !sepcon_assoc. cancel. rewrite <- (emp_sepcon (mem_mgr gv)).
    sep_apply (@data_at_tuchar_zero_array DCS.CS Ews vb Hvb). cancel. }
  { destruct HAF as [? [? ?]].
    split; [| split; [| split]].
    - intro Hz. rewrite Zlength_cons, Zlength_nil in Hz. lia.
    - unfold s32_ok. rep_lia.
    - unfold strm_ranges, zmk; cbn [z_next_in z_avail_in z_in z_total_in z_avail_out z_out z_total_out z_adler].
      rewrite Zlength_cons, !Zlength_nil. unfold u32_ok, u64_ok in *.
      repeat split; auto; try rep_lia.
    - exists (fun f => f). split; [ apply ef_ok_id | reflexivity ]. }
  unfold zmk; cbn [fst snd z_msg z_next_in z_avail_in z_total_in z_out z_avail_out z_total_out z_adler msg_ok].
  Intros msgv'.
  forward_call (Int.one).
  sep_apply (mt_dstream_sp_fold 2 None vs nullval sp' gv).
  sep_apply (HE None vs nullval gv).
  rewrite af_split.
  forward_call (@None dstate, vs, offset_val 0 vb, zmk [] 0 0 tin 1 tout adler (Some 0),
                (@None dstate, zmk [] 0 0 tin 1 tout adler (Some 0), Z_STREAM_ERROR), gv).
  all: try (cancel; fail).
  cbn [fst snd].
  sep_apply af_join.
  forward_call (Int.one).
  unfold MORE_COMMANDS, POSTCONDITION, abbreviate.
  eapply semax_pre; [| apply (HK tin tout adler msgv')].
  unfold MT13. rewrite !Zlength_nil. cbn [map app].
  rewrite isptr_offset_val_zero by auto.
  change (Zlength [vi 0]) with 1. rewrite sublist_same by reflexivity.
  rewrite (bytes_cs DCS.CS CS Ews 1).
  sep_apply (data_at_share_join Ews (Share.comp Ews) Tsh (tarray tuchar 1) [vi 0] vb (join_comp_Tsh Ews)).
  sep_apply (@data_at_tuchar_zero_array_inv DCS.CS Ews vb).
  entailer!.
Qed.

Lemma mt_end2_ok {Espec : OracleKind} I Iend vR vs vb gv tin tout adler msgv :
  run_mem_ok ->
  semax (Delta_m I Iend) (MT13 vR vs vb gv tin tout adler msgv) tsuf13 POST_m.
Proof.
  intros HM. unfold Delta_m, MT13, tsuf13, POST_m. simplify_func_tycontext. Intros.
  assert_PROP (field_compatible (tarray tuchar 1) [] vb) as FCb by entailer!.
  assert (Pvb : isptr vb) by (apply field_compatible_isptr in FCb; auto).
  (* deflateReset *)
  rewrite af_split. unfold af_rest. Intros.
  forward_call (2, @None dstate, vs, nullval, vb, vl tin, vl tout, msgv, vl adler,
                (@None dstate, zrst0, Z_STREAM_ERROR), gv).
  all: try (cancel; fail).
  simpl fst; simpl snd. change (if Z_STREAM_ERROR =? Z_OK then 2 else 2) with 2.
  change (Z_STREAM_ERROR =? Z_OK) with false. unfold rfv. Intros msgv1.
  match goal with Hm : msgv1 = msgv |- _ => subst msgv end.
  sep_apply (af_rest_fold vs 0 tin vb 1 tout msgv1 adler); [ assumption .. | ].
  sep_apply (af_join vs vb 0 tin vb 1 tout msgv1 adler).
  forward_call (Int.one).
  (* deflateParams *)
  assert_PROP (u32_ok 0 /\ u64_ok tin /\ u32_ok 1 /\ u64_ok tout /\ u64_ok adler) as HAF.
  { unfold api_fields. entailer!. }
  rewrite dstream_sp_eq. Intros sp.
  rewrite <- (data_at_share_join Ews (Share.comp Ews) Tsh) by apply join_comp_Tsh.
  rewrite (bytes_cs CS DCS.CS Ews 1).
  change (@data_at DCS.CS Ews (tarray tuchar 1)) with (@data_at DCS.CS Ews (tarray tuchar (Zlength [vi 0]))).
  forward_call (@None dstate, vs, nullval, sp, (Ews, nullval, nullval, nullval), vb, Ews, @nil Z, 0, 0, tin, vb,
                [vi 0], WVnone, tout, msgv1, Some 0, adler, 1, 0,
                (@None dstate, zmk [] 0 0 tin 1 tout adler (Some 0), Z_STREAM_ERROR), gv).
  { rewrite isptr_offset_val_zero by auto. rewrite Zlength_nil. simpl map.
    rewrite (@data_at_tuchar_zero_array_eq DCS.CS) by auto.
    unfold wv_at, hdr_at. change (Zlength [vi 0]) with 1. cancel. }
  { split; [| split].
    - intros X. inversion X.
    - unfold strm_ranges, zmk; simpl. unfold u32_ok, u64_ok in *.
      change (Zlength [vi 0]) with 1. rewrite Zlength_nil.
      repeat split; auto; try rep_lia.
    - exists (fun f => f). split; [ apply ef_ok_id | reflexivity ]. }
  simpl fst; simpl snd.
  unfold zmk; cbn [z_next_in z_out z_avail_in z_total_in z_avail_out z_total_out z_adler z_msg]. Intros msgv2.
  forward_call (Int.one).
  (* deflateSetDictionary *)
  rewrite Zlength_nil, !isptr_offset_val_zero by auto. simpl map.
  rewrite (@data_at_tuchar_zero_array_eq DCS.CS) by auto.
  change (map vi [] ++ sublist 0 (Zlength [vi 0]) [vi 0]) with [vi 0].
  unfold wv_at, hdr_at.
  assert (FD : dstream_sp 2 None vs nullval sp gv |-- dstream 2 None vs nullval gv)
    by (rewrite dstream_sp_eq; Exists sp; cancel).
  sep_apply FD. clear FD.
  change (@data_at DCS.CS Ews (tarray tuchar (Zlength [vi 0])) [vi 0])
    with (@data_at DCS.CS Ews (tarray tuchar (Zlength [0])) (map vi [0])).
  rewrite mt_opt_obj0.
  forward_call (@None dstate, vs, nullval, vb, 0, tin, vb, 1, tout, msgv2, Some 0, adler, vb, Ews, [0],
                (@None dstate, zmk [] 0 0 tin 1 tout adler (Some 0), Z_STREAM_ERROR), gv).
  { change (Zlength [0]) with 1. split; [rep_lia | repeat constructor; lia]. }
  simpl fst; simpl snd.
  unfold zmk; cbn [z_avail_in z_total_in z_avail_out z_total_out z_adler z_msg]. Intros msgv3.
  rewrite <- mt_opt_obj0.
  forward_call (Int.one).
  (* deflatePrime *)
  rewrite af_split.
  forward_call (@None dstate, vs, vb, nullval, 1, 1, zmk [] 0 0 tin 1 tout adler (Some 0),
                (@None dstate, zmk [] 0 0 tin 1 tout adler (Some 0), Z_STREAM_ERROR), gv).
  all: try (cancel; fail).
  simpl fst; simpl snd.
  sep_apply af_join.
  forward_call (Int.one).
  (* return 0 *)
  forward.
  Exists (Int.repr 0).
  sep_apply (proj1 HM None vs nullval gv vb 0 tin vb 1 tout msgv3 adler).
  change (Zlength [0]) with 1.
  rewrite (bytes_cs DCS.CS CS Ews 1).
  assert (JB : data_at Ews (tarray tuchar 1) [vi 0] vb * data_at (Share.comp Ews) (tarray tuchar 1) [vi 0] vb
               |-- data_at_ Tsh (tarray tuchar 1) vb).
  { rewrite (data_at_share_join Ews (Share.comp Ews) Tsh) by apply join_comp_Tsh. apply data_at_data_at_. }
  sep_apply JB. clear JB.
  assert (SPL: forall t q, data_at_ Tsh t q = data_at_ Ews t q * data_at_ (Share.comp Ews) t q)
    by (intros; unfold data_at_; symmetry; apply data_at_share_join; apply join_comp_Tsh).
  rewrite (SPL (Tstruct _z_stream_s noattr) vs).
  unfold t_drun, t_strmL. entailer!.
Qed.

(* main_tail_ok with msg_ok's need: deflate's PRE needs strm->msg pointer or null *)
Lemma main_tail_ok' {Espec : OracleKind} I Iend rf vR vs vb gv :
  run_mem_ok -> Zlib.proof.deflate.Obligations.ob_dstream_to_end -> is_pointer_or_null (rf_msgv rf) ->
  semax (Delta_m I Iend) (MA I Iend rf vR vs vb gv) msuf4 POST_m.
Proof.
  intros HM HE HP.
  apply mt_live1_ok; auto. intros.
  apply mt_live2_ok; auto. intros.
  apply mt_end1_ok; auto. intros.
  apply mt_end2_ok; auto.
Qed.

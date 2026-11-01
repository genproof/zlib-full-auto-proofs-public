(** * deflateParams() v8 (code D2): the body (deflate.c), against DSpec.deflateParams_spec (v4: on [dstream_sp], the same state
    pointer before and after; the state is re-opened after [deflate(strm, Z_BLOCK)]).  v6: the inner
    deflate(strm, Z_BLOCK) uses the model's [ef].  v8 (code D2): DEFLATE_KIND(s->level) != DEFLATE_KIND(level) is
    an int computation ([dkind] = [cfg_f] on 0..9), the model's comparison [Z.eqb]. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.DeflateKit.
#[export] Existing Instance DCS.CS.
Open Scope cmodel_scope.

(** ** Opening the stream (copied from MainDeflate.v) *)
Lemma dcheck_none_fold strmp za zf gv :
  (za = nullval \/ za = gv _zcalloc) -> (zf = nullval \/ zf = gv _zcfree) ->
  zfuncs gv * @field_at DCS.CS Ews t_strm (DOT _state) nullval strmp *
  @field_at DCS.CS Ews t_strm (DOT _zalloc) za strmp * @field_at DCS.CS Ews t_strm (DOT _zfree) zf strmp
  |-- dcheck_at None strmp nullval za zf gv.
Proof. intros. unfold dcheck_at. entailer!. Qed.

(** strm->next_in apart from the other API fields (v4: deflateStateCheck reads it). *)
Definition api_rest (strmp : val) (ain tin : Z) (nextout : val) (aout tout : Z) (msgv : val) (adler : Z) : mpred :=
  (!! (u32_ok ain /\ u64_ok tin /\ u32_ok aout /\ u64_ok tout /\ u64_ok adler) &&
   (@field_at DCS.CS Ews t_strm (DOT _avail_in) (vi ain) strmp *
    @field_at DCS.CS Ews t_strm (DOT _total_in) (vl tin) strmp *
    @field_at DCS.CS Ews t_strm (DOT _next_out) nextout strmp *
    @field_at DCS.CS Ews t_strm (DOT _avail_out) (vi aout) strmp *
    @field_at DCS.CS Ews t_strm (DOT _total_out) (vl tout) strmp *
    @field_at DCS.CS Ews t_strm (DOT _msg) msgv strmp *
    @field_at DCS.CS Ews t_strm (DOT _adler) (vl adler) strmp))%logic.

Lemma api_fields_split strmp ni ain tin no aout tout msgv adler :
  api_fields strmp ni ain tin no aout tout msgv adler |--
  @field_at DCS.CS Ews t_strm (DOT _next_in) ni strmp * api_rest strmp ain tin no aout tout msgv adler.
Proof. unfold api_fields, api_rest. Intros. entailer!. Qed.

Lemma api_fields_join strmp ni ain tin no aout tout msgv adler :
  @field_at DCS.CS Ews t_strm (DOT _next_in) ni strmp * api_rest strmp ain tin no aout tout msgv adler |--
  api_fields strmp ni ain tin no aout tout msgv adler.
Proof. unfold api_fields, api_rest. Intros. entailer!. Qed.

(** zutil.c's allocator addresses, hidden (they are not in deflate.c's type context). *)
Definition zca (gv : globals) : val := gv _zcalloc.
Definition zcf (gv : globals) : val := gv _zcfree.

(** What deflateStateCheck does not read of a live state. *)
Definition dcheck_frame (s : dstate) (p : dptrs) (gv : globals) : mpred :=
  (!! (dstate_ranges s /\ Int.min_signed <= tr_data_type (d_tr s) <= Int.max_signed) &&
   (ltree_at (tr_ltree (d_tr s)) (p_s p) * dtree_at (tr_dtree (d_tr s)) (p_s p) *
    out_at (tr_out (d_tr s)) (d_pbm s) (p_s p) (p_pbuf p) * sym_at (d_tr s) (p_s p) (p_pbuf p) *
    lvl_at (d_tr s) (p_s p) * trees_rest (d_tr s) (p_s p) (p_strm p) gv *
    @field_at DCS.CS Ews t_strm (DOT _data_type) (vi (tr_data_type (d_tr s))) (p_strm p) *
    win_at s p * hash_at s p * match_at s p * cfg_at s p *
    @field_at DCS.CS Ews t_ds (DOT _pending_buf_size) (vl (d_pending_buf_size s)) (p_s p) *
    @field_at DCS.CS Ews t_ds (DOT _pending_out) (offset_val (d_po s) (p_pbuf p)) (p_s p) *
    @field_at DCS.CS Ews t_ds (DOT _wrap) (vi (d_wrap s)) (p_s p) *
    @field_at DCS.CS Ews t_ds (DOT _gzhead) (p_gzhead p) (p_s p) *
    @field_at DCS.CS Ews t_ds (DOT _gzindex) (vl (d_gzindex s)) (p_s p) *
    @field_at DCS.CS Ews t_ds (DOT _method) (vi (d_method s)) (p_s p) *
    @field_at DCS.CS Ews t_ds (DOT _last_flush) (vi (d_last_flush s)) (p_s p)))%logic.

Lemma dcheck_split s p gv :
  dstate_at s p gv * zfuncs gv * @field_at DCS.CS Ews t_strm (DOT _state) (p_s p) (p_strm p) *
  @field_at DCS.CS Ews t_strm (DOT _zalloc) (gv _zcalloc) (p_strm p) *
  @field_at DCS.CS Ews t_strm (DOT _zfree) (gv _zcfree) (p_strm p)
  |-- dcheck_at (Some s) (p_strm p) (p_s p) (zca gv) (zcf gv) gv * dcheck_frame s p gv.
Proof.
  unfold dstate_at, dcheck_at, dcheck_frame, stat_at, dtype_at, zca, zcf. rewrite trees_at_open. unfold d_trm, dtype_at.
  cbn [fst snd]. Intros. entailer!. destruct H as (Hs & _). exact Hs.
Qed.

Lemma dcheck_join s p gv :
  dcheck_at (Some s) (p_strm p) (p_s p) (zca gv) (zcf gv) gv * dcheck_frame s p gv
  |-- dstate_at s p gv * zfuncs gv * @field_at DCS.CS Ews t_strm (DOT _state) (p_s p) (p_strm p) *
  @field_at DCS.CS Ews t_strm (DOT _zalloc) (gv _zcalloc) (p_strm p) *
  @field_at DCS.CS Ews t_strm (DOT _zfree) (gv _zcfree) (p_strm p).
Proof.
  unfold dstate_at, dcheck_at, dcheck_frame, stat_at, zca, zcf. rewrite trees_at_open. unfold d_trm, dtype_at.
  cbn [fst snd]. Intros. entailer!.
Qed.

Lemma status_ok_range x : status_ok x = true -> Int.min_signed <= x <= Int.max_signed.
Proof.
  intros E. unfold status_ok in E. repeat rewrite orb_true_iff in E. rewrite !Z.eqb_eq in E.
  unfold DState.INIT_STATE, DState.GZIP_STATE, DState.EXTRA_STATE, DState.NAME_STATE, DState.COMMENT_STATE,
    DState.HCRC_STATE, DState.BUSY_STATE, DState.FINISH_STATE in E.
  rep_lia.
Qed.

Lemma dcheck_some_eq s strmp sp gv :
  Int.min_signed <= d_status s <= Int.max_signed ->
  dcheck_at (Some s) strmp sp (zca gv) (zcf gv) gv =
  (zfuncs gv * @field_at DCS.CS Ews t_strm (DOT _state) sp strmp *
   @field_at DCS.CS Ews t_strm (DOT _zalloc) (zca gv) strmp *
   @field_at DCS.CS Ews t_strm (DOT _zfree) (zcf gv) strmp *
   (@field_at DCS.CS Ews t_ds (DOT _strm) strmp sp *
    @field_at DCS.CS Ews t_ds (DOT _status) (vi (d_status s)) sp))%logic.
Proof.
  intros. unfold dcheck_at, zca, zcf. apply pred_ext; entailer!.
Qed.

Lemma dcheck_some_fold s strmp sp gv :
  Int.min_signed <= d_status s <= Int.max_signed ->
  zfuncs gv * @field_at DCS.CS Ews t_strm (DOT _state) sp strmp *
  @field_at DCS.CS Ews t_strm (DOT _zalloc) (zca gv) strmp *
  @field_at DCS.CS Ews t_strm (DOT _zfree) (zcf gv) strmp *
  @field_at DCS.CS Ews t_ds (DOT _strm) strmp sp *
  @field_at DCS.CS Ews t_ds (DOT _status) (vi (d_status s)) sp
  |-- dcheck_at (Some s) strmp sp (zca gv) (zcf gv) gv.
Proof. intros. rewrite dcheck_some_eq by auto. cancel. Qed.

(** The live stream, opened for deflateStateCheck. *)
Definition dopen (s : dstate) (p : dptrs) (gv : globals) : mpred :=
  (dcheck_at (Some s) (p_strm p) (p_s p) (zca gv) (zcf gv) gv * dcheck_frame s p gv * dtokens s p *
   @field_at DCS.CS Ews t_strm (DOT _opaque) nullval (p_strm p) *
   @field_at_ DCS.CS Ews t_strm (DOT _reserved) (p_strm p))%logic.

Lemma dstream_open s strmp ghp sp gv :
  dstream_sp 2 (Some s) strmp ghp sp gv |--
  EX p : dptrs, !! (p_strm p = strmp /\ p_gzhead p = ghp /\ dsizes s /\ p_s p = sp) && dopen s p gv.
Proof.
  unfold dstream_sp, dopen. Intros p. Exists p. subst strmp ghp sp. unfold dstate_at'. simpl Z.eqb. cbv iota.
  sep_apply (dcheck_split s p gv). entailer!.
Qed.

Lemma dstream_close s p gv :
  dsizes s ->
  dcheck_at (Some s) (p_strm p) (p_s p) (zca gv) (zcf gv) gv * dcheck_frame s p gv * dtokens s p *
  @field_at DCS.CS Ews t_strm (DOT _opaque) nullval (p_strm p) *
  @field_at_ DCS.CS Ews t_strm (DOT _reserved) (p_strm p)
  |-- dstream_sp 2 (Some s) (p_strm p) (p_gzhead p) (p_s p) gv.
Proof.
  intros Hd. unfold dstream_sp. sep_apply (dcheck_join s p gv). Exists p. unfold dstate_at'. simpl Z.eqb. cbv iota.
  entailer!.
Qed.


Lemma hdr_at_res s ghp hx :
  hdr_at (Some s) ghp hx = (!! (d_gzhead s = None -> ghp = nullval) && hdr_res (d_gzhead s) ghp hx)%logic.
Proof.
  unfold hdr_at, hdr_res. destruct (d_gzhead s); apply pred_ext; entailer!.
Qed.


Ltac ctr := first [discriminate | contradiction |
  (exfalso; match goal with H : _ <> _ |- _ => apply H; reflexivity end)].

Ltac zall :=
  unfold Int.lt, Z_FIXED in *; rewrite ?Int.signed_repr by (unfold s32_ok in *; rep_lia);
  rewrite ?Z.geb_leb, ?Z.gtb_ltb in *;
  repeat match goal with
         | |- context [Z.ltb ?a ?b] => destruct (Z.ltb_spec a b)
         | |- context [Z.leb ?a ?b] => destruct (Z.leb_spec a b)
         | |- context [zlt ?a ?b] => destruct (zlt a b)
         | H : context [Z.ltb ?a ?b] |- _ => destruct (Z.ltb_spec a b)
         | H : context [Z.leb ?a ?b] |- _ => destruct (Z.leb_spec a b)
         end; cbn [orb andb negb] in *; try lia; try reflexivity; try ctr.

(** The rows of configuration_table. *)
Definition cfg_good (l : Z) : Z := let '(g, _, _, _, _) := Znth l config_table in g.
Definition cfg_lazy (l : Z) : Z := let '(_, a, _, _, _) := Znth l config_table in a.
Definition cfg_nice (l : Z) : Z := let '(_, _, n, _, _) := Znth l config_table in n.
Definition cfg_chain (l : Z) : Z := let '(_, _, _, c, _) := Znth l config_table in c.

Lemma cfg_Znth gv l d : 0 <= l < 10 ->
  @Znth _ d l (config_vals gv) =
  (vi (cfg_good l), (vi (cfg_lazy l), (vi (cfg_nice l), (vi (cfg_chain l), cfg_func_ptr gv (cfg_f l))))).
Proof.
  intros Hl. unfold config_vals.
  assert (E : @Znth _ d l (map (fun x : Z * Z * Z * Z * Z =>
         let '(g, l, n, c, f) := x in (vi g, (vi l, (vi n, (vi c, cfg_func_ptr gv f))))) config_table) =
     (fun x : Z * Z * Z * Z * Z =>
         let '(g, l, n, c, f) := x in (vi g, (vi l, (vi n, (vi c, cfg_func_ptr gv f))))) (Znth l config_table)).
  { unfold Znth. rewrite !if_false by lia. rewrite nth_map' with (d' := (0, 0, 0, 0, 0)).
    - reflexivity.
    - change (length config_table) with 10%nat. lia. }
  rewrite E. unfold cfg_good, cfg_lazy, cfg_nice, cfg_chain, cfg_f.
  destruct (Znth l config_table) as [[[[g a] n] c] f]. reflexivity.
Qed.

Lemma cfg_bounds l : 0 <= l < 10 ->
  0 <= cfg_good l <= 258 /\ 0 <= cfg_lazy l <= 258 /\ 0 <= cfg_nice l <= 258 /\ 0 <= cfg_chain l <= 4096 /\
  0 <= cfg_f l <= 2.
Proof.
  intros Hl. assert (l = 0 \/ l = 1 \/ l = 2 \/ l = 3 \/ l = 4 \/ l = 5 \/ l = 6 \/ l = 7 \/ l = 8 \/ l = 9) by lia.
  repeat destruct H as [H|H]; subst l; cbv; repeat split; congruence.
Qed.

(** DEFLATE_KIND(l) of the D2 code: the compressor index of configuration_table[l]. *)
Definition dkind (l : Z) : Z := if l =? 0 then 0 else if l <=? 3 then 1 else 2.

Lemma cfg_f_dkind l : 0 <= l <= 9 -> cfg_f l = dkind l.
Proof.
  intros H. assert (l = 0 \/ l = 1 \/ l = 2 \/ l = 3 \/ l = 4 \/ l = 5 \/ l = 6 \/ l = 7 \/ l = 8 \/ l = 9) by lia.
  repeat match goal with H : _ \/ _ |- _ => destruct H as [->|H] end; subst; reflexivity.
Qed.

Lemma dkind_range l : 0 <= dkind l <= 2.
Proof. unfold dkind. destruct (l =? 0); [|destruct (l <=? 3)]; lia. Qed.

Ltac dk_tac :=
  unfold dkind;
  repeat match goal with
         | H : Int.repr ?x = Int.repr ?y |- _ => apply repr_inj_signed in H; [|rep_lia|rep_lia]
         | H : Int.repr ?x <> Int.repr ?y |- _ =>
             assert (x <> y) by (intro; subst; apply H; reflexivity); clear H
         end;
  unfold Int.lt in *; rewrite ?Int.signed_repr in * by rep_lia;
  repeat match goal with
         | |- context [?a =? ?b] => destruct (Z.eqb_spec a b)
         | |- context [?a <=? ?b] => destruct (Z.leb_spec a b)
         | H : context [zlt ?a ?b] |- _ => destruct (zlt a b)
         end;
  first [reflexivity | exfalso; first [lia | ctr]].

(** The three compressors of configuration_table as function pointers (valid pointers). *)
Definition fp3 (gv : globals) : mpred :=
  (EX a : funspec, EX b : funspec, EX c : funspec,
   func_ptr' a (gv _deflate_stored) * func_ptr' b (gv _deflate_fast) * func_ptr' c (gv _deflate_slow))%logic.

Lemma fp3_fold gv a b c :
  func_ptr' c (gv _deflate_slow) * func_ptr' b (gv _deflate_fast) * func_ptr' a (gv _deflate_stored) |-- fp3 gv.
Proof. unfold fp3. Exists a b c. cancel. Qed.

Lemma fp3_valid gv f : fp3 gv |-- valid_pointer (cfg_func_ptr gv f).
Proof.
  unfold fp3, cfg_func_ptr. Intros a b c.
  destruct (f =? 0); [|destruct (f =? 1)]; auto with valid_pointer.
Qed.

Lemma fp3_isptr gv : fp3 gv |-- !! (isptr (gv _deflate_stored) /\ isptr (gv _deflate_fast) /\ isptr (gv _deflate_slow)).
Proof. unfold fp3. Intros a b c. entailer!. Qed.

#[local] Hint Resolve fp3_isptr : saturate_local.
#[local] Hint Resolve fp3_valid : valid_pointer.

Lemma fp3_emp gv : fp3 gv |-- emp.
Proof. unfold fp3. Intros a b c. sep_apply func_ptr'_emp. sep_apply func_ptr'_emp. sep_apply func_ptr'_emp. cancel. Qed.

Lemma ptr_ne_cmp v1 v2 : isptr v1 -> isptr v2 ->
  sem_cmp_pp Cne v1 v2 = Some (if Val.eq v1 v2 then Vint Int.zero else Vint Int.one).
Proof.
  intros H1 H2. destruct v1; try contradiction. destruct v2; try contradiction.
  unfold sem_cmp_pp. simpl. unfold Val.cmplu_bool.
  destruct (eq_block b b0).
  - subst b0. simpl. destruct (Val.eq (Vptr b i) (Vptr b i0)).
    + inversion e; subst i0. rewrite Ptrofs.eq_true. reflexivity.
    + rewrite Ptrofs.eq_false by congruence. reflexivity.
  - destruct (Val.eq (Vptr b i) (Vptr b0 i0)); [congruence|]. reflexivity.
Qed.


(** Freeze every SEP item but the first. *)
Ltac len_list R :=
  match R with nil => constr:(O) | _ :: ?R' => let n := len_list R' in constr:(S n) end.

Ltac freeze_but0 F :=
  match goal with |- semax _ (PROPx _ (LOCALx _ (SEPx (_ :: ?R)))) _ _ =>
    let n := len_list R in
    let L := eval compute in (map (fun k => Z.of_nat (S k)) (seq 0 n)) in
    freeze_tac L F
  end.

(** ** Folding the opened state back *)
Lemma dframe_fold s p gv :
  dstate_ranges s -> Int.min_signed <= tr_data_type (d_tr s) <= Int.max_signed ->
  ltree_at (tr_ltree (d_tr s)) (p_s p) * dtree_at (tr_dtree (d_tr s)) (p_s p) *
  out_at (tr_out (d_tr s)) (d_pbm s) (p_s p) (p_pbuf p) * sym_at (d_tr s) (p_s p) (p_pbuf p) *
  lvl_at (d_tr s) (p_s p) * trees_rest (d_tr s) (p_s p) (p_strm p) gv *
  @field_at DCS.CS Ews t_strm (DOT _data_type) (vi (tr_data_type (d_tr s))) (p_strm p) *
  win_at s p * hash_at s p * match_at s p * cfg_at s p *
  @field_at DCS.CS Ews t_ds (DOT _pending_buf_size) (vl (d_pending_buf_size s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _pending_out) (offset_val (d_po s) (p_pbuf p)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _wrap) (vi (d_wrap s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _gzhead) (p_gzhead p) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _gzindex) (vl (d_gzindex s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _method) (vi (d_method s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _last_flush) (vi (d_last_flush s)) (p_s p)
  |-- dcheck_frame s p gv.
Proof. intros. unfold dcheck_frame. entailer!. Qed.

Lemma dglobals_fold gv :
  trees_globals gv * errmsg_at gv *
  @data_at DCS.CS Ers (tarray t_config 10) (config_vals gv) (gv _configuration_table) *
  @data_at DCS.CS Ers (tarray tschar 6) (map vi [49; 46; 51; 46; 50; 0]) (gv _my_version) *
  Zlib.proof.crc32.Spec.crc_table_at Ers gv
  |-- deflate_globals gv.
Proof. unfold deflate_globals. cancel. Qed.

Lemma hdr_res_fold s ghp hx :
  (d_gzhead s = None -> ghp = nullval) -> hdr_res (d_gzhead s) ghp hx |-- hdr_at (Some s) ghp hx.
Proof. intros. rewrite hdr_at_res. entailer!. Qed.

Lemma api_fields_fold strmp nextin ain tin nextout aout tout msgv adler :
  u32_ok ain -> u64_ok tin -> u32_ok aout -> u64_ok tout -> u64_ok adler ->
  @field_at DCS.CS Ews t_strm (DOT _next_in) nextin strmp *
  @field_at DCS.CS Ews t_strm (DOT _avail_in) (vi ain) strmp *
  @field_at DCS.CS Ews t_strm (DOT _total_in) (vl tin) strmp *
  @field_at DCS.CS Ews t_strm (DOT _next_out) nextout strmp *
  @field_at DCS.CS Ews t_strm (DOT _avail_out) (vi aout) strmp *
  @field_at DCS.CS Ews t_strm (DOT _total_out) (vl tout) strmp *
  @field_at DCS.CS Ews t_strm (DOT _msg) msgv strmp *
  @field_at DCS.CS Ews t_strm (DOT _adler) (vl adler) strmp
  |-- api_fields strmp nextin ain tin nextout aout tout msgv adler.
Proof. intros. unfold api_fields. entailer!. Qed.

Lemma match_at_fold' s p :
  @field_at DCS.CS Ews t_ds (DOT _block_start) (vl (d_block_start s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _match_length) (vi (d_match_length s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _prev_match) (vi (d_prev_match s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _match_available) (vi (d_match_available s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _strstart) (vi (d_strstart s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _match_start) (vi (d_match_start s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _lookahead) (vi (d_lookahead s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _prev_length) (vi (d_prev_length s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _insert) (vi (d_insert s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _slid) (vi (d_slid s)) (p_s p)
  |-- match_at s p.
Proof. unfold match_at. cancel. Qed.

(** dcheck_frame without the groups deflateParams changes. *)
Definition dcf_rest (s : dstate) (p : dptrs) (gv : globals) : mpred :=
  (ltree_at (tr_ltree (d_tr s)) (p_s p) * dtree_at (tr_dtree (d_tr s)) (p_s p) *
   out_at (tr_out (d_tr s)) (d_pbm s) (p_s p) (p_pbuf p) * trees_rest (d_tr s) (p_s p) (p_strm p) gv *
   @field_at DCS.CS Ews t_strm (DOT _data_type) (vi (tr_data_type (d_tr s))) (p_strm p) * win_at s p *
   @field_at DCS.CS Ews t_ds (DOT _pending_buf_size) (vl (d_pending_buf_size s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _pending_out) (offset_val (d_po s) (p_pbuf p)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _wrap) (vi (d_wrap s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _gzhead) (p_gzhead p) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _gzindex) (vl (d_gzindex s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _method) (vi (d_method s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _last_flush) (vi (d_last_flush s)) (p_s p))%logic.

Lemma dframe_eq s p gv : dcheck_frame s p gv =
  (!! (dstate_ranges s /\ Int.min_signed <= tr_data_type (d_tr s) <= Int.max_signed) &&
   (dcf_rest s p gv * sym_at (d_tr s) (p_s p) (p_pbuf p) * lvl_at (d_tr s) (p_s p) * hash_at s p * match_at s p *
    cfg_at s p))%logic.
Proof. unfold dcheck_frame, dcf_rest. apply pred_ext; entailer!. Qed.

(** The rest of deflateParams after the optional deflate(strm, Z_BLOCK). *)
Definition tail_m (lv strategy : Z) (s : dstate) (z : strm) : option (dstate * strm * Z) :=
  let* s2 :=
    (if negb (d_level s =? lv) then
       let* s2 := (if ((d_level s =? 0) && negb (d_matches s =? 0))%bool then
                    let* s2 := (if d_matches s =? 1 then c_slide_hash s else c_clear_hash s) in
                    Some (set_d_matches s2 0)
                  else Some s) in
       let '(good, lazy, nice, chain, _) := Znth lv config_table in
       Some (set_d_max_chain_length (set_d_nice_match (set_d_good_match
               (set_d_max_lazy_match (set_d_level s2 lv) lazy) good) nice) chain)
     else Some s) in
  Some (set_d_strategy s2 strategy, z, DState.Z_OK).

(** ** deflate() returns one of zlib's codes (the model). *)
Local Strategy opaque [loop loop2].
Definition rc_ok (r : Z) : Prop := r = 0 \/ r = 1 \/ r = -2 \/ r = -5.

Ltac brute1 :=
  match goal with
  | Hx : None = Some _ |- _ => discriminate Hx
  | Hx : Some _ = Some _ |- _ => injection Hx; clear Hx; intros; subst
  | Hx : (match ?x with _ => _ end) = Some _ |- _ =>
      let E := fresh "E" in destruct x eqn:E; cbv beta iota zeta in Hx
  end.

Ltac brute H :=
  unfold c_flush_or_return, then_stage, bind, guard in H; cbv beta iota zeta in H;
  repeat brute1.

Ltac rc_fin := unfold rc_ok, DState.Z_OK, DState.Z_BUF_ERROR, DState.Z_STREAM_ERROR, DState.Z_STREAM_END; lia.

Definition stage_rc (x : option dres) : Prop := forall s z r, x = Some (s, z, Some r) -> rc_ok r.

Lemma rc_entry s z f : stage_rc (c_deflate_entry s z f).
Proof. intros s' z' r H. unfold c_deflate_entry in H. brute H; try rc_fin. Qed.
Lemma rc_zlib s z : stage_rc (c_deflate_zlib_header s z).
Proof. intros s' z' r H. unfold c_deflate_zlib_header in H. brute H; try rc_fin. Qed.
Lemma rc_gzip s z : stage_rc (c_deflate_gzip_header s z).
Proof. intros s' z' r H. unfold c_deflate_gzip_header in H. brute H; try rc_fin. Qed.
Lemma rc_extra s z : stage_rc (c_deflate_extra s z).
Proof. intros s' z' r H. unfold c_deflate_extra in H. brute H; try rc_fin. Qed.
Lemma rc_name s z : stage_rc (c_deflate_name s z).
Proof. intros s' z' r H. unfold c_deflate_name, c_deflate_str in H. brute H; try rc_fin. Qed.
Lemma rc_comment s z : stage_rc (c_deflate_comment s z).
Proof. intros s' z' r H. unfold c_deflate_comment, c_deflate_str in H. brute H; try rc_fin. Qed.
Lemma rc_hcrc s z : stage_rc (c_deflate_hcrc s z).
Proof. intros s' z' r H. unfold c_deflate_hcrc in H. brute H; try rc_fin. Qed.
Lemma rc_compress s z f : stage_rc (c_deflate_compress s z f).
Proof. intros s' z' r H. unfold c_deflate_compress in H. brute H; try rc_fin. Qed.

Lemma rc_trailer s z f s' z' r : c_deflate_trailer s z f = Some (s', z', r) -> rc_ok r.
Proof.
  intros H. unfold c_deflate_trailer in H. brute H;
  repeat match goal with |- context [if ?b then _ else _] => destruct b end; try rc_fin.
Qed.

Lemma then_stage_rc x k : stage_rc x -> (forall s z, stage_rc (k s z)) -> stage_rc (then_stage x k).
Proof.
  intros Hx Hk s z r H. unfold then_stage, bind in H.
  destruct x as [[[s1 z1] [c|]]|].
  - inversion H; subst. eapply Hx; reflexivity.
  - eapply Hk; exact H.
  - discriminate.
Qed.

Lemma c_deflate_rc s z f s' z' r : c_deflate s z f = Some (s', z', r) -> rc_ok r.
Proof.
  intros H. unfold c_deflate in H.
  destruct (bad_state s || (f >? DState.Z_BLOCK) || (f <? 0))%bool.
  { inversion H; subst. rc_fin. }
  unfold bind at 1 in H.
  match type of H with (match ?x with _ => _ end) = _ => destruct x as [[[s1 z1] [c|]]|] eqn:E end.
  - inversion H; subst. revert E. apply then_stage_rc.
    + apply rc_entry.
    + intros. repeat (apply then_stage_rc; [first [apply rc_zlib | apply rc_gzip | apply rc_extra | apply rc_name
        | apply rc_comment | apply rc_hcrc] | intros]). apply rc_compress.
  - eapply rc_trailer; exact H.
  - discriminate.
Qed.

Lemma rc_compress_g ef s z f : stage_rc (c_deflate_compress_g ef s z f).
Proof. intros s' z' r H. unfold c_deflate_compress_g in H. brute H; try rc_fin. Qed.

Lemma c_deflate_g_rc ef s z f s' z' r : c_deflate_g ef s z f = Some (s', z', r) -> rc_ok r.
Proof.
  intros H. unfold c_deflate_g in H.
  destruct (bad_state s || (f >? DState.Z_BLOCK) || (f <? 0))%bool.
  { inversion H; subst. rc_fin. }
  unfold bind at 1 in H.
  match type of H with (match ?x with _ => _ end) = _ => destruct x as [[[s1 z1] [c|]]|] eqn:E end.
  - inversion H; subst. revert E. apply then_stage_rc.
    + apply rc_entry.
    + intros. repeat (apply then_stage_rc; [first [apply rc_zlib | apply rc_gzip | apply rc_extra | apply rc_name
        | apply rc_comment | apply rc_hcrc] | intros]). apply rc_compress_g.
  - eapply rc_trailer; exact H.
  - discriminate.
Qed.


Ltac drop_fp3 :=
  eapply derives_trans; [apply sepcon_derives; [apply derives_refl | apply fp3_emp] |]; rewrite sepcon_emp.

(** ** The tail: the state after the level change, in a uniform form *)
Definition upd (s : dstate) (h pv : list Z) (sl m : Z) : dstate :=
  set_d_tr (set_d_slid (set_d_prev (set_d_head s h) pv) sl) (set_matches (d_tr s) m).

Definition upd2 (s : dstate) (h pv : list Z) (sl m l a g n c : Z) : dstate :=
  set_d_max_chain_length (set_d_nice_match (set_d_good_match
    (set_d_max_lazy_match (set_d_level (upd s h pv sl m) l) a) g) n) c.

Lemma upd_id s : upd s (d_head s) (d_prev s) (d_slid s) (d_matches s) = s.
Proof. destruct s as [? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? [] ?]. reflexivity. Qed.

Lemma upd2_id s : upd2 s (d_head s) (d_prev s) (d_slid s) (d_matches s) (d_level s) (d_max_lazy_match s)
  (d_good_match s) (d_nice_match s) (d_max_chain_length s) = s.
Proof. destruct s as [? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? [] ?]. reflexivity. Qed.

Lemma close_frame s p gv h pv sl m l a g n c x :
  dstate_ranges (upd s h pv sl m) -> Int.min_signed <= tr_data_type (d_tr s) <= Int.max_signed ->
  Int.min_signed <= l <= Int.max_signed -> Int.min_signed <= x <= Int.max_signed ->
  u32_ok a -> u32_ok g -> s32_ok n -> u32_ok c ->
  dcf_rest s p gv * sym_at (d_tr (upd s h pv sl m)) (p_s p) (p_pbuf p) *
  @field_at DCS.CS Ews t_ds (DOT Zlib.trees.code._level) (vi l) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT Zlib.deflate.code._strategy) (vi x) (p_s p) *
  hash_at (upd s h pv sl m) p * match_at (upd s h pv sl m) p *
  @field_at DCS.CS Ews t_ds (DOT _max_chain_length) (vi c) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _max_lazy_match) (vi a) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _good_match) (vi g) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _nice_match) (vi n) (p_s p)
  |-- dcheck_frame (set_d_strategy (upd2 s h pv sl m l a g n c) x) p gv.
Proof.
  intros Hr Hd Hl Hx Ha Hg Hn Hc. rewrite dframe_eq.
  change (dcf_rest (set_d_strategy (upd2 s h pv sl m l a g n c) x) p gv) with (dcf_rest s p gv).
  change (hash_at (set_d_strategy (upd2 s h pv sl m l a g n c) x) p) with (hash_at (upd s h pv sl m) p).
  change (match_at (set_d_strategy (upd2 s h pv sl m l a g n c) x) p) with (match_at (upd s h pv sl m) p).
  change (sym_at (d_tr (set_d_strategy (upd2 s h pv sl m l a g n c) x)) (p_s p) (p_pbuf p))
    with (sym_at (d_tr (upd s h pv sl m)) (p_s p) (p_pbuf p)).
  unfold lvl_at, cfg_at. cbn [upd2 upd set_d_strategy set_d_level set_d_max_chain_length set_d_nice_match
    set_d_good_match set_d_max_lazy_match set_d_tr set_d_slid set_d_prev set_d_head d_tr tr_level tr_strategy
    tr_data_type api_set_strategy api_set_level set_matches d_max_chain_length d_max_lazy_match d_good_match
    d_nice_match].
  entailer!.
  unfold dstate_ranges, u32_ok, s32_ok in *.
  cbn [upd2 upd set_d_strategy set_d_level set_d_max_chain_length set_d_nice_match
    set_d_good_match set_d_max_lazy_match set_d_tr set_d_slid set_d_prev set_d_head d_tr set_matches
    d_status d_pending_buf_size d_po d_wrap d_gzindex d_method d_last_flush d_w_size d_w_bits d_w_mask d_window
    d_window_size d_prev d_head d_ins_h d_hash_size d_hash_bits d_hash_mask d_hash_shift d_block_start
    d_match_length d_prev_match d_match_available d_strstart d_match_start d_lookahead d_prev_length
    d_max_chain_length d_max_lazy_match d_good_match d_nice_match d_insert d_high_water d_slid] in *.
  tauto.
Qed.

Definition inner2 (s : dstate) : option dstate :=
  if ((d_level s =? 0) && negb (d_matches s =? 0))%bool then
    let* s2 := (if d_matches s =? 1 then c_slide_hash s else c_clear_hash s) in Some (set_d_matches s2 0)
  else Some s.

Definition inner3 (lv : Z) (s : dstate) : option dstate :=
  if negb (d_level s =? lv) then
    let* s2 := inner2 s in
    let '(good, lazy, nice, chain, _) := Znth lv config_table in
    Some (set_d_max_chain_length (set_d_nice_match (set_d_good_match
            (set_d_max_lazy_match (set_d_level s2 lv) lazy) good) nice) chain)
  else Some s.

Lemma tail_m_eq lv st s z :
  tail_m lv st s z = let* s3 := inner3 lv s in Some (set_d_strategy s3 st, z, DState.Z_OK).
Proof. reflexivity. Qed.

Lemma sym_fold_m t sp pbp m :
  0 <= m <= Int.max_unsigned ->
  0 <= tr_sym_next t <= Int.max_unsigned -> 0 <= tr_sym_end t <= Int.max_unsigned ->
  0 <= tr_lit_bufsize t <= Int.max_unsigned ->
  @field_at DCS.CS Ews t_ds (DOT _sym_buf) (offset_val (tr_lit_bufsize t) pbp) sp *
  @field_at DCS.CS Ews t_ds (DOT _lit_bufsize) (vi (tr_lit_bufsize t)) sp *
  @field_at DCS.CS Ews t_ds (DOT _sym_next) (vi (tr_sym_next t)) sp *
  @field_at DCS.CS Ews t_ds (DOT _sym_end) (vi (tr_sym_end t)) sp *
  @field_at DCS.CS Ews t_ds (DOT _matches) (vi m) sp
  |-- sym_at (set_matches t m) sp pbp.
Proof. intros. unfold sym_at. cbn [set_matches tr_sym_next tr_sym_end tr_matches tr_lit_bufsize]. entailer!. Qed.

Lemma slide_inv s r : c_slide_hash s = Some r ->
  r = set_d_slid (set_d_prev (set_d_head s (map (slide_entry (d_w_size s)) (d_head s)))
                   (map (slide_entry (d_w_size s)) (d_prev s))) 1.
Proof.
  unfold c_slide_hash, bind, guard. intros H.
  match type of H with (match ?x with _ => _ end) = _ => destruct x end; [|discriminate].
  inversion H. reflexivity.
Qed.

Lemma clear_inv s r : c_clear_hash s = Some r ->
  1 <= d_hash_size s /\ Zlength (d_head s) = d_hash_size s /\
  r = set_d_slid (set_d_head s (repeat 0 (Z.to_nat (d_hash_size s)))) 0.
Proof.
  unfold c_clear_hash, bind, guard, wr. intros H.
  destruct (in_range _ _); [|discriminate].
  match type of H with context [if ?b then Some tt else None] => destruct b eqn:E end; [|discriminate].
  inversion H. rewrite andb_true_iff, Z.leb_le, Z.eqb_eq, Zlength_upd_Znth in E. tauto.
Qed.

(** ** CLEAR_HASH: zero bytes written by memset are zero unsigned shorts *)

Lemma tuchar_zero_mapsto_zeros1 sh q :
  readable_share sh ->
  @data_at DCS.CS sh tuchar (Vint Int.zero) q |-- mapsto_zeros 1 sh q.
Proof.
  intros Hsh.
  unfold data_at, field_at, at_offset. simpl.
  Intros. destruct q; try (destruct H as [Hp _]; contradiction).
  rewrite data_at_rec_eq. simpl. unfold mapsto. simpl. rewrite if_true by auto.
  destruct H as (_ & _ & Hsz & _). red in Hsz. simpl in Hsz.
  rewrite Ptrofs.add_zero.
  unfold mapsto_zeros. apply orp_left.
  - normalize. rewrite prop_true_andp by rep_lia. simpl.
    change (predicates_sl.sepcon ?a predicates_sl.emp) with (a * emp)%logic. rewrite sepcon_emp.
    apply derives_refl.
  - normalize. discriminate.
Qed.

Lemma tuchar_zeros_mapsto_zeros sh b ofs :
  readable_share sh -> 0 <= ofs ->
  forall n, 0 <= n -> ofs + n < Ptrofs.modulus ->
  @data_at DCS.CS sh (tarray tuchar n) (Zrepeat (Vint Int.zero) n) (Vptr b (Ptrofs.repr ofs))
  |-- mapsto_zeros n sh (Vptr b (Ptrofs.repr ofs)).
Proof.
  intros Hsh Ho n Hn. pattern n. revert n Hn. apply natlike_ind.
  - intros _. rewrite VST.floyd.aggregate_pred.mapsto_zeros_zero_Vptr. entailer!.
    rewrite data_at_zero_array_eq; auto.
  - intros x Hx IH Hm.
    assert_PROP (field_compatible (tarray tuchar (Z.succ x)) nil (Vptr b (Ptrofs.repr ofs))) by entailer!.
    replace (Zrepeat (Vint Int.zero) (Z.succ x)) with (Zrepeat (Vint Int.zero) x ++ [Vint Int.zero])
      by (unfold Zrepeat; rewrite Z2Nat.inj_succ by lia; rewrite <- repeat_cons; reflexivity).
    rewrite (split2_data_at_Tarray_app x (Z.succ x)) by (try rewrite Zlength_Zrepeat; list_solve).
    rewrite field_address0_offset by auto with field_compatible.
    replace (Z.succ x - x) with 1 by lia.
    rewrite (data_at_singleton_array_eq sh tuchar (Vint Int.zero)) by reflexivity.
    sep_apply IH; [lia|].
    sep_apply tuchar_zero_mapsto_zeros1.
    unfold Z.succ. rewrite VST.floyd.aggregate_pred.mapsto_zeros_split by lia.
    simpl offset_val. rewrite ptrofs_add_repr. cancel.
    replace (ofs + (0 + 1 * x)) with (ofs + x) by lia. apply derives_refl.
Qed.

(** head[hash_size-1] stored: the rest of head[] as the bytes memset clears, and the last entry. *)
Lemma head_split n p : 1 <= n -> n <= Int.max_unsigned ->
  @data_at DCS.CS Ews (tarray tushort n)
    (upd_Znth (n - 1) (default_val (tarray tushort n)) (Vint (Int.zero_ext 16 (Int.repr 0)))) p
  |-- @data_at_ DCS.CS Ews (tarray tuchar ((n - 1) * 2)) p *
      @data_at DCS.CS Ews (tarray tushort 1) [vi 0] (offset_val ((n - 1) * 2) p).
Proof.
  intros Hn Hm.
  assert_PROP (field_compatible (tarray tushort n) nil p) as Hfc by entailer!.
  replace (upd_Znth (n - 1) (default_val (tarray tushort n)) (Vint (Int.zero_ext 16 (Int.repr 0))))
    with (Zrepeat Vundef (n - 1) ++ [vi 0]).
  2: { unfold default_val. simpl. rewrite upd_Znth_unfold by (rewrite Zlength_Zrepeat; lia).
       rewrite Zlength_Zrepeat by lia. rewrite sublist_Zrepeat by lia. rewrite sublist_Zrepeat by lia.
       replace (n - (n - 1 + 1)) with 0 by lia. replace (n - 1 - 0) with (n - 1) by lia.
       reflexivity. }
  rewrite (split2_data_at_Tarray_app (n - 1) n) by (rewrite ?Zlength_Zrepeat; list_solve).
  rewrite field_address0_offset by auto with field_compatible.
  replace (n - (n - 1)) with 1 by lia.
  simpl nested_field_offset. replace (0 + 2 * (n - 1)) with ((n - 1) * 2) by lia.
  apply sepcon_derives; [|apply derives_refl].
  change (Zrepeat Vundef (n - 1)) with (default_val (tarray tushort (n - 1))).
  change (data_at Ews (tarray tushort (n - 1)) (default_val (tarray tushort (n - 1))) p)
    with (data_at_ Ews (tarray tushort (n - 1)) p).
  rewrite data_at__memory_block. Intros.
  rewrite <- memory_block_data_at__tarray_tuchar_eq by (simpl in *; rep_lia).
  simpl sizeof. replace (2 * Z.max 0 (n - 1)) with ((n - 1) * 2) by lia. apply derives_refl.
Qed.

(** The zero bytes memset wrote and the last entry: head[] all zero. *)
Lemma head_join n p : 1 <= n -> field_compatible (tarray tushort n) nil p ->
  @data_at DCS.CS Ews (tarray tuchar ((n - 1) * 2)) (Zlib.proof.zutil.Libc.byte_vals (repeat (0 mod 256) (Z.to_nat ((n - 1) * 2)))) p *
  @data_at DCS.CS Ews (tarray tushort 1) [vi 0] (offset_val ((n - 1) * 2) p)
  |-- @data_at DCS.CS Ews (tarray tushort n) (map vi (repeat 0 (Z.to_nat n))) p.
Proof.
  intros Hn Hfc.
  pose proof Hfc as Hfc'. destruct Hfc' as (Hp & _ & Hsz & _).
  destruct p; try contradiction. red in Hsz. simpl sizeof in Hsz.
  pose proof (Ptrofs.unsigned_range i) as Hi.
  rewrite <- (Ptrofs.repr_unsigned i) in Hfc |- *. set (ofs := Ptrofs.unsigned i) in *.
  assert (Hr : ofs + (n - 1) * 2 < Ptrofs.modulus) by lia.
  replace (Zlib.proof.zutil.Libc.byte_vals (repeat (0 mod 256) (Z.to_nat ((n - 1) * 2)))) with (Zrepeat (Vint Int.zero) ((n - 1) * 2))
    by (unfold Zlib.proof.zutil.Libc.byte_vals; rewrite map_repeat; reflexivity).
  sep_apply (tuchar_zeros_mapsto_zeros Ews b ofs (writable_readable writable_Ews) (proj1 Hi)
               ((n - 1) * 2) ltac:(lia) Hr).
  replace ((n - 1) * 2) with (sizeof (tarray tushort (n - 1))) at 1 by (simpl; lia).
  sep_apply (mapsto_zero_data_at_zero (tarray tushort (n - 1)) Ews); auto.
  { apply field_compatible_array_smaller0 with n; auto; lia. }
  rewrite zero_val_tarray. replace (zero_val tushort) with (vi 0) by (symmetry; apply zero_val_Tint).
  replace (map vi (repeat 0 (Z.to_nat n))) with (Zrepeat (vi 0) (n - 1) ++ [vi 0]).
  2: { unfold Zrepeat. rewrite map_repeat. replace (Z.to_nat n) with (S (Z.to_nat (n - 1))) by lia.
       rewrite <- repeat_cons. reflexivity. }
  rewrite (split2_data_at_Tarray_app (n - 1) n) by (rewrite ?Zlength_Zrepeat; list_solve).
  rewrite field_address0_offset by auto with field_compatible.
  replace (n - (n - 1)) with 1 by lia.
  simpl nested_field_offset. replace (0 + 2 * (n - 1)) with ((n - 1) * 2) by lia. cancel.
Qed.


(** head[hash_size-1] stored over arbitrary contents L. *)
Lemma head_split2 n L p : 1 <= n -> n <= Int.max_unsigned -> Zlength L = n ->
  @data_at DCS.CS Ews (tarray tushort n) (upd_Znth (n - 1) L (Vint (Int.zero_ext 16 (Int.repr 0)))) p
  |-- @data_at_ DCS.CS Ews (tarray tuchar ((n - 1) * 2)) p *
      @data_at DCS.CS Ews (tarray tushort 1) [vi 0] (offset_val ((n - 1) * 2) p).
Proof.
  intros Hn Hm HL.
  assert_PROP (field_compatible (tarray tushort n) nil p) as Hfc by entailer!.
  replace (upd_Znth (n - 1) L (Vint (Int.zero_ext 16 (Int.repr 0)))) with (sublist 0 (n - 1) L ++ [vi 0]).
  2: { rewrite upd_Znth_unfold by lia. rewrite HL. rewrite (sublist_nil_gen L (n - 1 + 1) n) by lia.
       rewrite app_nil_r. reflexivity. }
  rewrite (split2_data_at_Tarray_app (n - 1) n) by (rewrite ?Zlength_sublist; list_solve).
  rewrite field_address0_offset by auto with field_compatible.
  replace (n - (n - 1)) with 1 by lia.
  simpl nested_field_offset. replace (0 + 2 * (n - 1)) with ((n - 1) * 2) by lia.
  apply sepcon_derives; [|apply derives_refl].
  sep_apply data_at_data_at_.
  rewrite data_at__memory_block. Intros.
  rewrite <- memory_block_data_at__tarray_tuchar_eq by (simpl in *; rep_lia).
  simpl sizeof. replace (2 * Z.max 0 (n - 1)) with ((n - 1) * 2) by lia. apply derives_refl.
Qed.

Ltac drop_fp3_pre gv :=
  unfold fp3; let fa := fresh "fa" in let fb := fresh "fb" in let fc := fresh "fc" in Intros fa fb fc;
  sep_apply (func_ptr'_emp fa (gv _deflate_stored)); sep_apply (func_ptr'_emp fb (gv _deflate_fast));
  sep_apply (func_ptr'_emp fc (gv _deflate_slow)).

Lemma sym_fold t sp pbp :
  0 <= tr_sym_next t <= Int.max_unsigned -> 0 <= tr_sym_end t <= Int.max_unsigned ->
  0 <= tr_matches t <= Int.max_unsigned -> 0 <= tr_lit_bufsize t <= Int.max_unsigned ->
  @field_at DCS.CS Ews t_ds (DOT _sym_buf) (offset_val (tr_lit_bufsize t) pbp) sp *
  @field_at DCS.CS Ews t_ds (DOT _lit_bufsize) (vi (tr_lit_bufsize t)) sp *
  @field_at DCS.CS Ews t_ds (DOT _sym_next) (vi (tr_sym_next t)) sp *
  @field_at DCS.CS Ews t_ds (DOT _sym_end) (vi (tr_sym_end t)) sp *
  @field_at DCS.CS Ews t_ds (DOT _matches) (vi (tr_matches t)) sp
  |-- sym_at t sp pbp.
Proof. intros. unfold sym_at. entailer!. Qed.

Lemma dframe_fold2 s p gv :
  dstate_ranges s -> Int.min_signed <= tr_data_type (d_tr s) <= Int.max_signed ->
  dcf_rest s p gv * sym_at (d_tr s) (p_s p) (p_pbuf p) * lvl_at (d_tr s) (p_s p) * hash_at s p * match_at s p *
  cfg_at s p |-- dcheck_frame s p gv.
Proof. intros. rewrite dframe_eq. entailer!. Qed.

Lemma dsizes_slide s : dsizes s ->
  dsizes (set_d_slid (set_d_prev (set_d_head s (map (slide_entry (d_w_size s)) (d_head s)))
                   (map (slide_entry (d_w_size s)) (d_prev s))) 1).
Proof. unfold dsizes. cbn. rewrite !Zlength_map. tauto. Qed.

Lemma dsizes_clear s : dsizes s -> 0 <= d_hash_size s ->
  dsizes (set_d_slid (set_d_head s (repeat 0 (Z.to_nat (d_hash_size s)))) 0).
Proof. unfold dsizes. cbn. intros. rewrite Zlength_repeat by lia. tauto. Qed.

Lemma ranges_clear s : dstate_ranges s ->
  dstate_ranges (set_d_slid (set_d_head s (repeat 0 (Z.to_nat (d_hash_size s)))) 0).
Proof.
  unfold dstate_ranges, u32_ok, s32_ok, u64_ok, s64_ok. cbn. intros H. decompose [and] H.
  assert (F : Forall (fun x => 0 <= x < 65536) (repeat 0 (Z.to_nat (d_hash_size s)))).
  { apply Forall_forall. intros x Hx. apply repeat_spec in Hx. lia. }
  assert (Z1 : Zlength (repeat 0 (Z.to_nat (d_hash_size s))) <= 4294967295) by (rewrite Zlength_repeat; lia).
  assert (Z2 : -2147483648 <= 0 <= 2147483647) by lia.
  tauto.
Qed.

(** The state after slide_hash / CLEAR_HASH: head, prev, slid replaced. *)
Definition HP (s : dstate) (h pv : list Z) (sl : Z) : dstate := set_d_slid (set_d_prev (set_d_head s h) pv) sl.

Lemma HP_dcf s h pv sl p gv : dcf_rest (HP s h pv sl) p gv = dcf_rest s p gv.
Proof. reflexivity. Qed.
Lemma HP_sym s h pv sl sp pbp : sym_at (d_tr (HP s h pv sl)) sp pbp = sym_at (d_tr s) sp pbp.
Proof. reflexivity. Qed.
Lemma HP_lvl s h pv sl sp : lvl_at (d_tr (HP s h pv sl)) sp = lvl_at (d_tr s) sp.
Proof. reflexivity. Qed.
Lemma HP_cfg s h pv sl p : cfg_at (HP s h pv sl) p = cfg_at s p.
Proof. reflexivity. Qed.
Lemma HP_check s h pv sl a b c d gv : dcheck_at (Some (HP s h pv sl)) a b c d gv = dcheck_at (Some s) a b c d gv.
Proof. reflexivity. Qed.
Lemma upd_hash s h pv sl m p : hash_at (upd s h pv sl m) p = hash_at (HP s h pv sl) p.
Proof. reflexivity. Qed.
Lemma upd_match s h pv sl m p : match_at (upd s h pv sl m) p = match_at (HP s h pv sl) p.
Proof. reflexivity. Qed.
Lemma upd_sym s h pv sl m sp pbp : sym_at (d_tr (upd s h pv sl m)) sp pbp = sym_at (set_matches (d_tr s) m) sp pbp.
Proof. reflexivity. Qed.
Lemma upd_ranges s h pv sl m : dstate_ranges (upd s h pv sl m) = dstate_ranges (HP s h pv sl).
Proof. reflexivity. Qed.
Lemma upd_sizes s h pv sl m : dsizes (upd s h pv sl m) = dsizes (HP s h pv sl).
Proof. reflexivity. Qed.
Lemma HP_matches s h pv sl m : set_d_matches (HP s h pv sl) m = upd s h pv sl m.
Proof. reflexivity. Qed.

Lemma slide_inv' s r : c_slide_hash s = Some r ->
  r = HP s (map (slide_entry (d_w_size s)) (d_head s)) (map (slide_entry (d_w_size s)) (d_prev s)) 1.
Proof. intros H. apply slide_inv in H. exact H. Qed.

Lemma clear_inv' s r : c_clear_hash s = Some r ->
  1 <= d_hash_size s /\ Zlength (d_head s) = d_hash_size s /\
  r = HP s (repeat 0 (Z.to_nat (d_hash_size s))) (d_prev s) 0.
Proof. intros H. apply clear_inv in H. exact H. Qed.

(** The allocator fields of the stream, hidden (their globals are not in deflate.c's type context). *)
Definition zstuff (p : dptrs) (gv : globals) : mpred :=
  (zfuncs gv * @field_at DCS.CS Ews t_strm (DOT _state) (p_s p) (p_strm p) *
   @field_at DCS.CS Ews t_strm (DOT _zalloc) (gv _zcalloc) (p_strm p) *
   @field_at DCS.CS Ews t_strm (DOT _zfree) (gv _zcfree) (p_strm p))%logic.

Lemma dcheck_join' s p gv :
  dcheck_at (Some s) (p_strm p) (p_s p) (zca gv) (zcf gv) gv * dcheck_frame s p gv |-- dstate_at s p gv * zstuff p gv.
Proof. sep_apply (dcheck_join s p gv). unfold zstuff. cancel. Qed.

Lemma dcheck_split' s p gv :
  dstate_at s p gv * zstuff p gv |-- dcheck_at (Some s) (p_strm p) (p_s p) (zca gv) (zcf gv) gv * dcheck_frame s p gv.
Proof. unfold zstuff. sep_apply (dcheck_split s p gv). cancel. Qed.

Lemma sym_open t sp pbp : sym_at t sp pbp =
  (!! (0 <= tr_sym_next t <= Int.max_unsigned /\ 0 <= tr_sym_end t <= Int.max_unsigned /\
       0 <= tr_matches t <= Int.max_unsigned /\ 0 <= tr_lit_bufsize t <= Int.max_unsigned) &&
  (@field_at DCS.CS Ews t_ds (DOT _sym_buf) (offset_val (tr_lit_bufsize t) pbp) sp *
   @field_at DCS.CS Ews t_ds (DOT _lit_bufsize) (vi (tr_lit_bufsize t)) sp *
   @field_at DCS.CS Ews t_ds (DOT _sym_next) (vi (tr_sym_next t)) sp *
   @field_at DCS.CS Ews t_ds (DOT _sym_end) (vi (tr_sym_end t)) sp *
   @field_at DCS.CS Ews t_ds (DOT _matches) (vi (tr_matches t)) sp))%logic.
Proof. reflexivity. Qed.

Lemma hash_open s p : hash_at s p =
  (@field_at DCS.CS Ews t_ds (DOT _prev) (p_prev p) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _head) (p_head p) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _ins_h) (vi (d_ins_h s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _hash_size) (vi (d_hash_size s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _hash_bits) (vi (d_hash_bits s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _hash_mask) (vi (d_hash_mask s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _hash_shift) (vi (d_hash_shift s)) (p_s p) *
   @data_at DCS.CS Ews (tarray tushort (Zlength (d_prev s))) (map vi (d_prev s)) (p_prev p) *
   @data_at DCS.CS Ews (tarray tushort (Zlength (d_head s))) (map vi (d_head s)) (p_head p))%logic.
Proof. reflexivity. Qed.

Lemma match_open s p : match_at s p =
  (@field_at DCS.CS Ews t_ds (DOT _block_start) (vl (d_block_start s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _match_length) (vi (d_match_length s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _prev_match) (vi (d_prev_match s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _match_available) (vi (d_match_available s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _strstart) (vi (d_strstart s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _match_start) (vi (d_match_start s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _lookahead) (vi (d_lookahead s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _prev_length) (vi (d_prev_length s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _insert) (vi (d_insert s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _slid) (vi (d_slid s)) (p_s p))%logic.
Proof. reflexivity. Qed.

Lemma slide_entry_range ws m : 0 <= ws -> 0 <= m < 65536 -> 0 <= slide_entry ws m < 65536.
Proof. intros. unfold slide_entry, NIL. destruct (m >=? ws) eqn:E; lia. Qed.

Lemma ranges_slide s : dstate_ranges s -> 0 <= d_w_size s ->
  dstate_ranges (set_d_slid (set_d_prev (set_d_head s (map (slide_entry (d_w_size s)) (d_head s)))
                                        (map (slide_entry (d_w_size s)) (d_prev s))) 1).
Proof.
  intros Hr Hw. unfold dstate_ranges in *. simpl.
  destruct Hr as (?&?&?&?&?&?&?&?&?&?&?&?&?&Hp&Hh&Hpl&Hhl&?).
  rewrite !Zlength_map.
  assert (Hm : forall l, Forall (fun x => 0 <= x < 65536) l ->
                         Forall (fun x => 0 <= x < 65536) (map (slide_entry (d_w_size s)) l)).
  { intros l Hl. apply Forall_map. eapply Forall_impl; [|exact Hl]. intros a Ha. cbv beta in Ha. change (0 <= slide_entry (d_w_size s) a < 65536).
    apply slide_entry_range; lia. }
  intuition. unfold s32_ok. rep_lia.
Qed.

Lemma body_deflateParams : ob_deflateParams.
Proof.
  unfold ob_deflateParams.
  start_function.
  destruct H4 as (ef & Hef & H4).
  destruct os as [s0|].
  2: {
    simpl in H4. inversion H4; subst r; clear H4.
    unfold dstream_sp. Intros za zf op dt. subst ghp sp.
    sep_apply (dcheck_none_fold strmp za zf gv ltac:(assumption) ltac:(assumption)).
    sep_apply (api_fields_split strmp (offset_val nin pin) ain tin pout (Zlength rest) tout msgv adler). Intros.
    forward_call (@None dstate, strmp, nullval, za, zf, offset_val nin pin, gv).
    sep_apply (api_fields_join strmp (offset_val nin pin) ain tin pout (Zlength rest) tout msgv adler).
    simpl c_deflateStateCheck.
    forward_if; [|discriminate].
    forward.
    Exists msgv. unfold dcheck_at, dstream_sp. Intros. Exists za zf op dt.
    cbn [z_msg z_next_in z_avail_in z_total_in z_avail_out z_total_out z_adler z_out zmk app].
    rewrite Zlength_nil, sublist_same by auto. unfold hdr_at. entailer!. }
  set (z0 := zmk inb nin ain tin (Zlength rest) tout adler msg) in *.
  simpl in H4. destruct (c_deflateParams_g ef Z.eqb s0 z0 level strategy) as [[[s1 z1] rc]|] eqn:Hc; [|discriminate].
  inversion H4; subst r; clear H4.
  sep_apply (dstream_open s0 strmp ghp sp gv). Intros p. subst strmp ghp sp.
  match goal with H : dsizes s0 |- _ => rename H into Hds end.
  rewrite hdr_at_res. Intros.
  match goal with H : d_gzhead s0 = None -> _ |- _ => rename H into Hgz end.
  unfold dopen. Intros.
  sep_apply (api_fields_split (p_strm p) (offset_val nin pin) ain tin pout (Zlength rest) tout msgv adler). Intros.
  forward_call (Some s0, p_strm p, p_s p, zca gv, zcf gv, offset_val nin pin, gv).
  sep_apply (api_fields_join (p_strm p) (offset_val nin pin) ain tin pout (Zlength rest) tout msgv adler).
  unfold c_deflateParams_g in Hc.
  destruct (status_ok (d_status s0)) eqn:Est.
  2: {
    assert (Hck : c_deflateStateCheck (Some s0) = 1) by (simpl; rewrite Est; auto). rewrite Hck.
    assert (Hbs : bad_state s0 = true) by (unfold bad_state; rewrite Hck; reflexivity).
    rewrite Hbs in Hc. inversion Hc; subst s1 z1 rc; clear Hc.
    forward_if; [|ctr].
    forward. Exists msgv. sep_apply (dstream_close s0 p gv Hds). rewrite hdr_at_res.
    subst z0. cbn [z_msg z_next_in z_avail_in z_total_in z_avail_out z_total_out z_adler z_out zmk app].
    rewrite Zlength_nil, sublist_same by auto. entailer!. }
  assert (Hck : c_deflateStateCheck (Some s0) = 0) by (simpl; rewrite Est; auto). rewrite Hck.
  assert (Hbs : bad_state s0 = false) by (unfold bad_state; rewrite Hck; reflexivity).
  rewrite Hbs in Hc.
  forward_if; [ctr|].
  pose proof (status_ok_range _ Est) as Hst.
  rewrite dcheck_some_eq by exact Hst. Intros.
  forward.
  sep_apply (dcheck_some_fold s0 (p_strm p) (p_s p) gv Hst).
  set (lv := if level =? Z_DEFAULT_COMPRESSION then 6 else level) in Hc.
  assert (Hlv : Int.min_signed <= lv <= Int.max_signed).
  { unfold lv, s32_ok in *. destruct (level =? _); rep_lia. }
  forward_if_set _level (vi lv).
  { forward. entailer!. match goal with H : Int.repr level = _ |- _ => rename H into Hl end.
    change (Int.neg (Int.repr 1)) with (Int.repr (-1)) in Hl.
    apply repr_inj_signed in Hl; [|unfold s32_ok in H1; rep_lia|rep_lia]. unfold lv. rewrite Hl. reflexivity. }
  { forward. entailer!. unfold lv. destruct (Z.eqb_spec level Z_DEFAULT_COMPRESSION); [|reflexivity].
    match goal with H : Int.repr level <> _ |- _ => rename H into Hl end.
    exfalso. apply Hl. rewrite e. reflexivity. }
  forward_if_temp _t'2 (vi (if ((lv <? 0) || (lv >? 9))%bool then 1 else 0)).
  { forward. entailer!. clear Hc. unfold bool2val, vi. zall. }
  { forward. entailer!. clear Hc. unfold bool2val, vi. zall. }
  forward_if_temp _t'3 (vi (if ((lv <? 0) || (lv >? 9) || (strategy <? 0))%bool then 1 else 0)).
  { forward. entailer!. clear Hc. unfold bool2val, vi. zall. }
  { forward. entailer!. clear Hc. unfold bool2val, vi. zall. }
  forward_if_temp _t'4 (vi (if ((lv <? 0) || (lv >? 9) || (strategy <? 0) || (strategy >? Z_FIXED))%bool then 1 else 0)).
  { forward. entailer!. clear Hc. unfold bool2val, vi. zall. }
  { forward. entailer!. clear Hc. unfold bool2val, vi. zall. }
  destruct ((lv <? 0) || (lv >? 9) || (strategy <? 0) || (strategy >? Z_FIXED))%bool eqn:Ebad.
  { inversion Hc; subst s1 z1 rc; clear Hc.
    forward_if; [|ctr].
    forward. Exists msgv. sep_apply (dstream_close s0 p gv Hds). rewrite hdr_at_res.
    subst z0. cbn [z_msg z_next_in z_avail_in z_total_in z_avail_out z_total_out z_adler z_out zmk app].
    rewrite Zlength_nil, sublist_same by auto. entailer!. }
  forward_if; [ctr|].
  assert (Hok : 0 <= lv <= 9 /\ 0 <= strategy <= 4).
  { clear Hc. revert Ebad. unfold Z_FIXED. zall. }
  destruct (cfg_func (d_level s0)) as [f0|] eqn:Ecf; [|discriminate].
  assert (Hl0 : 0 <= d_level s0 <= 9 /\ f0 = cfg_f (d_level s0)).
  { clear Hc. unfold cfg_func in Ecf. destruct ((0 <=? d_level s0) && (d_level s0 <=? 9))%bool eqn:E; [|discriminate].
    rewrite andb_true_iff, !Z.leb_le in E. unfold cfg_f. destruct (Znth (d_level s0) config_table) as [[[[? ?] ?] ?] ?].
    inversion Ecf. split; auto. }
  destruct Hl0 as [Hl0 Ef0]. subst f0. assert (Hl0' : 0 <= d_level s0 < 10) by lia.
  make_func_ptr _deflate_stored. make_func_ptr _deflate_fast. make_func_ptr _deflate_slow.
  sep_apply (fp3_fold gv). 
  unfold dcheck_frame, lvl_at, deflate_globals. Intros.
  change (tr_level (d_tr s0)) with (d_level s0) in *.
  change (tr_strategy (d_tr s0)) with (d_strategy s0) in *.
  assert_PROP (isptr (gv _deflate_stored) /\ isptr (gv _deflate_fast) /\ isptr (gv _deflate_slow)) as Hfp.
  { entailer!. }
  destruct Hfp as (Hp0 & Hp1 & Hp2).
  forward.
  pose proof (cfg_bounds _ Hl0') as Hb0. pose proof (cfg_bounds lv ltac:(lia)) as Hb1.
  set (c7 := (negb (strategy =? d_strategy s0) || negb (cfg_f (d_level s0) =? cfg_f lv))%bool) in Hc.
  forward_if_temp _t'7 (vi (if c7 then 1 else 0)).
  { forward. entailer!. unfold c7. destruct (Z.eqb_spec strategy (d_strategy s0)); [|reflexivity].
    subst. contradiction. }
  { assert (Hst0 : strategy = d_strategy s0) by auto.
    forward.
    forward_if_temp _t'8 (vi (dkind (d_level s0))).
    { forward. entailer!. dk_tac. }
    { forward. forward_if.
      - forward. forward. entailer!. dk_tac.
      - forward. forward. entailer!. dk_tac. }
    forward_if_temp _t'9 (vi (dkind lv)).
    { forward. entailer!. dk_tac. }
    { forward_if.
      - forward. forward. entailer!. dk_tac.
      - forward. forward. entailer!. dk_tac. }
    forward. entailer!.
    unfold c7. rewrite ?Hst0, Z.eqb_refl, !cfg_f_dkind by lia. simpl.
    pose proof (dkind_range (d_level s0)). pose proof (dkind_range lv).
    destruct (Z.eqb_spec (dkind (d_level s0)) (dkind lv)) as [E|E].
    - rewrite E, Int.eq_true. reflexivity.
    - rewrite Int.eq_false; [reflexivity|]. intro E'. apply repr_inj_signed in E'; rep_lia. }
  set (c8 := (c7 && negb (d_last_flush s0 =? -2))%bool) in Hc.
  forward_if_temp _t'10 (vi (if c8 then 1 else 0)).
  { forward. forward. entailer!. unfold c8. destruct c7; [|ctr]. simpl.
    destruct (Z.eqb_spec (d_last_flush s0) (-2)); simpl.
    - rewrite e. reflexivity.
    - unfold dstate_ranges, s32_ok in H6. rewrite Int.eq_false; [reflexivity|].
      intro E. apply repr_inj_signed in E; rep_lia. }
  { forward. entailer!. unfold c8. destruct c7; [ctr|reflexivity]. }
  cbn [bind] in Hc.
  change ((negb (strategy =? d_strategy s0) || negb (cfg_f (d_level s0) =? cfg_f lv))%bool) with c7 in Hc.
  change ((c7 && negb (d_last_flush s0 =? -2))%bool) with c8 in Hc.
  clearbody c8.
  forward_if (EX s : dstate, EX z : strm, EX msgv' : val,
    PROP (tail_m lv strategy s z = Some (s1, z1, rc); msg_ok (z_msg z) msgv')
    LOCAL (temp _level (vi lv); temp _s (p_s p); gvars gv; temp _strm (p_strm p); temp _strategy (vi strategy))
    SEP (fp3 gv; dstream_sp 2 (Some s) (p_strm p) (p_gzhead p) (p_s p) gv;
         api_fields (p_strm p) (offset_val (z_next_in z) pin) (z_avail_in z) (z_total_in z)
           (offset_val (Zlength (z_out z)) pout) (z_avail_out z) (z_total_out z) msgv' (z_adler z);
         data_at ish (tarray tuchar (Zlength inb)) (map vi inb) pin;
         data_at Ews (tarray tuchar (Zlength rest))
           (map vi (z_out z) ++ sublist (Zlength (z_out z)) (Zlength rest) rest) pout;
         hdr_at (Some s0) (p_gzhead p) hx; deflate_globals gv; wv_at W pout)).
  2: {
    destruct c8; [ctr|].
    forward.
    sep_apply (lvl_at_fold (d_tr s0) (p_s p) H8 H9).
    sep_apply (dframe_fold s0 p gv H6 H7).
    sep_apply (dstream_close s0 p gv Hds).
    sep_apply (dglobals_fold gv).
    sep_apply (hdr_res_fold s0 (p_gzhead p) hx Hgz).
    Exists s0 z0 msgv. subst z0.
    cbn [z_msg z_next_in z_avail_in z_total_in z_avail_out z_total_out z_adler z_out zmk app].
    rewrite Zlength_nil, sublist_same by auto. simpl map. rewrite app_nil_l.
    assert_PROP (isptr pout) by entailer!. rewrite isptr_offset_val_zero by auto.
    entailer!. }
  destruct c8; [|ctr].
  destruct (c_deflate_g ef s0 z0 DState.Z_BLOCK) as [[[sd zd] err]|] eqn:Ed; [|discriminate].
  cbn [bind] in Hc.
  sep_apply (lvl_at_fold (d_tr s0) (p_s p) H8 H9).
  sep_apply (dframe_fold s0 p gv H6 H7).
  sep_apply (dstream_close s0 p gv Hds).
  sep_apply (dglobals_fold gv).
  sep_apply (hdr_res_fold s0 (p_gzhead p) hx Hgz).
  forward_call (Some s0, p_strm p, p_gzhead p, p_s p, hx, pin, ish, inb, nin, ain, tin, pout, rest, W, tout, msgv,
                msg, adler, 5, (Some sd, zd, err), gv).
  { split; [unfold s32_ok; rep_lia|]. exists ef. split; [exact Hef|]. simpl.
    change (c_deflate_g ef s0 (zmk inb nin ain tin (Zlength rest) tout adler msg) 5)
      with (c_deflate_g ef s0 z0 DState.Z_BLOCK).
    rewrite Ed. reflexivity. }
  Intros msgv1. cbn [fst snd] in *.
  assert (Hrc : rc_ok err) by (eapply c_deflate_g_rc; eauto).
  destruct (Z.eqb_spec err DState.Z_STREAM_ERROR) as [Eerr|Eerr].
  { cbn [bind] in Hc. inversion Hc; subst s1 z1 rc; clear Hc.
    forward_if; [|exfalso; match goal with Hn : Int.repr _ <> _ |- _ => apply Hn end; subst; reflexivity].
    forward. Exists msgv1. drop_fp3. entailer!. }
  cbn [fst snd] in *. cbn [bind] in Hc.
  match goal with |- semax _ ?Pre _ _ => forward_if Pre end.
  { exfalso. apply Eerr. match goal with Hx : Int.repr err = _ |- _ => rename Hx into Herr end.
    change (Int.neg (Int.repr 2)) with (Int.repr (-2)) in Herr.
    apply repr_inj_signed in Herr; [exact Herr| |rep_lia]. unfold rc_ok in Hrc; rep_lia. }
  { forward. all: entailer!. }
  unfold api_fields. Intros.
  forward.
  destruct (Z.eqb_spec (z_avail_in zd) 0) as [Eai|Eai]; cbn [negb] in Hc.
  2: {
    cbn [bind] in Hc. inversion Hc; subst s1 z1 rc; clear Hc.
    forward_if_temp _t'6 (vi 1).
    { forward. entailer!. }
    { exfalso. apply Eai. apply repr_inj_unsigned; [unfold u32_ok in *; rep_lia | rep_lia | assumption]. }
    forward_if; [|ctr].
    forward. Exists msgv1. drop_fp3. unfold api_fields. entailer!. }
  unfold guard in Hc.
  destruct (in_long (d_strstart sd - d_block_start sd)) eqn:G1; [|cbn [bind] in Hc; discriminate].
  destruct (in_long (d_strstart sd - d_block_start sd + d_lookahead sd)) eqn:G2; [|cbn [bind] in Hc; discriminate].
  cbn [bind] in Hc.
  rewrite Eai in *.
  sep_apply (dstream_open sd (p_strm p) (p_gzhead p) (p_s p) gv). Intros p'.
  match goal with Hx : p_s p' = p_s p |- _ => rename Hx into Esp end.
  match goal with Hx : p_strm p' = p_strm p |- _ => rename Hx into Estr end.
  match goal with Hx : p_gzhead p' = p_gzhead p |- _ => rename Hx into Egz end.
  match goal with Hx : dsizes sd |- _ => rename Hx into Hdsd end.
  rewrite <- Esp, <- Estr, <- Egz.
  unfold dopen, dcheck_frame, match_at. Intros.
  match goal with Hx : dstate_ranges sd |- _ => rename Hx into Hrd end.
  forward_if_temp _t'6 (vi (if d_strstart sd - d_block_start sd + d_lookahead sd =? 0 then 0 else 1)).
  { ctr. }
  { forward. forward. forward. forward.
    { entailer!. clear - Hrd G1 G2. unfold in_long in G1, G2. rewrite andb_true_iff, !Z.leb_le in G1, G2.
      open_dranges Hrd. rewrite !Int.unsigned_repr by rep_lia. rewrite !Int64.signed_repr by rep_lia. rep_lia. }
    entailer!. clear - Hrd G1 G2. unfold in_long in G1, G2. rewrite andb_true_iff, !Z.leb_le in G1, G2.
    open_dranges Hrd. rewrite !Int.unsigned_repr by rep_lia.
    destruct (Z.eqb_spec (d_strstart sd - d_block_start sd + d_lookahead sd) 0) as [E|E].
    - rewrite E. reflexivity.
    - rewrite Int64.eq_false; [reflexivity|]. intro Ex. apply E. apply (f_equal Int64.signed) in Ex.
      rewrite Int64.signed_repr in Ex by rep_lia. exact Ex. }
  match goal with Hx : Int.min_signed <= tr_data_type (d_tr sd) <= _ |- _ => rename Hx into Hdt end.
  sep_apply (match_at_fold' sd p'). sep_apply (dframe_fold sd p' gv Hrd Hdt).
  sep_apply (dstream_close sd p' gv Hdsd).
  match goal with Hx : u32_ok 0 |- _ => rename Hx into Ha1 end.
  match goal with Hx : u64_ok (z_total_in zd) |- _ => rename Hx into Ha2 end.
  match goal with Hx : u32_ok (z_avail_out zd) |- _ => rename Hx into Ha3 end.
  match goal with Hx : u64_ok (z_total_out zd) |- _ => rename Hx into Ha4 end.
  match goal with Hx : u64_ok (z_adler zd) |- _ => rename Hx into Ha5 end.
  sep_apply (api_fields_fold (p_strm p') (offset_val (z_next_in zd) pin) 0 (z_total_in zd)
    (offset_val (Zlength (z_out zd)) pout) (z_avail_out zd) (z_total_out zd) msgv1 (z_adler zd) Ha1 Ha2 Ha3 Ha4 Ha5).
  rewrite Esp, Estr, Egz.
  destruct (Z.eqb_spec (d_strstart sd - d_block_start sd + d_lookahead sd) 0) as [Ed0|Ed0]; cbn [negb bind] in Hc.
  2: {
    inversion Hc; subst s1 z1 rc; clear Hc.
    forward_if; [|ctr].
    forward. Exists msgv1. drop_fp3. rewrite Eai. entailer!. }
  forward_if; [ctr|].
  forward.
  Exists sd zd msgv1. rewrite Eai. entailer!.
  (** The tail: level and strategy. *)
  clear Hc. Intros sT zT msgvT.
  match goal with Hx : tail_m _ _ _ _ = _ |- _ => rename Hx into Htail end.
  sep_apply (dstream_open sT (p_strm p) (p_gzhead p) (p_s p) gv). Intros p2.
  match goal with Hx : p_s p2 = p_s p |- _ => rename Hx into Esp end.
  match goal with Hx : p_strm p2 = p_strm p |- _ => rename Hx into Estr end.
  match goal with Hx : p_gzhead p2 = p_gzhead p |- _ => rename Hx into Egz end.
  match goal with Hx : dsizes sT |- _ => rename Hx into HdsT end.
  rewrite <- Esp, <- Estr, <- Egz.
  unfold dopen. Intros. rewrite dframe_eq. Intros.
  match goal with Hx : dstate_ranges sT |- _ => rename Hx into HrT end.
  match goal with Hx : Int.min_signed <= tr_data_type (d_tr sT) <= _ |- _ => rename Hx into HdtT end.
  unfold lvl_at. Intros.
  forward.
  rewrite tail_m_eq in Htail.
  destruct (inner3 lv sT) as [s3|] eqn:Hin3; [|discriminate]. cbn [bind] in Htail.
  inversion Htail; subst s1 z1 rc; clear Htail.
  forward_if (EX h : list Z, EX pv : list Z, EX sl : Z, EX m : Z, EX l : Z, EX a : Z, EX g : Z, EX n : Z, EX c : Z,
    PROP (s3 = upd2 sT h pv sl m l a g n c; dstate_ranges (upd sT h pv sl m); dsizes (upd sT h pv sl m);
          Int.min_signed <= l <= Int.max_signed; u32_ok a; u32_ok g; s32_ok n; u32_ok c)
    LOCAL (temp _level (vi lv); temp _s (p_s p2); gvars gv; temp _strm (p_strm p2); temp _strategy (vi strategy))
    SEP (fp3 gv; dcheck_at (Some sT) (p_strm p2) (p_s p2) (zca gv) (zcf gv) gv; dcf_rest sT p2 gv;
         sym_at (d_tr (upd sT h pv sl m)) (p_s p2) (p_pbuf p2);
         field_at Ews t_ds (DOT Zlib.trees.code._level) (vi l) (p_s p2);
         field_at Ews t_ds (DOT Zlib.deflate.code._strategy) (vi (tr_strategy (d_tr sT))) (p_s p2);
         hash_at (upd sT h pv sl m) p2; match_at (upd sT h pv sl m) p2;
         field_at Ews t_ds (DOT _max_chain_length) (vi c) (p_s p2);
         field_at Ews t_ds (DOT _max_lazy_match) (vi a) (p_s p2);
         field_at Ews t_ds (DOT _good_match) (vi g) (p_s p2);
         field_at Ews t_ds (DOT _nice_match) (vi n) (p_s p2);
         dtokens sT p2; field_at Ews t_strm (DOT _opaque) nullval (p_strm p2);
         field_at_ Ews t_strm (DOT _reserved) (p_strm p2);
         api_fields (p_strm p2) (offset_val (z_next_in zT) pin) (z_avail_in zT) (z_total_in zT)
           (offset_val (Zlength (z_out zT)) pout) (z_avail_out zT) (z_total_out zT) msgvT (z_adler zT);
         data_at ish (tarray tuchar (Zlength inb)) (map vi inb) pin;
         data_at Ews (tarray tuchar (Zlength rest))
           (map vi (z_out zT) ++ sublist (Zlength (z_out zT)) (Zlength rest) rest) pout;
         hdr_at (Some s0) (p_gzhead p2) hx; deflate_globals gv; wv_at W pout))%assert.
  2: {
    forward.
    match goal with Hx : tr_level (d_tr sT) = lv |- _ => rename Hx into Elv end.
    unfold inner3 in Hin3. change (tr_level (d_tr sT)) with (d_level sT) in Elv. rewrite Elv, Z.eqb_refl in Hin3.
    cbn [negb] in Hin3. inversion Hin3; subst s3; clear Hin3.
    Exists (d_head sT) (d_prev sT) (d_slid sT) (d_matches sT) (d_level sT) (d_max_lazy_match sT)
      (d_good_match sT) (d_nice_match sT) (d_max_chain_length sT).
    rewrite upd2_id, upd_id. unfold cfg_at. entailer!.
    unfold dstate_ranges in HrT. tauto. }
  2: {
    Intros h pv sl m l a g n c. subst s3.
    match goal with Hx : dstate_ranges (upd _ _ _ _ _) |- _ => rename Hx into Hru end.
    match goal with Hx : dsizes (upd _ _ _ _ _) |- _ => rename Hx into Hdsu end.
    match goal with Hx : Int.min_signed <= l <= _ |- _ => rename Hx into Hl end.
    match goal with Hx : u32_ok a |- _ => rename Hx into Ha end.
    match goal with Hx : u32_ok g |- _ => rename Hx into Hg end.
    match goal with Hx : s32_ok n |- _ => rename Hx into Hn end.
    match goal with Hx : u32_ok c |- _ => rename Hx into Hc4 end.
    forward.
    assert (Hs : Int.min_signed <= strategy <= Int.max_signed) by (unfold s32_ok in H2; rep_lia).
    sep_apply (close_frame sT p2 gv h pv sl m l a g n c strategy Hru HdtT Hl Hs Ha Hg Hn Hc4).
    set (S4 := set_d_strategy (upd2 sT h pv sl m l a g n c) strategy).
    change (dcheck_at (Some sT) (p_strm p2) (p_s p2) (zca gv) (zcf gv) gv)
      with (dcheck_at (Some S4) (p_strm p2) (p_s p2) (zca gv) (zcf gv) gv).
    change (dtokens sT p2) with (dtokens S4 p2).
    assert (Hds4 : dsizes S4) by exact Hdsu.
    sep_apply (dstream_close S4 p2 gv Hds4).
    drop_fp3_pre gv.
    rewrite Esp, Estr, Egz.
    forward.
    Exists msgvT. unfold S4. entailer!. }
  { (* the level changes *)
    match goal with Hx : tr_level (d_tr sT) <> lv |- _ => rename Hx into Nlv end.
    unfold inner3 in Hin3. change (tr_level (d_tr sT)) with (d_level sT) in Nlv.
    rewrite (proj2 (Z.eqb_neq _ _) Nlv) in Hin3. cbn [negb] in Hin3.
    destruct (inner2 sT) as [s2|] eqn:Hin2; [|discriminate]. cbn [bind] in Hin3.
    forward.
    unfold sym_at. Intros.
    match goal with Hx : 0 <= tr_sym_next (d_tr sT) <= _ |- _ => rename Hx into Hsy1 end.
    match goal with Hx : 0 <= tr_sym_end (d_tr sT) <= _ |- _ => rename Hx into Hsy2 end.
    match goal with Hx : 0 <= tr_matches (d_tr sT) <= _ |- _ => rename Hx into Hsy3 end.
    match goal with Hx : 0 <= tr_lit_bufsize (d_tr sT) <= _ |- _ => rename Hx into Hsy4 end.
    forward_if_temp _t'11 (vi (if ((d_level sT =? 0) && negb (d_matches sT =? 0))%bool then 1 else 0)).
    { forward. forward. entailer!.
      match goal with Hx : tr_level (d_tr sT) = 0 |- _ => unfold d_level, d_matches; rewrite Hx end.
      destruct (zeq _ 0) as [E|E]; [rewrite E | rewrite (proj2 (Z.eqb_neq _ _) E)]; reflexivity. }
    { forward. entailer!.
      match goal with Hx : tr_level (d_tr sT) <> 0 |- _ => unfold d_level; rewrite (proj2 (Z.eqb_neq _ _) Hx) end.
      reflexivity. }
    forward_if (EX h : list Z, EX pv : list Z, EX sl : Z, EX m : Z,
      PROP (s2 = upd sT h pv sl m; dstate_ranges (upd sT h pv sl m); dsizes (upd sT h pv sl m))
      LOCAL (temp _level (vi lv); temp _s (p_s p2); gvars gv; temp _strm (p_strm p2); temp _strategy (vi strategy))
      SEP (fp3 gv; dcheck_at (Some sT) (p_strm p2) (p_s p2) (zca gv) (zcf gv) gv; dcf_rest sT p2 gv;
           sym_at (d_tr (upd sT h pv sl m)) (p_s p2) (p_pbuf p2);
           field_at Ews t_ds (DOT Zlib.trees.code._level) (vi (tr_level (d_tr sT))) (p_s p2);
           field_at Ews t_ds (DOT Zlib.deflate.code._strategy) (vi (tr_strategy (d_tr sT))) (p_s p2);
           hash_at (upd sT h pv sl m) p2; match_at (upd sT h pv sl m) p2; cfg_at sT p2;
           dtokens sT p2; field_at Ews t_strm (DOT _opaque) nullval (p_strm p2);
           field_at_ Ews t_strm (DOT _reserved) (p_strm p2);
           api_fields (p_strm p2) (offset_val (z_next_in zT) pin) (z_avail_in zT) (z_total_in zT)
             (offset_val (Zlength (z_out zT)) pout) (z_avail_out zT) (z_total_out zT) msgvT (z_adler zT);
           data_at ish (tarray tuchar (Zlength inb)) (map vi inb) pin;
           data_at Ews (tarray tuchar (Zlength rest))
             (map vi (z_out zT) ++ sublist (Zlength (z_out zT)) (Zlength rest) rest) pout;
           hdr_at (Some s0) (p_gzhead p2) hx; deflate_globals gv; wv_at W pout))%assert.
    { (* slide or clear *)
      destruct ((d_level sT =? 0) && negb (d_matches sT =? 0))%bool eqn:E9; [|ctr].
      unfold inner2 in Hin2. rewrite E9 in Hin2.
      forward.
      sep_apply (sym_fold (d_tr sT) (p_s p2) (p_pbuf p2) Hsy1 Hsy2 Hsy3 Hsy4).
      destruct (Z.eqb_spec (d_matches sT) 1) as [M1|M1].
      - destruct (c_slide_hash sT) as [r|] eqn:Hr; [|discriminate]. cbn [bind] in Hin2.
        inversion Hin2; subst s2; clear Hin2.
        pose proof (slide_inv' _ _ Hr) as Er.
        forward_if (PROP () LOCAL (temp _level (vi lv); temp _s (p_s p2); gvars gv; temp _strm (p_strm p2); temp _strategy (vi strategy))
          SEP (fp3 gv; dcheck_at (Some sT) (p_strm p2) (p_s p2) (zca gv) (zcf gv) gv; dcf_rest sT p2 gv;
           sym_at (d_tr sT) (p_s p2) (p_pbuf p2);
           field_at Ews t_ds (DOT Zlib.trees.code._level) (vi (tr_level (d_tr sT))) (p_s p2);
           field_at Ews t_ds (DOT Zlib.deflate.code._strategy) (vi (tr_strategy (d_tr sT))) (p_s p2);
           hash_at r p2; match_at r p2; cfg_at sT p2;
           dtokens sT p2; field_at Ews t_strm (DOT _opaque) nullval (p_strm p2);
           field_at_ Ews t_strm (DOT _reserved) (p_strm p2);
           api_fields (p_strm p2) (offset_val (z_next_in zT) pin) (z_avail_in zT) (z_total_in zT)
             (offset_val (Zlength (z_out zT)) pout) (z_avail_out zT) (z_total_out zT) msgvT (z_adler zT);
           data_at ish (tarray tuchar (Zlength inb)) (map vi inb) pin;
           data_at Ews (tarray tuchar (Zlength rest))
             (map vi (z_out zT) ++ sublist (Zlength (z_out zT)) (Zlength rest) rest) pout;
           hdr_at (Some s0) (p_gzhead p2) hx; deflate_globals gv; wv_at W pout)).
        { sep_apply (lvl_at_fold (d_tr sT) (p_s p2) H10 H12).
          sep_apply (dframe_fold2 sT p2 gv HrT HdtT).
          sep_apply (dcheck_join' sT p2 gv).
          forward_call (sT, p2, r, gv).
          1: cancel.
          sep_apply (dcheck_split' r p2 gv). rewrite dframe_eq. Intros.
          rewrite Er, HP_dcf, HP_sym, HP_lvl, HP_cfg, HP_check. rewrite <- Er.
          unfold lvl_at. Intros. entailer!. }
        { exfalso. match goal with Hx : tr_matches (d_tr sT) <> 1 |- _ => apply Hx; exact M1 end. }
        rewrite (sym_open (d_tr sT) (p_s p2) (p_pbuf p2)). Intros. forward.
        Exists (map (slide_entry (d_w_size sT)) (d_head sT)) (map (slide_entry (d_w_size sT)) (d_prev sT)) 1 0.
        rewrite upd_hash, upd_match, upd_sym, upd_ranges, upd_sizes, <- HP_matches, <- Er.
        sep_apply (sym_fold_m (d_tr sT) (p_s p2) (p_pbuf p2) 0 ltac:(rep_lia) Hsy1 Hsy2 Hsy4).
        assert (Hdsr : dsizes r) by (rewrite Er; apply dsizes_slide; exact HdsT).
        assert (Hrr : dstate_ranges r) by (rewrite Er; apply ranges_slide; [exact HrT | unfold dstate_ranges, u32_ok in HrT; tauto]).
        entailer!.
      - destruct (c_clear_hash sT) as [r|] eqn:Hr; [|discriminate]. cbn [bind] in Hin2.
        inversion Hin2; subst s2; clear Hin2.
        destruct (clear_inv' _ _ Hr) as (Hhs1 & Hhl & Er).
        forward_if (PROP () LOCAL (temp _level (vi lv); temp _s (p_s p2); gvars gv; temp _strm (p_strm p2); temp _strategy (vi strategy))
          SEP (fp3 gv; dcheck_at (Some sT) (p_strm p2) (p_s p2) (zca gv) (zcf gv) gv; dcf_rest sT p2 gv;
           sym_at (d_tr sT) (p_s p2) (p_pbuf p2);
           field_at Ews t_ds (DOT Zlib.trees.code._level) (vi (tr_level (d_tr sT))) (p_s p2);
           field_at Ews t_ds (DOT Zlib.deflate.code._strategy) (vi (tr_strategy (d_tr sT))) (p_s p2);
           hash_at r p2; match_at r p2; cfg_at sT p2;
           dtokens sT p2; field_at Ews t_strm (DOT _opaque) nullval (p_strm p2);
           field_at_ Ews t_strm (DOT _reserved) (p_strm p2);
           api_fields (p_strm p2) (offset_val (z_next_in zT) pin) (z_avail_in zT) (z_total_in zT)
             (offset_val (Zlength (z_out zT)) pout) (z_avail_out zT) (z_total_out zT) msgvT (z_adler zT);
           data_at ish (tarray tuchar (Zlength inb)) (map vi inb) pin;
           data_at Ews (tarray tuchar (Zlength rest))
             (map vi (z_out zT) ++ sublist (Zlength (z_out zT)) (Zlength rest) rest) pout;
           hdr_at (Some s0) (p_gzhead p2) hx; deflate_globals gv; wv_at W pout)).
        { exfalso. match goal with Hx : tr_matches (d_tr sT) = 1 |- _ => apply M1; exact Hx end. }
        { apply semax_loop_nocontinue.
          rewrite (hash_open sT p2). Intros. forward. forward.
          rewrite Hhl.
          assert (Hhsu : d_hash_size sT <= Int.max_unsigned) by (unfold dstate_ranges, u32_ok in HrT; tauto).
          assert_PROP (field_compatible (tarray tushort (d_hash_size sT)) nil (p_head p2)) as Hfc by entailer!.
          forward.
          sep_apply (head_split2 (d_hash_size sT) (map vi (d_head sT)) (p_head p2) Hhs1 Hhsu
            ltac:(rewrite Zlength_map; exact Hhl)). Intros.
          forward. forward.
          forward_call (Ews, p_head p2, (d_hash_size sT - 1) * 2, 0).
          sep_apply (head_join (d_hash_size sT) (p_head p2) Hhs1 Hfc).
          rewrite (match_open sT p2). Intros. forward. forward.
          rewrite Er, (hash_open (HP _ _ _ _) p2), (match_open (HP _ _ _ _) p2). unfold HP. dsimpl.
          rewrite Zlength_repeat by lia. entailer!. }
        rewrite (sym_open (d_tr sT) (p_s p2) (p_pbuf p2)). Intros. forward.
        Exists (repeat 0 (Z.to_nat (d_hash_size sT))) (d_prev sT) 0 0.
        rewrite upd_hash, upd_match, upd_sym, upd_ranges, upd_sizes, <- HP_matches, <- Er.
        sep_apply (sym_fold_m (d_tr sT) (p_s p2) (p_pbuf p2) 0 ltac:(rep_lia) Hsy1 Hsy2 Hsy4).
        assert (Hdsr : dsizes r) by (rewrite Er; exact (dsizes_clear sT HdsT ltac:(lia))).
        assert (Hrr : dstate_ranges r) by (rewrite Er; exact (ranges_clear sT HrT)).
        entailer!. }
    { (* nothing to clear *)
      destruct ((d_level sT =? 0) && negb (d_matches sT =? 0))%bool eqn:E9; [ctr|].
      unfold inner2 in Hin2. rewrite E9 in Hin2. inversion Hin2; subst s2; clear Hin2.
      forward.
      Exists (d_head sT) (d_prev sT) (d_slid sT) (d_matches sT). rewrite upd_id.
      sep_apply (sym_fold (d_tr sT) (p_s p2) (p_pbuf p2) Hsy1 Hsy2 Hsy3 Hsy4).
      entailer!. }
    Intros h pv sl m. subst s2.
    match goal with Hx : dstate_ranges (upd _ _ _ _ _) |- _ => rename Hx into Hru end.
    match goal with Hx : dsizes (upd _ _ _ _ _) |- _ => rename Hx into Hdsu end.
    forward.
    unfold cfg_at, deflate_globals. Intros.
    forward. 1: (entailer!; rewrite (cfg_Znth gv lv) by lia; cbv beta iota; simpl;
                 rewrite Int.unsigned_repr by rep_lia; rep_lia).
    rewrite (cfg_Znth gv lv) by lia; cbv beta iota. forward.
    forward. 1: (entailer!; rewrite (cfg_Znth gv lv) by lia; cbv beta iota; simpl;
                 rewrite Int.unsigned_repr by rep_lia; rep_lia).
    rewrite (cfg_Znth gv lv) by lia; cbv beta iota. forward.
    forward. 1: (entailer!; rewrite (cfg_Znth gv lv) by lia; cbv beta iota; simpl;
                 rewrite Int.unsigned_repr by rep_lia; rep_lia).
    rewrite (cfg_Znth gv lv) by lia; cbv beta iota. forward.
    forward. 1: (entailer!; rewrite (cfg_Znth gv lv) by lia; cbv beta iota; simpl;
                 rewrite Int.unsigned_repr by rep_lia; rep_lia).
    rewrite (cfg_Znth gv lv) by lia; cbv beta iota. forward.
    assert (Es3 : s3 = upd2 sT h pv sl m lv (cfg_lazy lv) (cfg_good lv) (cfg_nice lv) (cfg_chain lv)).
    { unfold cfg_lazy, cfg_good, cfg_nice, cfg_chain.
      destruct (Znth lv config_table) as [[[[g' a'] n'] c'] f']. inversion Hin3. reflexivity. }
    Exists h pv sl m lv (cfg_lazy lv) (cfg_good lv) (cfg_nice lv) (cfg_chain lv).
    sep_apply (dglobals_fold gv).
    entailer!. unfold u32_ok, s32_ok. rep_lia. }
Qed.

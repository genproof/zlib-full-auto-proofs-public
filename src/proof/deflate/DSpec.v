(** * THE specifications of deflate.c's functions (one per function, shared by every law)

    Uniform shape (see TSpec.v): the representation of what the function touches (DRep.v, TRep.v) and the
    checked model run (DModel*.v) [c_f args = Some r]; the postcondition is the representation of [r].

    Internal functions of deflate.c whose model takes the whole stream ([dstate] and [strm]) are specified on
    the whole stream [dfull] (all fields of deflate_state and of the z_stream, the input object of the call and
    the output space), so no frame lemmas are needed; proofs unfold only the groups they use.  The leaves
    read_buf, putShortMSB and flush_pending are specified on exactly what they touch, because their callers
    hand them pieces (read_buf writes into a slice of the window or of the output space).

    The API functions (deflateInit2_, deflate, deflateEnd, ...) are specified on the abstract stream
    [dstream lvl os strmp ghp gv] (pointers hidden; [os = None]: no state, e.g. after deflateEnd) and the
    z_stream fields the caller sets and reads between calls, given explicitly ([api_fields]): next_in,
    avail_in, total_in, next_out, avail_out, total_out, msg, adler.  [lvl] (v2) is the initialisation level of the
    state (2 = complete; 1 = head[] undefined; 0 = also the tree descriptors not yet set): only deflateResetKeep,
    deflateReset and deflateStateCheck accept lvl < 2 (deflateInit2_ calls deflateReset right after zmemzero).
    The user's gzip header ([gzh_at], the caller's memory) is given to the functions that read it (deflate,
    deflateBound, deflateParams) when the state has one ([hdr_at]). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Zlib.proof.deflate.DCS.
Require Export Zlib.proof.deflate.DRep.
Require Export Zlib.proof.trees.TSpec.
Require Export Zlib.proof.deflate.DModel4.
Require Export Zlib.proof.deflate.DModel5.
Require Import Zlib.proof.zutil.Libc Zlib.proof.zutil.Spec.
Require Import Zlib.proof.adler32.Spec Zlib.proof.crc32.Spec.
Require Import Zlib.deflate.code.

#[export] Existing Instance DCS.CS.

Definition Vprog : varspecs. mk_varspecs Zlib.deflate.code.prog. Defined.

Definition t_config := Tstruct _config_s noattr.

(** ** Globals read by deflate.c *)
Definition cfg_func_ptr (gv : globals) (f : Z) : val :=
  if f =? 0 then gv _deflate_stored else if f =? 1 then gv _deflate_fast else gv _deflate_slow.

(** v6 (DModel5): Floyd cannot prove the three function addresses distinct.  [ef_ok gv ef]: the function
    [ef f] has the address of the function [f] of configuration_table, so a call of [f] (by name or through
    configuration_table) may use the specification of [ef f].  [ef = fun f => f] always qualifies
    ([ef_ok_id]).  [gv_feq gv i j]: deflateParams' comparison of the two function pointers. *)
Definition ef_ok (gv : globals) (ef : Z -> Z) : Prop :=
  forall f, 0 <= f <= 2 -> 0 <= ef f <= 2 /\ cfg_func_ptr gv (ef f) = cfg_func_ptr gv f.

Definition gv_feq (gv : globals) (i j : Z) : bool :=
  if Val.eq (cfg_func_ptr gv i) (cfg_func_ptr gv j) then true else false.

Lemma ef_ok_id : forall gv, ef_ok gv (fun f => f).
Proof. intros gv f Hf. split; [lia | reflexivity]. Qed.

(** With distinct addresses, [gv_feq] is index equality on the three functions. *)
Lemma gv_feq_distinct : forall gv,
    gv _deflate_stored <> gv _deflate_fast -> gv _deflate_stored <> gv _deflate_slow ->
    gv _deflate_fast <> gv _deflate_slow ->
    forall i j, 0 <= i <= 2 -> 0 <= j <= 2 -> gv_feq gv i j = (i =? j).
Proof.
  intros gv H01 H02 H12 i j Hi Hj. unfold gv_feq, cfg_func_ptr.
  assert (i = 0 \/ i = 1 \/ i = 2) as [-> | [-> | ->]] by lia;
  assert (j = 0 \/ j = 1 \/ j = 2) as [-> | [-> | ->]] by lia; cbn;
  repeat match goal with |- context [Val.eq ?a ?b] => destruct (Val.eq a b) end;
  try reflexivity; congruence.
Qed.

Definition config_vals (gv : globals) : list (reptype t_config) :=
  map (fun x : Z * Z * Z * Z * Z =>
         let '(g, l, n, c, f) := x in (vi g, (vi l, (vi n, (vi c, cfg_func_ptr gv f))))) config_table.

Definition deflate_globals (gv : globals) : mpred :=
  (trees_globals gv * errmsg_at gv *
   @data_at DCS.CS Ers (tarray t_config 10) (config_vals gv) (gv _configuration_table) *
   @data_at DCS.CS Ers (tarray tschar 6) (map vi [49; 46; 51; 46; 50; 0]) (gv _my_version) *
   crc_table_at Ers gv)%logic.

(** ** The whole stream during a call *)
Definition dfull (s : dstate) (z : strm) (p : dptrs) (pin pout : val) (ish : share) (rest : list val)
    (msgv : val) (gv : globals) : mpred :=
  (!! (strm_ranges z /\ msg_ok (z_msg z) msgv /\ readable_share ish) &&
   (dstate_at s p gv * strm_at z (p_s p) (p_strm p) pin pout msgv gv * in_obj ish z pin *
    out_space z pout rest))%logic.

(** The output space beyond the bytes written: [rest] loses its first (new bytes written) elements. *)
Definition rest_after (z z' : strm) (rest : list val) : list val :=
  sublist (Zlength (z_out z') - Zlength (z_out z)) (Zlength rest) rest.

(** The post-state of a call on the whole stream. *)
Definition dfull_post (z0 : strm) (r : dstate * strm) (p : dptrs) (pin pout : val) (ish : share)
    (rest : list val) (gv : globals) : mpred :=
  (EX msgv : val, dfull (fst r) (snd r) p pin pout ish (rest_after z0 (snd r) rest) msgv gv)%logic.

(** head[] may be undefined: [dstate_at] with head's contents any. *)
Definition hash_at_h0 (s : dstate) (p : dptrs) : mpred :=
  (@field_at DCS.CS Ews t_ds (DOT _prev) (p_prev p) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _head) (p_head p) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _ins_h) (vi (d_ins_h s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _hash_size) (vi (d_hash_size s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _hash_bits) (vi (d_hash_bits s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _hash_mask) (vi (d_hash_mask s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _hash_shift) (vi (d_hash_shift s)) (p_s p) *
   @data_at DCS.CS Ews (tarray tushort (Zlength (d_prev s))) (map vi (d_prev s)) (p_prev p) *
   @data_at_ DCS.CS Ews (tarray tushort (Zlength (d_head s))) (p_head p))%logic.

Definition dstate_at_h0 (s : dstate) (p : dptrs) (gv : globals) : mpred :=
  (!! dstate_ranges s &&
   (trees_at (d_trm s) (p_s p) (p_pbuf p) (p_strm p) gv * win_at s p * hash_at_h0 s p * match_at s p *
    cfg_at s p * stat_at s p))%logic.

(** Right after deflateInit2_'s zmemzero (v2): as [dstate_at_h0], but the three tree descriptors' dyn_tree
    and stat_desc pointers any value (they are NULL until _tr_init sets them). *)
Definition trees_at_d0 (cs : tstate * list bool) (sp pbp strmp : val) (gv : globals) : mpred :=
  (EX lp : val, EX ls : val, EX dp : val, EX ds : val, EX bp : val, EX bs : val,
   ltree_at (tr_ltree (fst cs)) sp * dtree_at (tr_dtree (fst cs)) sp * bltree_at (tr_bltree (fst cs)) sp *
   ldesc_at lp (tr_lmax (fst cs)) ls sp * ddesc_at dp (tr_dmax (fst cs)) ds sp *
   bldesc_at bp (tr_blmax (fst cs)) bs sp *
   work_at (tr_wk (fst cs)) sp * out_at (tr_out (fst cs)) (snd cs) sp pbp * sym_at (fst cs) sp pbp *
   lvl_at (fst cs) sp *
   (* v7: deflateInit2_ does not write strm->data_type before deflateReset: any value *)
   (!! (Int.min_signed <= tr_data_type (fst cs) <= Int.max_signed) &&
    (@field_at DCS.CS Ews t_ds (DOT _strm) strmp sp *
     EX dt : val, @field_at DCS.CS Ews t_strm (DOT _data_type) dt strmp)))%logic.

(** v7: right after zmemzero, s->pending_out is NULL: any value at level 0. *)
Definition stat_at_d0 (s : dstate) (p : dptrs) : mpred :=
  (@field_at DCS.CS Ews t_ds (DOT _status) (vi (d_status s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _pending_buf_size) (vl (d_pending_buf_size s)) (p_s p) *
  @field_at_ DCS.CS Ews t_ds (DOT _pending_out) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _wrap) (vi (d_wrap s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _gzhead) (p_gzhead p) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _gzindex) (vl (d_gzindex s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _method) (vi (d_method s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _last_flush) (vi (d_last_flush s)) (p_s p))%logic.

Definition dstate_at_d0 (s : dstate) (p : dptrs) (gv : globals) : mpred :=
  (!! dstate_ranges s &&
   (trees_at_d0 (d_trm s) (p_s p) (p_pbuf p) (p_strm p) gv * win_at s p * hash_at_h0 s p * match_at s p *
    cfg_at s p * stat_at_d0 s p))%logic.

(** The level of initialisation of a live state (v2): 2 = complete ([dstate_at]); 1 = head[] undefined (after
    _tr_init, before lm_init); 0 = also the descriptors not yet set (right after zmemzero). *)
Definition dstate_at' (lvl : Z) (s : dstate) (p : dptrs) (gv : globals) : mpred :=
  if lvl =? 2 then dstate_at s p gv else if lvl =? 1 then dstate_at_h0 s p gv else dstate_at_d0 s p gv.

(** ** The abstract stream of the API *)

(** The z_stream fields of the caller (set and read between calls). *)
Definition api_fields (strmp nextin : val) (ain tin : Z) (nextout : val) (aout tout : Z) (msgv : val)
    (adler : Z) : mpred :=
  (!! (u32_ok ain /\ u64_ok tin /\ u32_ok aout /\ u64_ok tout /\ u64_ok adler) &&
   (@field_at DCS.CS Ews t_strm (DOT _next_in) nextin strmp *
    @field_at DCS.CS Ews t_strm (DOT _avail_in) (vi ain) strmp *
    @field_at DCS.CS Ews t_strm (DOT _total_in) (vl tin) strmp *
    @field_at DCS.CS Ews t_strm (DOT _next_out) nextout strmp *
    @field_at DCS.CS Ews t_strm (DOT _avail_out) (vi aout) strmp *
    @field_at DCS.CS Ews t_strm (DOT _total_out) (vl tout) strmp *
    @field_at DCS.CS Ews t_strm (DOT _msg) msgv strmp *
    @field_at DCS.CS Ews t_strm (DOT _adler) (vl adler) strmp))%logic.

(** The allocator functions as function pointers (deflateStateCheck compares strm->zalloc / zfree with 0;
    ZALLOC / ZFREE call through them). *)
Definition zfuncs (gv : globals) : mpred :=
  (func_ptr' (snd zcalloc_spec) (gv _zcalloc) * func_ptr' (snd zcfree_spec) (gv _zcfree))%logic.

(** The rest of the z_stream and the state: [os = Some s] a live stream (state, allocator fields, reserved,
    the deflate_state at initialisation level [lvl] with its five allocations, data_type inside it);
    [os = None]: strm->state is Z_NULL, zalloc / zfree Z_NULL or the default allocator's (v2). *)
(** The buffers have the sizes their fields say (v4: the tokens of dtokens and the data are at the same types,
    deflateEnd frees them with one type each). *)
Definition dsizes (s : dstate) : Prop :=
  Zlength (mb_val (d_window s)) = 2 * d_w_size s /\ Zlength (d_prev s) = d_w_size s /\
  Zlength (d_head s) = d_hash_size s /\ Zlength (o_buf (tr_out (d_tr s))) = 4 * tr_lit_bufsize (d_tr s).

Definition dstream (lvl : Z) (os : option dstate) (strmp ghp : val) (gv : globals) : mpred :=
  (zfuncs gv * @field_at_ DCS.CS Ews t_strm (DOT _reserved) strmp *
   match os with
   | Some s =>
       EX p : dptrs, !! (p_strm p = strmp /\ p_gzhead p = ghp /\ dsizes s) &&
       (dstate_at' lvl s p gv * dtokens s p *
        @field_at DCS.CS Ews t_strm (DOT _state) (p_s p) strmp *
        @field_at DCS.CS Ews t_strm (DOT _zalloc) (gv _zcalloc) strmp *
        @field_at DCS.CS Ews t_strm (DOT _zfree) (gv _zcfree) strmp *
        @field_at DCS.CS Ews t_strm (DOT _opaque) nullval strmp)
   | None =>
       EX za : val, EX zf : val, EX op : val, EX dt : val,
       !! (ghp = nullval /\ (za = nullval \/ za = gv _zcalloc) /\ (zf = nullval \/ zf = gv _zcfree)) &&
       (@field_at DCS.CS Ews t_strm (DOT _state) nullval strmp *
        @field_at DCS.CS Ews t_strm (DOT _zalloc) za strmp *
        @field_at DCS.CS Ews t_strm (DOT _zfree) zf strmp *
        @field_at DCS.CS Ews t_strm (DOT _opaque) op strmp *
        @field_at DCS.CS Ews t_strm (DOT _data_type) dt strmp)
   end)%logic.

(** [dstream] with the state pointer exposed (v4): deflate and deflateParams keep the same deflate_state (and
    deflateParams dereferences its local [s] after calling deflate). [dstream_sp_eq]: dstream = EX sp, dstream_sp. *)
Definition dstream_sp (lvl : Z) (os : option dstate) (strmp ghp sp : val) (gv : globals) : mpred :=
  (zfuncs gv * @field_at_ DCS.CS Ews t_strm (DOT _reserved) strmp *
   match os with
   | Some s =>
       EX p : dptrs, !! (p_strm p = strmp /\ p_gzhead p = ghp /\ dsizes s /\ p_s p = sp) &&
       (dstate_at' lvl s p gv * dtokens s p *
        @field_at DCS.CS Ews t_strm (DOT _state) (p_s p) strmp *
        @field_at DCS.CS Ews t_strm (DOT _zalloc) (gv _zcalloc) strmp *
        @field_at DCS.CS Ews t_strm (DOT _zfree) (gv _zcfree) strmp *
        @field_at DCS.CS Ews t_strm (DOT _opaque) nullval strmp)
   | None =>
       EX za : val, EX zf : val, EX op : val, EX dt : val,
       !! (sp = nullval /\ ghp = nullval /\ (za = nullval \/ za = gv _zcalloc) /\ (zf = nullval \/ zf = gv _zcfree)) &&
       (@field_at DCS.CS Ews t_strm (DOT _state) nullval strmp *
        @field_at DCS.CS Ews t_strm (DOT _zalloc) za strmp *
        @field_at DCS.CS Ews t_strm (DOT _zfree) zf strmp *
        @field_at DCS.CS Ews t_strm (DOT _opaque) op strmp *
        @field_at DCS.CS Ews t_strm (DOT _data_type) dt strmp)
   end)%logic.

Lemma dstream_sp_eq lvl os strmp ghp gv :
  dstream lvl os strmp ghp gv = (EX sp : val, dstream_sp lvl os strmp ghp sp gv)%logic.
Proof.
  unfold dstream, dstream_sp. destruct os as [s|].
  - apply pred_ext.
    + Intros p. Exists (p_s p) p. entailer!.
    + Intros sp p. Exists p. entailer!.
  - apply pred_ext.
    + Intros za zf op dt. Exists nullval za zf op dt. entailer!.
    + Intros sp za zf op dt. Exists za zf op dt. entailer!.
Qed.

(** The user's gzip header when the state has one (its memory belongs to the caller); without one, the state's
    gzhead pointer is Z_NULL (v2). *)
Definition hdr_at (os : option dstate) (ghp : val) (hx : share * val * val * val) : mpred :=
  match os with
  | Some s => match d_gzhead s with
              | Some h => let '(hsh, xp, np, cp) := hx in gzh_at hsh h ghp xp np cp
              | None => !! (ghp = nullval) && emp
              end
  | None => emp
  end%logic.

(** What deflateEnd needs (v2): the fields it reads, every other field of deflate_state with any contents, and
    each of the four buffers either Z_NULL or an allocation (token and contents any): the state of a live stream
    ([dstream_to_end]) and the state of deflateInit2_'s failure path both give it. *)
Definition opt_alloc (t : type) (q : val) : mpred :=
  (if eq_dec q nullval then emp else @malloc_token DCS.CS Ews t q * @data_at_ DCS.CS Ews t q)%logic.

Definition dend_at (s : dstate) (p : dptrs) : mpred :=
  (@field_at DCS.CS Ews t_ds (DOT _strm) (p_strm p) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _status) (vi (d_status s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _pending_buf) (p_pbuf p) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _head) (p_head p) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _prev) (p_prev p) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _window) (p_window p) (p_s p) *
   @malloc_token DCS.CS Ews t_ds (p_s p) *
   opt_alloc (tarray tuchar (4 * tr_lit_bufsize (d_tr s))) (p_pbuf p) *
   opt_alloc (tarray tushort (d_hash_size s)) (p_head p) *
   opt_alloc (tarray tushort (d_w_size s)) (p_prev p) *
   opt_alloc (tarray tuchar (2 * d_w_size s)) (p_window p) *
   @field_at_ DCS.CS Ews t_ds (DOT _pending_buf_size) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _pending_out) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _pending) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _wrap) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _gzhead) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _gzindex) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _method) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _last_flush) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _w_size) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _w_bits) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _w_mask) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _window_size) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _ins_h) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _hash_size) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _hash_bits) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _hash_mask) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _hash_shift) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _block_start) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _match_length) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _prev_match) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _match_available) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _strstart) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _match_start) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _lookahead) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _prev_length) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _max_chain_length) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _max_lazy_match) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _level) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _strategy) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _good_match) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _nice_match) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _dyn_ltree) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _dyn_dtree) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _bl_tree) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _l_desc) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _d_desc) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _bl_desc) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _bl_count) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _heap) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _heap_len) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _heap_max) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _depth) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _sym_buf) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _lit_bufsize) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _sym_next) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _sym_end) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _opt_len) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _static_len) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _matches) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _insert) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _bi_buf) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _bi_valid) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _bi_used) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _high_water) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _slid) (p_s p))%logic.

Definition dstream_end (os : option dstate) (strmp : val) (gv : globals) : mpred :=
  (zfuncs gv * @field_at_ DCS.CS Ews t_strm (DOT _reserved) strmp *
   match os with
   | Some s =>
       EX p : dptrs, !! (p_strm p = strmp /\ Int.min_signed <= d_status s <= Int.max_signed) &&
       (dend_at s p * ds_pad (p_s p) *
        @field_at DCS.CS Ews t_strm (DOT _state) (p_s p) strmp *
        @field_at DCS.CS Ews t_strm (DOT _zalloc) (gv _zcalloc) strmp *
        @field_at DCS.CS Ews t_strm (DOT _zfree) (gv _zcfree) strmp *
        @field_at DCS.CS Ews t_strm (DOT _opaque) nullval strmp *
        EX dt : val, @field_at DCS.CS Ews t_strm (DOT _data_type) dt strmp)
   | None =>
       EX za : val, EX zf : val, EX op : val, EX dt : val,
       !! ((za = nullval \/ za = gv _zcalloc) /\ (zf = nullval \/ zf = gv _zcfree)) &&
       (@field_at DCS.CS Ews t_strm (DOT _state) nullval strmp *
        @field_at DCS.CS Ews t_strm (DOT _zalloc) za strmp *
        @field_at DCS.CS Ews t_strm (DOT _zfree) zf strmp *
        @field_at DCS.CS Ews t_strm (DOT _opaque) op strmp *
        @field_at DCS.CS Ews t_strm (DOT _data_type) dt strmp)
   end)%logic.

(** The model's stream of an API call: the input object [inb] with next_in at [nin], nothing written yet. *)
Definition zmk (inb : list Z) (nin ain tin aout tout adler : Z) (msg : option Z) : strm :=
  mkST inb nin ain tin [] aout tout adler msg.

(** The model on an option state (deflateStateCheck first). *)
Definition on_state (f : dstate -> strm -> option (dstate * strm * Z)) (os : option dstate) (z : strm)
    : option (option dstate * strm * Z) := c_on_state f os z.

Definition bstate_num (b : bstate) : Z :=
  match b with need_more => 0 | block_done => 1 | finish_started => 2 | finish_done => 3 end.

(** ** Leaves *)

Definition read_buf_spec :=
 DECLARE _read_buf
 WITH strmp : val, sp : val, pin : val, msgv : val, ish : share, z : strm, s : dstate,
      size : Z, bufp : val, r : strm * list Z, gv : globals
 PRE [ tptr t_strm, tptr tuchar, tuint ]
  PROP (0 <= size <= Int.max_unsigned; strm_ranges z; readable_share ish; s32_ok (d_wrap s);
        c_read_buf s z size = Some r)
  PARAMS (strmp; bufp; vi size) GLOBALS (gv)
  SEP (strm_in_at z sp strmp pin msgv gv; in_obj ish z pin;
       @field_at DCS.CS Ews t_ds (DOT _wrap) (vi (d_wrap s)) sp;
       @data_at_ DCS.CS Ews (tarray tuchar (Zlength (snd r))) bufp; crc_table_at Ers gv)
 POST [ tuint ]
  PROP () RETURN (vi (Zlength (snd r)))
  SEP (strm_in_at (fst r) sp strmp pin msgv gv; in_obj ish (fst r) pin;
       @field_at DCS.CS Ews t_ds (DOT _wrap) (vi (d_wrap s)) sp;
       @data_at DCS.CS Ews (tarray tuchar (Zlength (snd r))) (map vi (snd r)) bufp; crc_table_at Ers gv).

Definition c_putShortMSB_o (om : cout) (b : Z) : option cout :=
  let* om := c_put_byte om (Z.shiftr b 8) in c_put_byte om (Z.land b 255).

Definition putShortMSB_spec :=
 DECLARE _putShortMSB
 WITH sp : val, pbp : val, o : outbuf, m : list bool, b : Z, r : cout
 PRE [ tptr t_ds, tuint ]
  PROP (0 <= b <= Int.max_unsigned; c_putShortMSB_o (o, m) b = Some r)
  PARAMS (sp; vi b)
  SEP (out_at o m sp pbp)
 POST [ tvoid ]
  PROP () RETURN ()
  SEP (out_at (fst r) (snd r) sp pbp).

(** flush_pending(strm): the stream fields, the output space, and the state's pending_out and bit output. *)
Definition flush_pending_spec :=
 DECLARE _flush_pending
 WITH strmp : val, sp : val, pbp : val, pin : val, pout : val, msgv : val, rest : list val,
      s : dstate, z : strm, r : dstate * strm, gv : globals
 PRE [ tptr t_strm ]
  PROP (strm_ranges z; c_flush_pending s z = Some r)
  PARAMS (strmp) GLOBALS (gv)
  SEP (strm_at z sp strmp pin pout msgv gv; out_space z pout rest;
       @field_at DCS.CS Ews t_ds (DOT _pending_out) (offset_val (d_po s) pbp) sp;
       out_at (tr_out (d_tr s)) (d_pbm s) sp pbp)
 POST [ tvoid ]
  PROP () RETURN ()
  SEP (strm_at (snd r) sp strmp pin pout msgv gv; out_space (snd r) pout (rest_after z (snd r) rest);
       @field_at DCS.CS Ews t_ds (DOT _pending_out) (offset_val (d_po (fst r)) pbp) sp;
       out_at (tr_out (d_tr (fst r))) (d_pbm (fst r)) sp pbp).

(** ** Internal functions on the state only *)

Definition slide_hash_spec :=
 DECLARE _slide_hash
 WITH s : dstate, p : dptrs, r : dstate, gv : globals
 PRE [ tptr t_ds ]
  PROP (c_slide_hash s = Some r)
  PARAMS (p_s p) GLOBALS (gv)
  SEP (dstate_at s p gv)
 POST [ tvoid ]
  PROP () RETURN ()
  SEP (dstate_at r p gv).

Definition longest_match_spec :=
 DECLARE _longest_match
 WITH s : dstate, p : dptrs, cur : Z, r : dstate * Z, gv : globals
 PRE [ tptr t_ds, tuint ]
  PROP (0 <= cur <= Int.max_unsigned; c_longest_match s cur = Some r)
  PARAMS (p_s p; vi cur) GLOBALS (gv)
  SEP (dstate_at s p gv)
 POST [ tuint ]
  PROP () RETURN (vi (snd r))
  SEP (dstate_at (fst r) p gv).

Definition lm_init_spec :=
 DECLARE _lm_init
 WITH s : dstate, p : dptrs, r : dstate, gv : globals
 PRE [ tptr t_ds ]
  PROP (c_lm_init s = Some r)
  PARAMS (p_s p) GLOBALS (gv)
  SEP (dstate_at_h0 s p gv; deflate_globals gv)
 POST [ tvoid ]
  PROP () RETURN ()
  SEP (dstate_at r p gv; deflate_globals gv).

(** ** Internal functions on the whole stream *)

(** The whole stream without the output side (v2): fill_window and read_buf never touch the output, and
    deflateSetDictionary calls fill_window with next_out any value (Z_NULL in the harnesses). *)
Definition dfull_in (s : dstate) (z : strm) (p : dptrs) (pin : val) (ish : share) (msgv : val)
    (gv : globals) : mpred :=
  (!! (strm_ranges z /\ msg_ok (z_msg z) msgv /\ readable_share ish) &&
   (dstate_at s p gv * strm_in_at z (p_s p) (p_strm p) pin msgv gv * in_obj ish z pin))%logic.

Definition fill_window_spec :=
 DECLARE _fill_window
 WITH s : dstate, z : strm, p : dptrs, pin : val, ish : share, msgv : val, r : dstate * strm, gv : globals
 PRE [ tptr t_ds ]
  PROP (c_fill_window s z = Some r)
  PARAMS (p_s p) GLOBALS (gv)
  SEP (dfull_in s z p pin ish msgv gv; deflate_globals gv)
 POST [ tvoid ]
  PROP () RETURN ()
  SEP (EX msgv' : val, dfull_in (fst r) (snd r) p pin ish msgv' gv; deflate_globals gv).

(** The five compression functions: [deflate_X(s, flush)] returns the block_state ([bstate_num]). *)
Definition compress_spec (f : ident) (cf : dstate -> strm -> Z -> option (dstate * strm * bstate)) :=
 DECLARE f
 WITH s : dstate, z : strm, p : dptrs, pin : val, pout : val, ish : share, rest : list val, msgv : val,
      flush : Z, r : dstate * strm * bstate, gv : globals
 PRE [ tptr t_ds, tint ]
  PROP (Int.min_signed <= flush <= Int.max_signed; cf s z flush = Some r)
  PARAMS (p_s p; vi flush) GLOBALS (gv)
  SEP (dfull s z p pin pout ish rest msgv gv; deflate_globals gv)
 POST [ tint ]
  PROP () RETURN (vi (bstate_num (snd r)))
  SEP (dfull_post z (fst r) p pin pout ish rest gv; deflate_globals gv).

Definition deflate_stored_spec := compress_spec _deflate_stored c_deflate_stored.
Definition deflate_fast_spec := compress_spec _deflate_fast c_deflate_fast.
Definition deflate_slow_spec := compress_spec _deflate_slow c_deflate_slow.
Definition deflate_rle_spec := compress_spec _deflate_rle c_deflate_rle.
Definition deflate_huff_spec := compress_spec _deflate_huff c_deflate_huff.

(** ** deflateStateCheck (v2: on exactly what it reads, so that every API function can give it from its own
    precondition: dstream, dstream_end; v4: also strm->next_in, the field at offset 0 of the z_stream, which makes
    strm weakly valid for `strm == Z_NULL`) *)
Definition dcheck_at (os : option dstate) (strmp sp za zf : val) (gv : globals) : mpred :=
  (zfuncs gv *
   @field_at DCS.CS Ews t_strm (DOT _state) sp strmp *
   @field_at DCS.CS Ews t_strm (DOT _zalloc) za strmp *
   @field_at DCS.CS Ews t_strm (DOT _zfree) zf strmp *
   match os with
   | Some s => !! (za = gv _zcalloc /\ zf = gv _zcfree /\ Int.min_signed <= d_status s <= Int.max_signed) &&
               (@field_at DCS.CS Ews t_ds (DOT _strm) strmp sp *
                @field_at DCS.CS Ews t_ds (DOT _status) (vi (d_status s)) sp)
   | None => !! (sp = nullval /\ (za = nullval \/ za = gv _zcalloc) /\ (zf = nullval \/ zf = gv _zcfree)) && emp
   end)%logic.

Definition deflateStateCheck_spec :=
 DECLARE _deflateStateCheck
 WITH os : option dstate, strmp : val, sp : val, za : val, zf : val, ni : val, gv : globals
 PRE [ tptr t_strm ]
  PROP ()
  PARAMS (strmp) GLOBALS (gv)
  SEP (dcheck_at os strmp sp za zf gv; @field_at DCS.CS Ews t_strm (DOT _next_in) ni strmp)
 POST [ tint ]
  PROP () RETURN (vi (c_deflateStateCheck os))
  SEP (dcheck_at os strmp sp za zf gv; @field_at DCS.CS Ews t_strm (DOT _next_in) ni strmp).

(** ** The API
    v5: the functions that call deflateStateCheck and do not take [api_fields] (Tune, SetHeader, Prime, End,
    Bound_z, Bound) also take strm->next_in ([ni], returned unchanged): deflateStateCheck needs it. *)

(** A function on a live or ended stream that does not use the input / output objects: the caller's fields
    are given; the model's stream has no input object ([zmk []]). *)
Definition api_simple_spec (f : ident) (cf : dstate -> strm -> option (dstate * strm * Z))
    (post_lvl : Z -> Z -> Z) :=
 DECLARE f
 WITH lvl : Z, os : option dstate, strmp : val, ghp : val, nextin : val, ain : Z, tin : Z, nextout : val, aout : Z,
      tout : Z, msgv : val, msg : option Z, adler : Z, r : option dstate * strm * Z, gv : globals
 PRE [ tptr t_strm ]
  PROP (msg_ok msg msgv; on_state cf os (zmk [] 0 ain tin aout tout adler msg) = Some r)
  PARAMS (strmp) GLOBALS (gv)
  SEP (dstream lvl os strmp ghp gv; api_fields strmp nextin ain tin nextout aout tout msgv adler;
       deflate_globals gv)
 POST [ tint ]
  PROP () RETURN (vi (snd r))
  SEP (dstream (post_lvl lvl (snd r)) (fst (fst r)) strmp ghp gv;
       EX msgv' : val, !! msg_ok (z_msg (snd (fst r))) msgv' &&
       api_fields strmp nextin (z_avail_in (snd (fst r))) (z_total_in (snd (fst r))) nextout
         (z_avail_out (snd (fst r))) (z_total_out (snd (fst r))) msgv' (z_adler (snd (fst r)));
       deflate_globals gv).

(** deflateReset and deflateResetKeep accept any initialisation level (deflateInit2_ calls deflateReset right
    after zmemzero); on Z_OK, ResetKeep has set the descriptors (level >= 1) and Reset also head[] (level 2). *)
Definition deflateReset_spec := api_simple_spec _deflateReset c_deflateReset
  (fun lvl code => if code =? Z_OK then 2 else lvl).
Definition deflateResetKeep_spec := api_simple_spec _deflateResetKeep c_deflateResetKeep
  (fun lvl code => if code =? Z_OK then Z.max lvl 1 else lvl).

Definition deflateTune_spec :=
 DECLARE _deflateTune
 WITH os : option dstate, strmp : val, ni : val, ghp : val, good : Z, lazy : Z, nice : Z, chain : Z,
      r : option dstate * strm * Z, z : strm, gv : globals
 PRE [ tptr t_strm, tint, tint, tint, tint ]
  PROP (s32_ok good; s32_ok lazy; s32_ok nice; s32_ok chain;
        on_state (fun s z => c_deflateTune s z good lazy nice chain) os z = Some r)
  PARAMS (strmp; vi good; vi lazy; vi nice; vi chain) GLOBALS (gv)
  SEP (@field_at DCS.CS Ews t_strm (DOT _next_in) ni strmp; dstream 2 os strmp ghp gv)
 POST [ tint ]
  PROP () RETURN (vi (snd r))
  SEP (@field_at DCS.CS Ews t_strm (DOT _next_in) ni strmp; dstream 2 (fst (fst r)) strmp ghp gv).

Definition deflateSetHeader_spec :=
 DECLARE _deflateSetHeader
 WITH os : option dstate, strmp : val, ni : val, ghp : val, hp : val, h : gzh, xp : val, np : val, cp : val,
      r : option dstate * strm * Z, z : strm, gv : globals
 PRE [ tptr t_strm, tptr t_gzh ]
  PROP (on_state (fun s z => c_deflateSetHeader s z (Some h)) os z = Some r)
  PARAMS (strmp; hp) GLOBALS (gv)
  SEP (@field_at DCS.CS Ews t_strm (DOT _next_in) ni strmp; dstream 2 os strmp ghp gv; gzh_at Ews h hp xp np cp)
 POST [ tint ]
  PROP () RETURN (vi (snd r))
  SEP (@field_at DCS.CS Ews t_strm (DOT _next_in) ni strmp; dstream 2 (fst (fst r)) strmp (if snd r =? Z_OK then hp else ghp) gv; gzh_at Ews h hp xp np cp).

(** deflateSetDictionary(strm, dictionary, dictLength): the dictionary is an object of [dictLength] bytes. *)
Definition deflateSetDictionary_spec :=
 DECLARE _deflateSetDictionary
 WITH os : option dstate, strmp : val, ghp : val, nextin : val, ain : Z, tin : Z, nextout : val, aout : Z,
      tout : Z, msgv : val, msg : option Z, adler : Z, dp : val, dsh : share, dict : list Z,
      r : option dstate * strm * Z, gv : globals
 PRE [ tptr t_strm, tptr tuchar, tuint ]
  PROP (msg_ok msg msgv; readable_share dsh; Zlength dict <= Int.max_unsigned;
        Forall (fun b => 0 <= b < 256) dict;
        on_state (fun s z => c_deflateSetDictionary s z (Some dict)) os (zmk [] 0 ain tin aout tout adler msg)
          = Some r; is_pointer_or_null nextin)
  PARAMS (strmp; dp; vi (Zlength dict)) GLOBALS (gv)
  SEP (dstream 2 os strmp ghp gv; api_fields strmp nextin ain tin nextout aout tout msgv adler;
       opt_obj dsh (Some dict) dp; deflate_globals gv)
 POST [ tint ]
  PROP () RETURN (vi (snd r))
  SEP (dstream 2 (fst (fst r)) strmp ghp gv;
       EX msgv' : val, !! msg_ok (z_msg (snd (fst r))) msgv' &&
       api_fields strmp nextin (z_avail_in (snd (fst r))) (z_total_in (snd (fst r))) nextout
         (z_avail_out (snd (fst r))) (z_total_out (snd (fst r))) msgv' (z_adler (snd (fst r)));
       opt_obj dsh (Some dict) dp; deflate_globals gv).

(** A witness that a pointer is weakly valid (v2), lent by the caller of deflate / deflateParams when there is
    no output space: the malloc token of a 0-byte object at the pointer, or a byte just before it
    (one-past-the-end pointers). *)
Inductive wvw := WVnone | WVtok (t : type) | WVbefore (sh : share) (v : val).
Definition wv_ok (w : wvw) : Prop :=
  match w with WVnone => False | WVtok t => sizeof t <= 0 | WVbefore sh _ => readable_share sh end.
Definition wv_at (w : wvw) (p : val) : mpred :=
  (match w with
   | WVnone => emp
   | WVtok t => @malloc_token DCS.CS Ews t p
   | WVbefore sh v => @data_at DCS.CS sh tuchar v (offset_val (-1) p)
   end)%logic.

(** deflate(strm, flush): the input object [inb] (next_in = pin + nin, avail_in = ain) and the output space
    (next_out = pout, avail_out bytes [rest]); for a live stream with a gzip header, the header.  [W]: the caller's witness
    ([wv_at], returned unchanged) that [pout] is weakly valid when there is no output space (v2: deflate tests
    next_out == Z_NULL). *)
Definition deflate_spec :=
 DECLARE _deflate
 WITH os : option dstate, strmp : val, ghp : val, sp : val, hx : share * val * val * val,
      pin : val, ish : share, inb : list Z, nin : Z, ain : Z, tin : Z, pout : val, rest : list val, W : wvw, tout : Z,
      msgv : val, msg : option Z, adler : Z, flush : Z, r : option dstate * strm * Z, gv : globals
 PRE [ tptr t_strm, tint ]
  PROP (msg_ok msg msgv; readable_share ish; Zlength rest = 0 -> wv_ok W; s32_ok flush;
        strm_ranges (zmk inb nin ain tin (Zlength rest) tout adler msg);
        (* v6: the functions [ef] are used for the compression functions (DModel5) *)
        exists ef, ef_ok gv ef /\
          on_state (fun s z => c_deflate_g ef s z flush) os (zmk inb nin ain tin (Zlength rest) tout adler msg)
            = Some r)
  PARAMS (strmp; vi flush) GLOBALS (gv)
  SEP (dstream_sp 2 os strmp ghp sp gv;
       api_fields strmp (offset_val nin pin) ain tin pout (Zlength rest) tout msgv adler;
       @data_at DCS.CS ish (tarray tuchar (Zlength inb)) (map vi inb) pin;
       @data_at DCS.CS Ews (tarray tuchar (Zlength rest)) rest pout;
       hdr_at os ghp hx; deflate_globals gv; wv_at W pout)
 POST [ tint ]
  PROP () RETURN (vi (snd r))
  SEP (dstream_sp 2 (fst (fst r)) strmp ghp sp gv;
       EX msgv' : val, !! msg_ok (z_msg (snd (fst r))) msgv' &&
       api_fields strmp (offset_val (z_next_in (snd (fst r))) pin) (z_avail_in (snd (fst r)))
         (z_total_in (snd (fst r))) (offset_val (Zlength (z_out (snd (fst r)))) pout)
         (z_avail_out (snd (fst r))) (z_total_out (snd (fst r))) msgv' (z_adler (snd (fst r)));
       @data_at DCS.CS ish (tarray tuchar (Zlength inb)) (map vi inb) pin;
       @data_at DCS.CS Ews (tarray tuchar (Zlength rest))
         (map vi (z_out (snd (fst r))) ++ sublist (Zlength (z_out (snd (fst r)))) (Zlength rest) rest) pout;
       hdr_at os ghp hx; deflate_globals gv; wv_at W pout).

(** deflateParams(strm, level, strategy): may call deflate(strm, Z_BLOCK), so it gets what deflate gets. *)
Definition deflateParams_spec :=
 DECLARE _deflateParams
 WITH os : option dstate, strmp : val, ghp : val, sp : val, hx : share * val * val * val,
      pin : val, ish : share, inb : list Z, nin : Z, ain : Z, tin : Z, pout : val, rest : list val, W : wvw, tout : Z,
      msgv : val, msg : option Z, adler : Z, level : Z, strategy : Z, r : option dstate * strm * Z,
      gv : globals
 PRE [ tptr t_strm, tint, tint ]
  PROP (msg_ok msg msgv; readable_share ish; Zlength rest = 0 -> wv_ok W; s32_ok level; s32_ok strategy;
        strm_ranges (zmk inb nin ain tin (Zlength rest) tout adler msg);
        (* v8 (code deviation D2): deflateParams compares DEFLATE_KIND(s->level) != DEFLATE_KIND(level), the
           compressor indices (DEFLATE_KIND = cfg_f on 0..9): [fe] is index equality; [ef] for its deflate(Z_BLOCK) *)
        exists ef, ef_ok gv ef /\
          on_state (fun s z => c_deflateParams_g ef Z.eqb s z level strategy) os
            (zmk inb nin ain tin (Zlength rest) tout adler msg) = Some r)
  PARAMS (strmp; vi level; vi strategy) GLOBALS (gv)
  SEP (dstream_sp 2 os strmp ghp sp gv;
       api_fields strmp (offset_val nin pin) ain tin pout (Zlength rest) tout msgv adler;
       @data_at DCS.CS ish (tarray tuchar (Zlength inb)) (map vi inb) pin;
       @data_at DCS.CS Ews (tarray tuchar (Zlength rest)) rest pout;
       hdr_at os ghp hx; deflate_globals gv; wv_at W pout)
 POST [ tint ]
  PROP () RETURN (vi (snd r))
  SEP (dstream_sp 2 (fst (fst r)) strmp ghp sp gv;
       EX msgv' : val, !! msg_ok (z_msg (snd (fst r))) msgv' &&
       api_fields strmp (offset_val (z_next_in (snd (fst r))) pin) (z_avail_in (snd (fst r)))
         (z_total_in (snd (fst r))) (offset_val (Zlength (z_out (snd (fst r)))) pout)
         (z_avail_out (snd (fst r))) (z_total_out (snd (fst r))) msgv' (z_adler (snd (fst r)));
       @data_at DCS.CS ish (tarray tuchar (Zlength inb)) (map vi inb) pin;
       @data_at DCS.CS Ews (tarray tuchar (Zlength rest))
         (map vi (z_out (snd (fst r))) ++ sublist (Zlength (z_out (snd (fst r)))) (Zlength rest) rest) pout;
       hdr_at os ghp hx; deflate_globals gv; wv_at W pout).

Definition deflatePrime_spec :=
 DECLARE _deflatePrime
 WITH os : option dstate, strmp : val, ni : val, ghp : val, bits : Z, value : Z, z : strm,
      r : option dstate * strm * Z, gv : globals
 PRE [ tptr t_strm, tint, tint ]
  PROP (s32_ok bits; s32_ok value; on_state (fun s z => c_deflatePrime s z bits value) os z = Some r)
  PARAMS (strmp; vi bits; vi value) GLOBALS (gv)
  SEP (@field_at DCS.CS Ews t_strm (DOT _next_in) ni strmp; dstream 2 os strmp ghp gv)
 POST [ tint ]
  PROP () RETURN (vi (snd r))
  SEP (@field_at DCS.CS Ews t_strm (DOT _next_in) ni strmp; dstream 2 (fst (fst r)) strmp ghp gv).

(** deflateEnd(strm): frees the five allocations (mem_mgr). *)
Definition deflateEnd_spec :=
 DECLARE _deflateEnd
 WITH os : option dstate, strmp : val, ni : val, z : strm, r : option dstate * strm * Z, gv : globals
 PRE [ tptr t_strm ]
  PROP (match os with Some s => c_deflateEnd s z = Some r | None => r = (None, z, Z_STREAM_ERROR) end)
  PARAMS (strmp) GLOBALS (gv)
  SEP (@field_at DCS.CS Ews t_strm (DOT _next_in) ni strmp; dstream_end os strmp gv; mem_mgr gv)
 POST [ tint ]
  PROP () RETURN (vi (snd r))
  SEP (@field_at DCS.CS Ews t_strm (DOT _next_in) ni strmp; match fst (fst r) with
       | None => dstream 2 None strmp nullval gv
       | Some _ => dstream_end os strmp gv
       end;
       mem_mgr gv).

Definition deflateBound_z_spec :=
 DECLARE _deflateBound_z
 WITH os : option dstate, strmp : val, ni : val, ghp : val, hx : share * val * val * val, n : Z,
      r : Z, gv : globals
 PRE [ tptr t_strm, tulong ]
  PROP (u64_ok n; c_deflateBound_z os n = Some r)
  PARAMS (strmp; vl n) GLOBALS (gv)
  SEP (@field_at DCS.CS Ews t_strm (DOT _next_in) ni strmp; dstream 2 os strmp ghp gv; hdr_at os ghp hx)
 POST [ tulong ]
  PROP () RETURN (vl r)
  SEP (@field_at DCS.CS Ews t_strm (DOT _next_in) ni strmp; dstream 2 os strmp ghp gv; hdr_at os ghp hx).

Definition deflateBound_spec :=
 DECLARE _deflateBound
 WITH os : option dstate, strmp : val, ni : val, ghp : val, hx : share * val * val * val, n : Z,
      r : Z, gv : globals
 PRE [ tptr t_strm, tulong ]
  PROP (u64_ok n; c_deflateBound os n = Some r)
  PARAMS (strmp; vl n) GLOBALS (gv)
  SEP (@field_at DCS.CS Ews t_strm (DOT _next_in) ni strmp; dstream 2 os strmp ghp gv; hdr_at os ghp hx)
 POST [ tulong ]
  PROP () RETURN (vl r)
  SEP (@field_at DCS.CS Ews t_strm (DOT _next_in) ni strmp; dstream 2 os strmp ghp gv; hdr_at os ghp hx).

(** deflateInit2_(strm, level, method, windowBits, memLevel, strategy, version, stream_size), for a stream
    with zalloc = zfree = Z_NULL (the caller's default allocator) and a version string [vers] at [vp]; strm->msg
    may be anything before the call (v2: it is written before it is read; untouched on Z_VERSION_ERROR).
    The outcomes of the five allocations are chosen by the allocator: the precondition asks that the model
    succeed for all of them, the postcondition says which happened. *)
(** The caller's z_stream fields as one record (to keep the WITH list short). *)
Record apif := mkAF { af_nin : val; af_ain : Z; af_tin : Z; af_nout : val; af_aout : Z; af_tout : Z;
                      af_msgv : val; af_adler : Z }.
Definition api_fields_r (strmp : val) (a : apif) : mpred :=
  api_fields strmp (af_nin a) (af_ain a) (af_tin a) (af_nout a) (af_aout a) (af_tout a) (af_msgv a) (af_adler a).

Definition deflateInit2__spec :=
 DECLARE _deflateInit2_
 WITH strmp : val, level : Z, method : Z, wbits : Z, mem : Z, strategy : Z, vp : val, vsh : share,
      vers : list Z, ssize : Z, a : apif, op : val, dt : val, st0 : val, gv : globals
 PRE [ tptr t_strm, tint, tint, tint, tint, tint, tptr tschar, tint ]
  PROP (s32_ok level; s32_ok method; s32_ok wbits; s32_ok mem; s32_ok strategy; s32_ok ssize;
        readable_share vsh; 1 <= Zlength vers; -128 <= Znth 0 vers < 128;
        forall a1 a2 a3 a4 a5, exists r,
          c_deflateInit2_ (Znth 0 vers =? 49) (ssize =? 112) false level method wbits mem strategy a1 a2 a3 a4 a5
            (zmk [] 0 (af_ain a) (af_tin a) (af_aout a) (af_tout a) (af_adler a) None) = Some r)
  PARAMS (strmp; vi level; vi method; vi wbits; vi mem; vi strategy; vp; vi ssize) GLOBALS (gv)
  SEP (api_fields_r strmp a;
       @field_at DCS.CS Ews t_strm (DOT _zalloc) nullval strmp;
       @field_at DCS.CS Ews t_strm (DOT _zfree) nullval strmp;
       @field_at DCS.CS Ews t_strm (DOT _opaque) op strmp;
       @field_at DCS.CS Ews t_strm (DOT _data_type) dt strmp;
       @field_at DCS.CS Ews t_strm (DOT _state) st0 strmp;
       @field_at_ DCS.CS Ews t_strm (DOT _reserved) strmp;
       @data_at DCS.CS vsh (tarray tschar (Zlength vers)) (map vi vers) vp;
       mem_mgr gv; deflate_globals gv)
 POST [ tint ]
  EX a1 : bool, EX a2 : bool, EX a3 : bool, EX a4 : bool, EX a5 : bool, EX r : option dstate * strm * Z,
  PROP (c_deflateInit2_ (Znth 0 vers =? 49) (ssize =? 112) false level method wbits mem strategy a1 a2 a3 a4 a5
          (zmk [] 0 (af_ain a) (af_tin a) (af_aout a) (af_tout a) (af_adler a) None) = Some r)
  RETURN (vi (snd r))
  SEP (match fst (fst r) with
       | Some _ => dstream 2 (fst (fst r)) strmp nullval gv
       | None => EX st : val, EX za : val, EX zf : val, EX op' : val, EX dt' : val,
                 !! (snd r = Z_VERSION_ERROR -> st = st0) &&
                 (zfuncs gv * @field_at_ DCS.CS Ews t_strm (DOT _reserved) strmp *
                  @field_at DCS.CS Ews t_strm (DOT _state) st strmp *
                  @field_at DCS.CS Ews t_strm (DOT _zalloc) za strmp *
                  @field_at DCS.CS Ews t_strm (DOT _zfree) zf strmp *
                  @field_at DCS.CS Ews t_strm (DOT _opaque) op' strmp *
                  @field_at DCS.CS Ews t_strm (DOT _data_type) dt' strmp)
       end;
       EX msgv' : val,
       !! (if snd r =? Z_VERSION_ERROR then msgv' = af_msgv a else msg_ok (z_msg (snd (fst r))) msgv') &&
       api_fields strmp (af_nin a) (z_avail_in (snd (fst r))) (z_total_in (snd (fst r))) (af_nout a)
         (z_avail_out (snd (fst r))) (z_total_out (snd (fst r))) msgv' (z_adler (snd (fst r)));
       @data_at DCS.CS vsh (tarray tschar (Zlength vers)) (map vi vers) vp;
       mem_mgr gv; deflate_globals gv).

(** ** The contexts of the body proofs (callees). *)
Definition Gprog_read_buf : funspecs := [memcpy_spec; adler32_spec; crc32_spec].
Definition Gprog_putShortMSB : funspecs := [].
Definition Gprog_flush_pending : funspecs := [tr_flush_bits_spec; memcpy_spec].
Definition Gprog_slide_hash : funspecs := [].
Definition Gprog_longest_match : funspecs := [].
Definition Gprog_lm_init : funspecs := [memset_spec].
Definition Gprog_fill_window : funspecs := [memcpy_spec; memset_spec; slide_hash_spec; read_buf_spec].
Definition Gprog_compress : funspecs :=
  [fill_window_spec; longest_match_spec; flush_pending_spec; tr_flush_block_spec; tr_stored_block_spec;
   read_buf_spec; memcpy_spec].
Definition Gprog_deflateStateCheck : funspecs := [].
Definition Gprog_deflateResetKeep : funspecs := [deflateStateCheck_spec; tr_init_spec; adler32_spec; crc32_spec].
Definition Gprog_deflateReset : funspecs := [deflateResetKeep_spec; lm_init_spec].
Definition Gprog_deflateSetHeader : funspecs := [deflateStateCheck_spec].
Definition Gprog_deflateTune : funspecs := [deflateStateCheck_spec].
Definition Gprog_deflatePrime : funspecs := [deflateStateCheck_spec; tr_flush_bits_spec].
Definition Gprog_deflateBound_z : funspecs := [deflateStateCheck_spec].
Definition Gprog_deflateBound : funspecs := [deflateBound_z_spec].
Definition Gprog_deflateSetDictionary : funspecs :=
  [deflateStateCheck_spec; adler32_spec; memset_spec; fill_window_spec].
Definition Gprog_deflateEnd : funspecs := [deflateStateCheck_spec; zcfree_spec].
Definition Gprog_deflateInit2_ : funspecs :=
  [zcalloc_spec; zcfree_spec; memset_spec; deflateEnd_spec; deflateReset_spec].
Definition Gprog_deflate : funspecs :=
  [deflateStateCheck_spec; flush_pending_spec; putShortMSB_spec; adler32_spec; crc32_spec; crc32_z_spec;
   memcpy_spec; memset_spec; deflate_stored_spec; deflate_fast_spec; deflate_slow_spec; deflate_rle_spec;
   deflate_huff_spec; tr_align_spec; tr_stored_block_spec].
Definition Gprog_deflateParams : funspecs :=
  [deflateStateCheck_spec; deflate_spec; slide_hash_spec; memset_spec; deflate_stored_spec; deflate_fast_spec;
   deflate_slow_spec].

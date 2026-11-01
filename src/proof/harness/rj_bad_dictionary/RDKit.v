(* The main of harness/rj_bad_dictionary.c, proved against MainLib.main_core_spec R (RDGlobals.v) from the
   theory of its inflate() call (RDFacts.rbd_theory_stmt), calling laws_common.h's helpers through their
   shared specifications (laws_common/Spec.v), adler32_z through adler32/Spec.v and inflate.c's API through
   Spec5.v, except inflate() and inflateSetDictionary: the harness offers up to UINT_MAX bytes of input (the first
   clip(stream_len) bytes of a stream of any length) and of output space, and a dictionary of up to UINT_MAX
   bytes, so these calls go through the wide specifications of SpecW.v (on this zlib stream, istreamA is Spec5's
   istream). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.SpecW.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.proof.adler32.Spec.
Require Import Zlib.proof.harness.rj_bad_dictionary.RDLawCS.
Require Import Zlib.proof.harness.rj_bad_dictionary.RDGlobals.
Require Import Zlib.proof.harness.rj_bad_dictionary.RDFacts.
Require Import Zlib.harness.rj_bad_dictionary.code.
Require Zlib.proof.harness.inflate_common.HarnessLib.

Definition Gmain : funspecs :=
  [inflateInit2__spec; inflate_specW; inflateSetDictionary_specW; zcalloc_i; zcfree_i;
   Zlib.proof.adler32.Spec.adler32_z_spec;
   upto_spec; clip_spec; any_bytes_spec; offer_spec; new_stream_spec;
   (_quickproof_malloc, malloc_spec');
   nondet_u32_spec; gp_assert_spec; gp_assume_spec].

(* ---------------------------------------------------------------------------------------------- *)
(* Compspecs moves: the callees' specifications are at their units' compspecs, main at the law's   *)

Lemma rbd_bytes_adler_cs sh n (v: list val) q:
  @data_at Zlib.units.Adler32.CS sh (tarray tuchar n) v q = @data_at CS sh (tarray tuchar n) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_adler32); [apply JMeq_refl | reflexivity]. Qed.
Lemma rbd_tok_adler_cs sh n q:
  @malloc_token Zlib.units.Adler32.CS sh (tarray tuchar n) q = @malloc_token CS sh (tarray tuchar n) q.
Proof. apply equal_f; apply (@malloc_token_change_composite _ _ CC_adler32). reflexivity. Qed.
Lemma rbd_bytes_inflate_cs sh n (v: list val) q:
  @data_at Zlib.units.Inflate.CS sh (tarray tuchar n) v q = @data_at CS sh (tarray tuchar n) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_inflate); [apply JMeq_refl | reflexivity]. Qed.
Lemma rbd_tok_inflate_cs sh n q:
  @malloc_token Zlib.units.Inflate.CS sh (tarray tuchar n) q = @malloc_token CS sh (tarray tuchar n) q.
Proof. apply equal_f; apply (@malloc_token_change_composite _ _ CC_inflate). reflexivity. Qed.

Lemma rbd_schar_inflate_cs sh n (v: list val) q:
  @data_at Zlib.units.Inflate.CS sh (tarray tschar n) v q = @data_at CS sh (tarray tschar n) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_inflate); [apply JMeq_refl | reflexivity]. Qed.

(* struct z_stream: laws_common's t_zs (compress unit) and Spec5's t_strm (inflate unit) are main's struct *)
Definition rbd_strm_tuple : Type :=
  (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * val)))))))))))))%type.

Lemma rbd_zs_cs sh (v: rbd_strm_tuple) q:
  @data_at Zlib.units.Compress.CS sh t_zs v q = @data_at CS sh (Tstruct _z_stream_s noattr) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_compress); [apply JMeq_refl | reflexivity]. Qed.
Lemma rbd_strm_cs sh (v: rbd_strm_tuple) q:
  @data_at Zlib.units.Inflate.CS sh Rep.t_strm v q = @data_at CS sh (Tstruct _z_stream_s noattr) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_inflate); [apply JMeq_refl | reflexivity]. Qed.

(* the local z_stream after inflateInit2_ and offer (laws_common's view) as Spec5's live stream *)
Lemma rbd_istream_fold gv v L ni ai no ao:
  live_ok L -> 0 <= ai <= Int.max_unsigned -> 0 <= ao <= Int.max_unsigned ->
  @data_at Zlib.units.Compress.CS Tsh t_zs
    (zs_val ni (Vint (Int.repr ai)) (Vlong (Int64.repr 0)) no (Vint (Int.repr ao)) (Vlong (Int64.repr 0)) nullval
       (l_sp L) (gv Zlib.inflate.code._zcalloc) (gv Zlib.inflate.code._zcfree) nullval (Vint (Int.repr 0))
       (Vlong (Int64.repr 1)) Vundef) v * state_mem gv v L
  |-- istream gv Tsh v (ZF ni ai 0 no ao 0 None 0 1 Vundef) (Some L).
Proof.
  intros LV Hai Hao.
  rewrite <- istream_raw_istream by (unfold zf_ok; simpl; rep_lia || reflexivity).
  unfold istream_raw, raw_strm. rewrite rbd_zs_cs, <- rbd_strm_cs. simpl. entailer!.
Qed.

(* a stream (live or not) gives back the local variable's memory *)
Lemma rbd_istream_undef gv v z st:
  istream gv Tsh v z st |-- @data_at_ CS Tsh (Tstruct _z_stream_s noattr) v * TT.
Proof.
  unfold istream, zstrm_at, strm_rep. destruct st as [L | ]; Intros.
  - rewrite rbd_strm_cs. sep_apply (data_at_data_at_ Tsh (Tstruct _z_stream_s noattr)). cancel.
  - rewrite rbd_strm_cs. sep_apply (data_at_data_at_ Tsh (Tstruct _z_stream_s noattr)). cancel.
Qed.

(* the input object (the stream bytes) and the output object (room bytes, never written before) as the buffers of
   inflate()'s call *)
Lemma rbd_bufs_pre L ibp n (ci: list val) obp m:
  0 <= m ->
  data_at Ews (tarray tuchar n) ci ibp * malloc_token Ews (tarray tuchar n) ibp *
  data_at_ Ews (tarray tuchar m) obp * malloc_token Ews (tarray tuchar m) obp
  |-- bufs_opt (Some L) (InBuf Ews ibp 0 n ci) (Some (OutBuf Ews obp 0 m (Zrepeat Vundef m))) [] true true.
Proof.
  intros Hm. unfold bufs_opt, in_rep, out_opt, out_rep, in_tok, out_tok.
  rewrite <- (rbd_bytes_inflate_cs Ews n ci ibp), <- (rbd_tok_inflate_cs Ews n ibp),
          <- (rbd_tok_inflate_cs Ews m obp).
  assert (Eo: sublist 0 0 (Zrepeat Vundef m) ++ byte_vals [] ++ sublist (0 + Zlength (@nil Z)) m (Zrepeat Vundef m)
              = Zrepeat Vundef m).
  { rewrite sublist_nil. simpl. rewrite sublist_same; auto. rewrite Zlength_Zrepeat; lia. }
  rewrite Eo. rewrite (rbd_bytes_inflate_cs Ews m (Zrepeat Vundef m) obp).
  unfold data_at_. simpl default_val. unfold Zrepeat. cancel.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The header bytes the harness writes                                                            *)

(* stream[0] = (unsigned char) (cinfo << 4 | 8) *)
Lemma rbd_b0_val c: 0 <= c <= 7 ->
  Int.zero_ext 8 (Int.zero_ext 8 (Int.or (Int.shl (Int.repr c) (Int.repr 4)) (Int.repr 8))) = Int.repr (rbd_b0 c).
Proof.
  intros Hc. assert (c = 0 \/ c = 1 \/ c = 2 \/ c = 3 \/ c = 4 \/ c = 5 \/ c = 6 \/ c = 7) by lia.
  repeat destruct H as [-> | H]; [reflexivity .. | subst; reflexivity].
Qed.

(* the two stores into stream[1]: f0 = (x & 0xc0) | 0x20, then f0 + FCHECK, as main computes them (int
   arithmetic, % on signed ints, truncated to unsigned char) *)
Definition rbd_f0_int (x: Z) : int :=
  Int.zero_ext 8 (Int.zero_ext 8 (Int.or (Int.and (Int.repr x) (Int.repr 192)) (Int.repr 32))).
Definition rbd_b1_int (c x: Z) : int :=
  Int.zero_ext 8 (Int.zero_ext 8
    (Int.add (Int.repr (rbd_f0 x))
       (Int.mods (Int.sub (Int.repr 31)
                    (Int.mods (Int.add (Int.mul (Int.repr (rbd_b0 c)) (Int.repr 256)) (Int.repr (rbd_f0 x)))
                       (Int.repr 31))) (Int.repr 31)))).

(* checked for every cinfo 0..7 and every byte x *)
Definition rbd_hdr_chk (c x: Z) : bool :=
  Int.eq (rbd_f0_int x) (Int.repr (rbd_f0 x)) && Int.eq (rbd_b1_int c x) (Int.repr (rbd_b1 c x)) &&
  (0 <=? rbd_f0 x) && (rbd_f0 x <=? 255) && (0 <=? rbd_b1 c x) && (rbd_b1 c x <=? 255).

Lemma rbd_hdr_chk_all :
  forallb (fun c => forallb (fun x => rbd_hdr_chk (Z.of_nat c) (Z.of_nat x)) (seq 0 256)) (seq 0 8) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma rbd_hdr_ok c x: 0 <= c <= 7 -> 0 <= x <= 255 -> rbd_hdr_chk c x = true.
Proof.
  intros Hc Hx. pose proof rbd_hdr_chk_all as A. rewrite forallb_forall in A.
  specialize (A (Z.to_nat c)). rewrite in_seq in A. specialize (A ltac:(lia)).
  rewrite forallb_forall in A. specialize (A (Z.to_nat x)). rewrite in_seq in A. specialize (A ltac:(lia)).
  rewrite !Z2Nat.id in A by lia. exact A.
Qed.

Lemma rbd_f0_val x: 0 <= x <= 255 -> rbd_f0_int x = Int.repr (rbd_f0 x) /\ 0 <= rbd_f0 x <= 255.
Proof.
  intros Hx. pose proof (rbd_hdr_ok 0 x ltac:(lia) Hx) as K. unfold rbd_hdr_chk in K.
  rewrite !andb_true_iff, !Z.leb_le in K. destruct K as [[[[[K1 _] ?] ?] _] _].
  split; [apply Int.same_if_eq; exact K1 | lia].
Qed.

Lemma rbd_b1_val c x: 0 <= c <= 7 -> 0 <= x <= 255 -> rbd_b1_int c x = Int.repr (rbd_b1 c x) /\ 0 <= rbd_b1 c x <= 255.
Proof.
  intros Hc Hx. pose proof (rbd_hdr_ok c x Hc Hx) as K. unfold rbd_hdr_chk in K.
  rewrite !andb_true_iff, !Z.leb_le in K. destruct K as [[[[[_ K2] _] _] ?] ?].
  split; [apply Int.same_if_eq; exact K2 | lia].
Qed.

(* inflateInit2_ with windowBits 8..15: accepted, a zlib stream (wrap 5) without a gz_header *)
Lemma rbd_init_facts sp w: 8 <= w <= 15 ->
  wbits_ok w = true /\ i_wrap (l_s (init_live sp w)) = 5 /\ i_head (l_s (init_live sp w)) = false.
Proof.
  intros Hw. assert (w = 8 \/ w = 9 \/ w = 10 \/ w = 11 \/ w = 12 \/ w = 13 \/ w = 14 \/ w = 15) as T by lia.
  repeat destruct T as [-> | T]; [repeat split; reflexivity .. | subst; repeat split; reflexivity].
Qed.

(* the state after inflateInit2_ (mode HEAD) satisfies the wide invariant of a saved state *)
Lemma rbd_init_swfW sp w: 8 <= w <= 15 -> swfW (l_s (init_live sp w)).
Proof.
  intros Hw. assert (w = 8 \/ w = 9 \/ w = 10 \/ w = 11 \/ w = 12 \/ w = 13 \/ w = 14 \/ w = 15) as T by lia.
  repeat destruct T as [-> | T]; [split; intro E; discriminate E .. | subst; split; intro E; discriminate E].
Qed.

Lemma rbd_upd_bytes i (l: list Z) v:
  upd_Znth i (bytes_rep l) (Vint (Int.repr v)) = bytes_rep (upd_Znth i l v).
Proof. unfold bytes_rep. apply (upd_Znth_map (fun b => Vint (Int.repr b))). Qed.

Lemma rbd_znth_bytes i (l: list Z): 0 <= i < Zlength l -> Znth i (bytes_rep l) = Vint (Int.repr (Znth i l)).
Proof. intros Hi. unfold bytes_rep. rewrite Znth_map by lia. reflexivity. Qed.

Lemma rbd_byte_range i (l: list Z): is_bytes l -> 0 <= i < Zlength l -> 0 <= Znth i l <= 255.
Proof. intros Hb Hi. unfold is_bytes in Hb. rewrite Forall_forall in Hb. apply Hb, Znth_In; lia. Qed.

(* VST's after_forward_call simplifies remove_localdef_temp with `simpl rlt_ident_eq`, which runs away on main's
   identifiers (e.g. _stream against _stream_len); each identifier comparison is decided by vm_compute instead. *)
Ltac rbd_rlt_fix u :=
  lazymatch u with
  | context C [rlt_ident_eq ?a ?b] =>
      let v := eval vm_compute in (rlt_ident_eq a b) in
      let u2 := context C [v] in rbd_rlt_fix u2
  | _ => u
  end.

Ltac simplify_remove_localdef_temp ::=
  match goal with |- context [remove_localdef_temp ?i ?L] =>
    let u := constr:(remove_localdef_temp i L) in
    let u' := eval lazy delta [remove_localdef_temp] beta iota in u in
    let u' := rbd_rlt_fix u' in
    let u' := eval lazy beta iota in u' in
    let u' := eval lazy zeta in u' in
    change u with u'
  end.

(* the value of `q == NULL` for an allocated object q *)
Ltac rbd_cmp := match goal with |- context [sem_cmp_pp Ceq ?q _] =>
  match goal with Hf: field_compatible _ _ q |- _ =>
    let P := fresh in pose proof (field_compatible_isptr _ _ _ Hf) as P;
    destruct q; try contradiction; reflexivity end end.

(* `x = f(...); y = (cast) x;` as two statements (forward_call takes the casting Sset only when neutral) *)
Ltac rbd_split_call :=
  repeat match goal with |- semax _ _ (Ssequence (Ssequence (Ssequence _ _) _) _) _ => apply seq_assoc1 end;
  match goal with |- semax _ _ (Ssequence (Ssequence (Scall _ _ _) _) _) _ => apply seq_assoc1 end.

(* return 0 with the local z_stream given back (any contents) and everything else to TT *)
Ltac rbd_ret := forward; Exists (Int.repr 0); try sep_apply (data_at_data_at_ Tsh (Tstruct _z_stream_s noattr));
  entailer!.

(* a branch excluded by the value of its test *)
Ltac rbd_nob := exfalso; first [ congruence | exact (Int.one_not_zero ltac:(assumption)) | contradiction ].

(* ---------------------------------------------------------------------------------------------- *)
(* The segments of main's body                                                                    *)

Definition Delta_rd : tycontext := func_tycontext f_main (QPvarspecs p) Gmain nil.

(* main's postcondition after start_function (main_core_spec) *)
Definition POST_rd : ret_assert :=
  frame_ret_assert (function_body_ret_assert tint (EX r : int, PROP () RETURN (Vint r) SEP (TT))%argsassert)
    (stackframe_of f_main).

(* the postcondition of every suffix of the chain: it never ends normally *)
Definition POST_B : ret_assert := overridePost FF POST_rd.

(* main's body is `chain; return 0`, the chain s1; (s2; (s3; ...)); rd_seg k is its suffix from the k-th statement *)
Fixpoint rd_drop (n : nat) (s : statement) : statement :=
  match n, s with
  | O, _ => s
  | S n', Ssequence _ b => rd_drop n' b
  | _, _ => Sskip
  end.
Definition rd_chain (s : statement) : statement := match s with Ssequence a _ => a | _ => Sskip end.
Ltac rd_get_seg k :=
  let n := eval compute in (k - 1)%nat in
  let x := eval cbv beta iota zeta delta [rd_drop rd_chain f_main fn_body] in
    (rd_drop n (rd_chain (fn_body f_main))) in
  exact x.
Definition rd_seg1 : statement := ltac:(rd_get_seg 1%nat).
Definition rd_seg8 : statement := ltac:(rd_get_seg 8%nat).
Definition rd_seg9 : statement := ltac:(rd_get_seg 9%nat).
Definition rd_seg14 : statement := ltac:(rd_get_seg 14%nat).
Definition rd_seg17 : statement := ltac:(rd_get_seg 17%nat).

Lemma rd_body_eq : fn_body f_main = Ssequence rd_seg1 (Sreturn (Some (Econst_int (Int.repr 0) tint))).
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The assertions at the cuts.  Main's statements: 1-4 window_bits, stream_len, room, dict_len (upto),
   5-7 stream = any_bytes(stream_len), out = malloc(room), dict = any_bytes(dict_len), 8 their NULL test,
   9 cinfo = upto(window_bits - 8), 10-12 the stores of the header bytes stream[0] and stream[1], 13 dictid,
   14 gp_assume(adler32_z(1, dict, dict_len) != dictid), 15 new_stream(&strm), 16 inflateInit2 and its check,
   17 offer(&strm, stream, clip(stream_len), out, room), 18 gp_assert(inflate(...) == Z_NEED_DICT),
   19 gp_assert(inflateSetDictionary(...) == Z_DATA_ERROR). *)

Local Open Scope Z_scope.
Local Open Scope logic.

Definition t_zsl : type := Tstruct _z_stream_s noattr.

(* the inputs drawn: windowBits 8 + t1, stream_len 6 + t2, room, dict_len dlen *)
Definition rd_in (t1 t2 room dlen : Z) : Prop :=
  0 <= t1 <= 7 /\ 0 <= t2 <= Int64.max_signed - 6 /\ 0 <= room <= Int.max_unsigned /\ 0 <= dlen <= Int.max_unsigned.

Section Assertions.
Context (gv : globals) (vs : val).

(* after start_function *)
Definition rd_A0 : environ -> mpred :=
  PROP ()
  LOCAL (lvar _strm t_zsl vs; gvars gv)
  SEP (mem_mgr gv; tables_rep Ers gv; Zlib.proof.crc32.Spec.crc_table_at Ers gv; version_lit gv; rbd_hversion_lit gv;
       data_at_ Tsh t_zsl vs; zfuncs gv).

(* before statement 8 (the NULL test): the inputs drawn, the three objects made (or NULL) *)
Definition rd_A8 (t1 t2 room dlen : Z) (streamp : val) (src : list Z) (outp dictp : val) (dict : list Z) :
    environ -> mpred :=
  PROP (rd_in t1 t2 room dlen; Zlength src = (6 + t2)%Z; is_bytes src; Zlength dict = dlen; is_bytes dict)
  LOCAL (temp _dict dictp; temp _out outp; temp _stream streamp; temp _dict_len (Vlong (Int64.repr dlen));
         temp _room (Vlong (Int64.repr room)); temp _stream_len (Vlong (Int64.repr (6 + t2)));
         temp _window_bits (Vint (Int.repr (8 + t1))); lvar _strm t_zsl vs; gvars gv)
  SEP (mem_mgr gv;
       if eq_dec dictp nullval then emp
       else malloc_token Ews (tarray tuchar dlen) dictp * data_at Ews (tarray tuchar dlen) (bytes_rep dict) dictp;
       if eq_dec outp nullval then emp
       else malloc_token Ews (tarray tuchar room) outp * data_at_ Ews (tarray tuchar room) outp;
       if eq_dec streamp nullval then emp
       else malloc_token Ews (tarray tuchar (6 + t2)) streamp *
            data_at Ews (tarray tuchar (6 + t2)) (bytes_rep src) streamp;
       zfuncs gv; data_at_ Tsh t_zsl vs;
       tables_rep Ers gv; Zlib.proof.crc32.Spec.crc_table_at Ers gv; version_lit gv; rbd_hversion_lit gv).

(* before statement 9: no object is NULL *)
Definition rd_A9 (t1 t2 room dlen : Z) (streamp : val) (src : list Z) (outp dictp : val) (dict : list Z) :
    environ -> mpred :=
  PROP (rd_in t1 t2 room dlen; Zlength src = (6 + t2)%Z; is_bytes src; Zlength dict = dlen; is_bytes dict;
        streamp <> nullval; outp <> nullval; dictp <> nullval)
  LOCAL (temp _dict dictp; temp _out outp; temp _stream streamp; temp _dict_len (Vlong (Int64.repr dlen));
         temp _room (Vlong (Int64.repr room)); temp _stream_len (Vlong (Int64.repr (6 + t2)));
         temp _window_bits (Vint (Int.repr (8 + t1))); lvar _strm t_zsl vs; gvars gv)
  SEP (mem_mgr gv; malloc_token Ews (tarray tuchar dlen) dictp;
       data_at Ews (tarray tuchar dlen) (bytes_rep dict) dictp;
       malloc_token Ews (tarray tuchar room) outp; data_at_ Ews (tarray tuchar room) outp;
       malloc_token Ews (tarray tuchar (6 + t2)) streamp;
       data_at Ews (tarray tuchar (6 + t2)) (bytes_rep src) streamp;
       zfuncs gv; data_at_ Tsh t_zsl vs;
       tables_rep Ers gv; Zlib.proof.crc32.Spec.crc_table_at Ers gv; version_lit gv; rbd_hversion_lit gv).

(* the stream bytes s after the header stores: CMF and FLG as the theory's rbd_b0 / rbd_b1 *)
Definition rd_hdr (t1 t2 : Z) (s : list Z) (cinfo x : Z) : Prop :=
  Zlength s = 6 + t2 /\ is_bytes s /\ 0 <= cinfo <= t1 /\ 0 <= x <= 255 /\
  Znth 0 s = rbd_b0 cinfo /\ Znth 1 s = rbd_b1 cinfo x.

(* before statement 14 (the gp_assume on the dictionary's Adler-32): the header written, dictid read *)
Definition rd_A14 (t1 t2 room dlen : Z) (streamp : val) (s : list Z) (outp dictp : val) (dict : list Z)
    (cinfo x : Z) : environ -> mpred :=
  PROP (rd_in t1 t2 room dlen; rd_hdr t1 t2 s cinfo x; Zlength dict = dlen; is_bytes dict;
        streamp <> nullval; outp <> nullval; dictp <> nullval)
  LOCAL (temp _dictid (Vlong (Int64.repr (rbd_dictid s)));
         temp _dict dictp; temp _out outp; temp _stream streamp; temp _dict_len (Vlong (Int64.repr dlen));
         temp _room (Vlong (Int64.repr room)); temp _stream_len (Vlong (Int64.repr (6 + t2)));
         temp _window_bits (Vint (Int.repr (8 + t1))); lvar _strm t_zsl vs; gvars gv)
  SEP (mem_mgr gv; malloc_token Ews (tarray tuchar dlen) dictp;
       data_at Ews (tarray tuchar dlen) (bytes_rep dict) dictp;
       malloc_token Ews (tarray tuchar room) outp; data_at_ Ews (tarray tuchar room) outp;
       malloc_token Ews (tarray tuchar (6 + t2)) streamp;
       data_at Ews (tarray tuchar (6 + t2)) (bytes_rep s) streamp;
       zfuncs gv; data_at_ Tsh t_zsl vs;
       tables_rep Ers gv; Zlib.proof.crc32.Spec.crc_table_at Ers gv; version_lit gv; rbd_hversion_lit gv).

(* before statement 17 (offer): the dictionary's Adler-32 is not the id; inflateInit2_ returned Z_OK with the
   state init_live sp (8 + t1); the local z_stream as laws_common's view of its fields *)
Definition rd_A17 (t1 t2 room dlen : Z) (streamp : val) (s : list Z) (outp dictp : val) (dict : list Z)
    (cinfo x : Z) (sp : val) : environ -> mpred :=
  PROP (rd_in t1 t2 room dlen; rd_hdr t1 t2 s cinfo x; Zlength dict = dlen; is_bytes dict;
        streamp <> nullval; outp <> nullval; dictp <> nullval; isptr vs;
        adler32_z_val 1 dict <> rbd_dictid s; live_ok (init_live sp (8 + t1)))
  LOCAL (temp _dict dictp; temp _out outp; temp _stream streamp; temp _dict_len (Vlong (Int64.repr dlen));
         temp _room (Vlong (Int64.repr room)); temp _stream_len (Vlong (Int64.repr (6 + t2)));
         lvar _strm t_zsl vs; gvars gv)
  SEP (@data_at Zlib.units.Compress.CS Tsh t_zs
         (zs_val nullval (Vint (Int.repr 0)) (Vlong (Int64.repr 0)) nullval (Vint (Int.repr 0))
            (Vlong (Int64.repr 0)) nullval (l_sp (init_live sp (8 + t1))) (gv Zlib.inflate.code._zcalloc)
            (gv Zlib.inflate.code._zcfree) nullval (Vint (Int.repr 0)) (Vlong (Int64.repr 1)) Vundef) vs;
       state_mem gv vs (init_live sp (8 + t1));
       mem_mgr gv; zfuncs gv; malloc_token Ews (tarray tuchar dlen) dictp;
       data_at Ews (tarray tuchar dlen) (bytes_rep dict) dictp;
       malloc_token Ews (tarray tuchar room) outp; data_at_ Ews (tarray tuchar room) outp;
       malloc_token Ews (tarray tuchar (6 + t2)) streamp;
       data_at Ews (tarray tuchar (6 + t2)) (bytes_rep s) streamp;
       tables_rep Ers gv; Zlib.proof.crc32.Spec.crc_table_at Ers gv; TT).

End Assertions.

(* ---------------------------------------------------------------------------------------------- *)
(* The segments, each from its cut to the end of main                                             *)

Definition seg_inputs_stmt : Prop :=
  forall {Espec : OracleKind} gv vs,
  (forall t1 t2 room dlen streamp src outp dictp dict,
     semax Delta_rd (rd_A8 gv vs t1 t2 room dlen streamp src outp dictp dict) rd_seg8 POST_B) ->
  semax Delta_rd (rd_A0 gv vs) rd_seg1 POST_B.

Definition seg_null_stmt : Prop :=
  forall {Espec : OracleKind} gv vs t1 t2 room dlen streamp src outp dictp dict,
  semax Delta_rd (rd_A9 gv vs t1 t2 room dlen streamp src outp dictp dict) rd_seg9 POST_B ->
  semax Delta_rd (rd_A8 gv vs t1 t2 room dlen streamp src outp dictp dict) rd_seg8 POST_B.

Definition seg_header_stmt : Prop :=
  forall {Espec : OracleKind} gv vs t1 t2 room dlen streamp src outp dictp dict,
  (forall s cinfo x,
     semax Delta_rd (rd_A14 gv vs t1 t2 room dlen streamp s outp dictp dict cinfo x) rd_seg14 POST_B) ->
  semax Delta_rd (rd_A9 gv vs t1 t2 room dlen streamp src outp dictp dict) rd_seg9 POST_B.

Definition seg_init_stmt : Prop :=
  forall {Espec : OracleKind} gv vs t1 t2 room dlen streamp s outp dictp dict cinfo x,
  (forall sp,
     semax Delta_rd (rd_A17 gv vs t1 t2 room dlen streamp s outp dictp dict cinfo x sp) rd_seg17 POST_B) ->
  semax Delta_rd (rd_A14 gv vs t1 t2 room dlen streamp s outp dictp dict cinfo x) rd_seg14 POST_B.

Definition seg_calls_stmt : Prop :=
  rbd_theory_stmt ->
  forall {Espec : OracleKind} gv vs t1 t2 room dlen streamp s outp dictp dict cinfo x sp,
  semax Delta_rd (rd_A17 gv vs t1 t2 room dlen streamp s outp dictp dict cinfo x sp) rd_seg17 POST_B.

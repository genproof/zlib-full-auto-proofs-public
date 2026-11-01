(* Laws res_free_deflate and res_memory_deflate: what main's body proof needs between the calls, at the law's
   compspecs CSa (main's two locals struct z_stream_s strm and struct count count):
   - [call_alone]: VST's forward_call on the pair [_t = f(...); x = _t;] when f's postcondition is existential
     (any_bytes, malloc) is very slow at CSa; on the call alone (the pair reassociated) it is not;
   - the locals as counted_stream's specification takes them (z_stream at the compress unit's compspecs, struct
     count at the harness unit's, CS_count), and the struct count back at CSa (main reads count.peak);
   - [init_total]: deflateInit2_'s model is defined for any int parameters (the PROP of its specification). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.za.deflate.ZSpec.
Require Import Zlib.proof.deflate.LawFacts.
Require Zlib.proof.deflate.LTApiInit Zlib.proof.deflate.LTCInitKit.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.counted.Spec.
Require Zlib.proof.harness.counted.Kit.
Require Import Zlib.proof.harness.res_alloc_deflate.ACS.
Require Zlib.units.Compress.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.deflate.DSpec.
Require Zlib.proof.harness.bound_common.BoundKit.
Local Open Scope logic.

Ltac call_alone := rewrite <- seq_assoc; rewrite <- seq_assoc.

(* main's struct z_stream_s, uninitialised, as counted_stream takes it *)
Lemma strm_local (p : val) :
  @data_at_ CSa Tsh (Tstruct HL._z_stream_s noattr) p =
  @data_at Zlib.units.Compress.CS Tsh t_zs
    (zs_val Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef) p.
Proof.
  set (u := zs_val Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef).
  assert (E : @data_at Zlib.units.Compress.CS Tsh t_zs u p = @data_at CSa Tsh t_zs u p).
  { change t_zs with (Tstruct HL._z_stream_s noattr).
    rewrite (@data_at_change_composite Zlib.units.Compress.CS CSa CC_compress Tsh
               (Tstruct HL._z_stream_s noattr) u u (JMeq_refl _)) by reflexivity.
    reflexivity. }
  rewrite E. reflexivity.
Qed.

(* main's struct count, as counted_stream takes it and as main reads it *)
Lemma count_local_ (p : val) :
  @data_at_ CSa Tsh (Tstruct HC._count noattr) p = @data_at_ CS_count Tsh t_count p.
Proof.
  unfold t_count.
  rewrite (@data_at__change_composite CS_count CSa CC_count Tsh (Tstruct HC._count noattr)) by reflexivity.
  reflexivity.
Qed.

Lemma count_local (v : val * (val * val)) (p : val) :
  @data_at CS_count Tsh t_count v p = @data_at CSa Tsh (Tstruct HC._count noattr) v p.
Proof.
  unfold t_count.
  rewrite (@data_at_change_composite CS_count CSa CC_count Tsh (Tstruct HC._count noattr) v v (JMeq_refl _))
    by reflexivity.
  reflexivity.
Qed.

(* deflateInit2_'s model is defined for any parameters and any outcome of the allocations *)
Lemma init_total level method wbits mem strategy a1 a2 a3 a4 a5 z :
  exists r, c_deflateInit2_ true true false level method wbits mem strategy a1 a2 a3 a4 a5 z = Some r.
Proof.
  rewrite Zlib.proof.deflate.LTApiInit.init_shape.
  destruct (params_ok level method wbits mem strategy) eqn:P; [ | eauto].
  destruct a1; [ | eauto]. destruct (a2 && a3 && a4 && a5)%bool; [ | eauto].
  rewrite (Zlib.proof.deflate.LTCInitKit.init_eq _ _ _ _ _ _ P). eauto.
Qed.

(* the counting allocator's state right after counted_stream: no event yet *)
Lemma count_res_nil (cp : val) (gv : globals) :
  (mem_mgr gv * @data_at CS_count Tsh t_count (Vlong (Int64.repr 0), (Vlong (Int64.repr 0), Vint (Int.repr 0))) cp)%logic =
  count_res cp gv [].
Proof. reflexivity. Qed.

(* an unsigned int drawn by nondet_u32, cast to int: the signed value *)
Lemma vint_signed (x : Z) : Vint (Int.repr x) = Vint (Int.repr (Int.signed (Int.repr x))).
Proof. rewrite Int.repr_signed. reflexivity. Qed.

(* The [counted_stream] postcondition's two pieces and the two function pointers, as deflateInit2_'s
   allocator: its [za_funcs] at DCS.CS and its state with no event. *)
Lemma counted_pieces (cp za zf : val) (gv : globals) :
  (func_ptr' (snd count_alloc_spec) za * func_ptr' (snd count_free_spec) zf * mem_mgr gv *
   @data_at CS_count Tsh t_count (Vlong (Int64.repr 0), (Vlong (Int64.repr 0), Vint (Int.repr 0))) cp)%logic
  |-- (@za_funcs DCS.CS (counted cp za zf) * count_res cp gv [])%logic.
Proof.
  rewrite <- count_res_nil.
  sep_apply (@Zlib.proof.harness.counted.Kit.counted_za_funcs DCS.CS cp za zf). cancel.
Qed.

(* main's returns: its z_stream, the part the specifications held (Ews, at DCS.CS) and the part main kept
   (the complement of Ews, at the compress unit's compspecs), is again the uninitialised local at CSa *)
Lemma strm_back (p : val) :
  (@data_at_ DCS.CS Ews t_strm p *
   @data_at_ Zlib.units.Compress.CS Zlib.proof.harness.bound_common.BoundKit.Ecomp t_zs p)%logic
  |-- @data_at_ CSa Tsh (Tstruct HL._z_stream_s noattr) p.
Proof.
  rewrite (@data_at__change_composite DCS.CS CSa CC_dcs Ews t_strm) by reflexivity.
  change t_zs with (Tstruct HL._z_stream_s noattr).
  rewrite (@data_at__change_composite Zlib.units.Compress.CS CSa CC_compress
             Zlib.proof.harness.bound_common.BoundKit.Ecomp (Tstruct HL._z_stream_s noattr)) by reflexivity.
  change t_strm with (Tstruct HL._z_stream_s noattr).
  rewrite (Zlib.proof.harness.bound_common.BoundKit.data_at__Tsh_split (Tstruct HL._z_stream_s noattr) p).
  apply derives_refl.
Qed.

(* the counting allocator's state at a return of main: struct count back as the uninitialised local *)
Lemma count_back (cp : val) (gv : globals) (tr : list zev) :
  count_res cp gv tr |-- (@data_at_ CSa Tsh (Tstruct HC._count noattr) cp * TT)%logic.
Proof.
  unfold count_res. rewrite count_local. sep_apply (@data_at_data_at_ CSa). cancel.
Qed.

(* deflate()'s output space: the object malloc gave (any contents), at DCS.CS; when it is empty its malloc token
   is the witness that next_out is weakly valid (DSpec.wv_ok) *)
Definition out_wv (n : Z) : wvw := if n =? 0 then WVtok (tarray tuchar 0) else WVnone.

Lemma out_wv_ok (n : Z) : n = 0 -> wv_ok (out_wv n).
Proof. intros E. subst n. cbn. lia. Qed.

Lemma out_split (n : Z) (p : val) :
  0 <= n ->
  (@malloc_token CSa Ews (tarray tuchar n) p * @data_at_ CSa Ews (tarray tuchar n) p)%logic
  |-- (@data_at DCS.CS Ews (tarray tuchar (Zlength (Zrepeat Vundef n))) (Zrepeat Vundef n) p *
       wv_at (out_wv n) p * TT)%logic.
Proof.
  intros Hn. replace (Zlength (Zrepeat Vundef n)) with n by list_solve.
  rewrite (data_at__tuchar_cs CSa DCS.CS).
  unfold data_at_, field_at_.
  change (@default_val DCS.CS (tarray tuchar n)) with (Zrepeat Vundef n).
  fold (@data_at DCS.CS Ews (tarray tuchar n) (Zrepeat Vundef n) p).
  unfold out_wv, wv_at. destruct (Z.eqb_spec n 0).
  - subst n.
    rewrite <- (@malloc_token_change_composite DCS.CS CSa CC_dcs Ews (tarray tuchar 0)) by reflexivity.
    cancel.
  - cancel.
Qed.

(* the application's members after offer(), as deflate()'s specification takes them *)
Lemma api_fold (sp p : val) (ain tin : Z) (nout : val) (aout tout : Z) (msgv : val) (adler : Z) :
  isptr p -> u32_ok ain -> u64_ok tin -> u32_ok aout -> u64_ok tout -> u64_ok adler ->
  (@field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._next_in) p sp *
   @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._avail_in) (Vint (Int.repr ain)) sp *
   @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._total_in) (vl tin) sp *
   @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._next_out) nout sp *
   @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._avail_out) (Vint (Int.repr aout)) sp *
   @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._total_out) (vl tout) sp *
   @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._msg) msgv sp *
   @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._adler) (vl adler) sp)%logic
  |-- api_fields sp (offset_val 0 p) ain tin nout aout tout msgv adler.
Proof.
  intros Hp H1 H2 H3 H4 H5. rewrite isptr_offset_val_zero by exact Hp.
  unfold api_fields. rewrite prop_true_andp by auto. unfold vi. cancel.
Qed.

(* a state without gzip header: its hdr_at is empty *)
Lemma add_hdr (P : mpred) (s : dstate) (hx : share * val * val * val) :
  d_gzhead s = None -> P |-- (P * hdr_at (Some s) nullval hx)%logic.
Proof. intros E. unfold hdr_at. rewrite E. entailer!. Qed.

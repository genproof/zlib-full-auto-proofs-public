(* Laws res_free_inflate and res_memory_inflate: what main's body proofs need between the calls, at the law's
   compspecs CSi (main's two locals, struct z_stream_s strm and struct count count):
   - the locals as counted_stream's specification takes them (z_stream at the compress unit's compspecs, struct
     count at the harness unit's, CS_count), and back at CSi;
   - the stream after counted_stream as inflateInit2_'s specification takes it (raw_strm at the inflate unit's
     compspecs) and the counting allocator as inflate.c's allocator (za_funcs, its state with no event). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Zlib.proof.za.inflate_api.USpec.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.counted.Spec.
Require Zlib.proof.harness.counted.Kit.
Require Import Zlib.proof.harness.res_inflate.ResICS Zlib.proof.harness.res_inflate.ResISpecs.
Require Zlib.units.Compress Zlib.units.Inflate.
Require Zlib.harness.res_free_inflate.code.
Require Import QuickProof.Assembly.
Require Zlib.units.Adler32.
Local Open Scope logic.

Ltac call_alone := rewrite <- seq_assoc; rewrite <- seq_assoc.

Definition tzs : type := Tstruct Zlib.harness.res_free_inflate.code._z_stream_s noattr.
Definition tcount : type := Tstruct Zlib.harness.res_free_inflate.code._count noattr.

(* main's struct z_stream_s, uninitialised, as counted_stream takes it *)
Lemma strm_local (p : val) :
  @data_at_ CSi Tsh tzs p =
  @data_at Zlib.units.Compress.CS Tsh t_zs
    (zs_val Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef) p.
Proof.
  unfold data_at_, zs_val, t_zs. symmetry.
  apply equal_f; apply (@data_at_change_composite _ _ CC_compress); [apply JMeq_refl | reflexivity].
Qed.

(* main's struct count, as counted_stream takes it and as main reads it *)
Lemma count_local_ (p : val) : @data_at_ CSi Tsh tcount p = @data_at_ CS_count Tsh t_count p.
Proof.
  unfold data_at_, field_at_. symmetry. change tcount with t_count.
  change (@default_val CSi t_count) with (@default_val CS_count t_count).
  apply equal_f; apply (@field_at_change_composite _ _ CC_count); [apply JMeq_refl | reflexivity].
Qed.

Lemma count_local (v : val * (val * val)) (p : val) :
  @data_at CS_count Tsh t_count v p = @data_at CSi Tsh tcount v p.
Proof.
  change tcount with t_count.
  apply equal_f; apply (@data_at_change_composite _ _ CC_count); [apply JMeq_refl | reflexivity].
Qed.

(* a z_stream at the compress unit's compspecs (laws_common, counted_stream) is raw_strm at the inflate unit's *)
Lemma zs_raw gv sh q ni ai ti no ao to msgv stv za zf opq dt ad rs :
  @data_at Zlib.units.Compress.CS sh t_zs (zs_val ni ai ti no ao to msgv stv za zf opq dt ad rs) q =
  raw_strm gv sh q (RF ni ai ti no ao to dt ad rs) msgv stv za zf opq.
Proof.
  unfold raw_strm, zs_val, t_zs. simpl.
  transitivity (@data_at CSi sh tzs (ni, (ai, (ti, (no, (ao, (to, (msgv, (stv, (za, (zf, (opq, (dt, (ad, rs))))))))))))) q).
  - apply equal_f; apply (@data_at_change_composite _ _ CC_compress); [apply JMeq_refl | reflexivity].
  - symmetry. apply equal_f; apply (@data_at_change_composite _ _ CC_inflate); [apply JMeq_refl | reflexivity].
Qed.

(* any raw_strm is main's local again *)
Lemma raw_undef gv sh q r msgv stv za zf opq :
  raw_strm gv sh q r msgv stv za zf opq |-- @data_at_ CSi sh tzs q.
Proof.
  destruct r. rewrite <- zs_raw. sep_apply (@data_at_data_at_ Zlib.units.Compress.CS).
  unfold data_at_. apply derives_refl'.
  apply equal_f; apply (@data_at_change_composite _ _ CC_compress); [apply JMeq_refl | reflexivity].
Qed.

(* The [counted_stream] postcondition's struct count and the two function pointers, as inflate.c's
   allocator: its [za_funcs] at the inflate unit's compspecs and its state with no event. *)
Lemma counted_pieces (cp za zf : val) (gv : globals) :
  (func_ptr' (snd count_alloc_spec) za * func_ptr' (snd count_free_spec) zf * mem_mgr gv *
   @data_at CS_count Tsh t_count (Vlong (Int64.repr 0), (Vlong (Int64.repr 0), Vint (Int.repr 0))) cp)%logic
  |-- (@za_funcs Zlib.units.Inflate.CS (counted cp za zf) * count_res cp gv [])%logic.
Proof.
  sep_apply (@Zlib.proof.harness.counted.Kit.counted_za_funcs Zlib.units.Inflate.CS cp za zf).
  unfold count_res. cancel.
Qed.

(* the counting allocator's state at a return of main: struct count back as the uninitialised local *)
Lemma count_back (cp : val) (gv : globals) (tr : list zev) :
  count_res cp gv tr |-- (@data_at_ CSi Tsh tcount cp * TT)%logic.
Proof.
  unfold count_res. rewrite count_local. sep_apply (@data_at_data_at_ CSi). cancel.
Qed.

(* an unsigned int drawn by nondet_u32, cast to int: the signed value *)
Lemma vint_signed (x : Z) : Vint (Int.repr x) = Vint (Int.repr (Int.signed (Int.repr x))).
Proof. rewrite Int.repr_signed. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* The stream after a successful inflateInit2_, offer() and inflate()      *)
(* ---------------------------------------------------------------------- *)

(* the state inflateInit2_(strm, w) makes, and strm->adler after it: undefined on a raw stream (wrap = 0),
   wrap & 1 otherwise (inflateResetKeep) *)
Definition init_wrap (w : Z) : Z := i_wrap (l_s (init_live nullval w)).
Definition init_adler (w : Z) : Z := if init_wrap w =? 0 then 0 else Z.land (init_wrap w) 1.
Definition init_cell (w : Z) : adler_cell := AdlerCell (init_wrap w =? 0).

(* main's stream before inflateInit2_ (after counted_stream) *)
Definition raw0 : rawf :=
  RF nullval (Vint (Int.repr 0)) Vundef nullval (Vint (Int.repr 0)) Vundef Vundef Vundef Vundef.

(* the application's fields after offer(strm, in, n, out, room) *)
Definition zinit (dp : val) (n : Z) (op : val) (room : Z) (w : Z) : zfields :=
  ZF dp n 0 op room 0 None 0 (init_adler w) Vundef.

(* after inflateInit2_ returned Z_OK: the struct z_stream as offer() takes it, and the state *)
Lemma init_offer_pre gv cp za zf sp w strmp :
  @istream_raw_za (counted cp za zf) gv Tsh strmp (raw_after_init raw0 (l_s (init_live sp w))) (init_live sp w)
  |-- !! live_ok (init_live sp w) &&
      (@data_at Zlib.units.Compress.CS Tsh t_zs
         (zs_val nullval (Vint (Int.repr 0)) (Vlong (Int64.repr 0)) nullval (Vint (Int.repr 0))
                 (Vlong (Int64.repr 0)) nullval sp za zf cp (Vint (Int.repr 0))
                 (@adler_val (init_cell w) (init_adler w)) Vundef) strmp *
       @state_mem_za (counted cp za zf) gv strmp (init_live sp w)).
Proof.
  unfold istream_raw_za. Intros. rewrite prop_true_andp by tauto. unfold raw_after_init, raw0.
  cbn [rf_ni rf_ai rf_tin rf_no rf_ao rf_tout rf_dt rf_adler rf_res]. rewrite <- (zs_raw gv).
  unfold init_adler, init_cell, adler_val, init_wrap. cbn [av_undef].
  change (l_s (init_live nullval w)) with (l_s (init_live sp w)).
  destruct (i_wrap (l_s (init_live sp w)) =? 0); simpl za_alloc; simpl za_free; simpl za_opaque; cancel.
Qed.

(* after offer(): the stream as inflate() takes it, with the adler cell of the stream's wrap *)
Lemma offer_istream gv cp za zf sp w strmp dp n op room :
  0 <= n <= Int.max_unsigned -> 0 <= room <= Int.max_unsigned -> live_ok (init_live sp w) ->
  @data_at Zlib.units.Compress.CS Tsh t_zs
    (zs_val dp (Vint (Int.repr n)) (Vlong (Int64.repr 0)) op (Vint (Int.repr room))
            (Vlong (Int64.repr 0)) nullval sp za zf cp (Vint (Int.repr 0))
            (@adler_val (init_cell w) (init_adler w)) Vundef) strmp *
  @state_mem_za (counted cp za zf) gv strmp (init_live sp w)
  |-- @istream_za (counted cp za zf) (init_cell w) gv Tsh strmp (zinit dp n op room w) (Some (init_live sp w)).
Proof.
  intros Hn Hr HL. rewrite (zs_raw gv).
  rewrite <- (@istream_raw_istream_za (counted cp za zf) (init_cell w) gv Tsh strmp (zinit dp n op room w)
                (init_live sp w)).
  2: { unfold zf_ok, zinit, init_adler; cbn.
       assert (0 <= Z.land (init_wrap w) 1 <= 1).
       { pose proof (Z.land_ones (init_wrap w) 1 ltac:(lia)) as E. change (Z.ones 1) with 1 in E. rewrite E.
         pose proof (Z.mod_pos_bound (init_wrap w) (2^1) ltac:(lia)). simpl in *. lia. }
       destruct (init_wrap w =? 0); rep_lia. }
  2: reflexivity.
  unfold istream_raw_za, zinit. cbn [zf_ni zf_ai zf_tin zf_no zf_ao zf_tout zf_dt zf_adler zf_res].
  simpl za_alloc; simpl za_free; simpl za_opaque. entailer!. apply derives_refl.
Qed.

Lemma malloc_token_tuchar_cs (cs1 cs2 : compspecs) sh n p :
  @malloc_token cs1 sh (tarray tuchar n) p = @malloc_token cs2 sh (tarray tuchar n) p.
Proof.
  apply (f_equal (fun f => f p)). apply (@malloc_token_change_composite cs1 cs2 (CCE_any cs1 cs2) sh (tarray tuchar n)). reflexivity.
Qed.

(* inflate()'s input: the n bytes bs from any_bytes; its output space: the room bytes from malloc *)
Definition ibuf (dp : val) (n : Z) (bs : list Z) : inbuf := InBuf Ews dp 0 n (bytes_rep bs).
Definition obuf (op : val) (room : Z) : outbuf := OutBuf Ews op 0 room (Zrepeat Vundef room).

Lemma bufs_pre L dp n bs op room :
  Zlength bs = n -> 0 <= room ->
  (@malloc_token Zlib.units.Adler32.CS Ews (tarray tuchar n) dp *
   @data_at Zlib.units.Adler32.CS Ews (tarray tuchar n) (bytes_rep bs) dp *
   @malloc_token CSi Ews (tarray tuchar room) op * @data_at_ CSi Ews (tarray tuchar room) op)
  |-- bufs_opt (Some L) (ibuf dp n bs) (Some (obuf op room)) [] true true.
Proof.
  intros Hn Hr. unfold bufs_opt, in_rep, out_opt, out_rep, in_tok, out_tok, ibuf, obuf.
  rewrite (malloc_token_tuchar_cs Zlib.units.Adler32.CS Zlib.units.Inflate.CS).
  rewrite (malloc_token_tuchar_cs CSi Zlib.units.Inflate.CS).
  rewrite (data_at_tuchar_cs Zlib.units.Adler32.CS Zlib.units.Inflate.CS).
  rewrite (data_at__tuchar_cs CSi Zlib.units.Inflate.CS).
  assert (E: sublist 0 0 (Zrepeat Vundef room) ++ byte_vals [] ++
             sublist (0 + Zlength (@nil Z)) room (Zrepeat Vundef room) = Zrepeat Vundef room).
  { rewrite sublist_nil. simpl. rewrite sublist_same; auto. rewrite Zlength_Zrepeat; lia. }
  rewrite E. unfold data_at_, field_at_.
  change (@default_val Zlib.units.Inflate.CS (tarray tuchar room)) with (Zrepeat Vundef room).
  cancel.
Qed.

(* a closed stream (strm->state = NULL, after inflateEnd) is main's local again *)
Lemma closed_local {ZA : zallocator} {ZAV : adler_cell} gv sh strmp z :
  @istream_za ZA ZAV gv sh strmp z None |-- @data_at_ CSi sh tzs strmp.
Proof.
  unfold istream_za, zstrm_at_za, strm_rep_za. Intros.
  sep_apply (@data_at_data_at_ Zlib.units.Inflate.CS).
  rewrite (@data_at__change_composite Zlib.units.Inflate.CS CSi CC_inflate sh t_strm) by reflexivity.
  apply derives_refl.
Qed.

(* a live stream, at a return of main: its struct z_stream is main's local again (the state is left over) *)
Lemma live_local {ZA : zallocator} {ZAV : adler_cell} gv sh strmp z L :
  @istream_za ZA ZAV gv sh strmp z (Some L) |-- (@data_at_ CSi sh tzs strmp * TT)%logic.
Proof.
  unfold istream_za, zstrm_at_za, strm_rep_za. Intros.
  sep_apply (@data_at_data_at_ Zlib.units.Inflate.CS).
  rewrite (@data_at__change_composite Zlib.units.Inflate.CS CSi CC_inflate sh t_strm) by reflexivity.
  cancel.
Qed.

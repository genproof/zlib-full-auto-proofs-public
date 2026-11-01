(** * The body of compress.c's compress2_z against RTCSpecW.compress2_z_spec_w (any sizes)

    As RTCBC2z.v (sizes up to (uInt)-1, each given in one piece), with compress2_z's loop over pieces: each
    iteration refills avail_out / avail_in with at most (uInt)-1 bytes when exhausted (RTC2.c2_give) and calls
    deflate.  DSpec.deflate_spec takes an input object and an output space of at most 2^32-1 bytes: the source
    is presented as its three parts [0, next_in), [next_in, next_in + avail_in) (deflate's input object) and the
    rest, the destination as [0, next_out), [next_out, next_out + avail_out) (deflate's output space) and the
    rest; the model's call on the whole source is moved to the slice by InSlice.deflate_slice.  A Z_NULL source
    (no bytes, RTCSpecW.c2_src) is given to deflate as next_in = Z_NULL with no input object (DSpecN.deflate_specN:
    [in_ptrN], [in_objN]); the lemmas [c2_src_open] / [c2_src_close] cut the source for both cases at once. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.DSpec Zlib.proof.deflate.DSpec9.
Require Import Zlib.proof.deflate.DSpecN.
Require Zlib.proof.deflate.Obligations Zlib.proof.deflate.Api_toend.
Require Zlib.proof.compress.CSpec.
Require Zlib.units.Compress.
Require Zlib.deflate.code.
Require Import Zlib.compress.code.
Require Import Zlib.proof.roundtrip.RTDIface Zlib.proof.roundtrip.RTC2.
Require Import Zlib.proof.roundtrip.RTCSpec Zlib.proof.roundtrip.RTCSpecW.
Require Import Zlib.proof.roundtrip.RTCBKit Zlib.proof.roundtrip.RTCBModel Zlib.proof.roundtrip.RTCBDest.
Require Import Zlib.proof.deflate.InitStrm Zlib.proof.roundtrip.RTCBPure.
Require Import Zlib.proof.roundtrip.RTCBC2z.
Require Import Zlib.proof.deflate.InSlice.
Require Zlib.proof.deflate.DeflateParams8.
Require Import Zlib.proof.deflate.LTBInit.
Local Open Scope logic.

#[local] Existing Instance Zlib.units.Compress.CS.

#[local] Instance CC_dc : change_composite_env DCS.CS Zlib.units.Compress.CS.
Proof. make_cs_preserve DCS.CS Zlib.units.Compress.CS. Defined.

(** ** Pure facts *)

(* deflateInit_ succeeds only with a level in -1..9 *)
Lemma c2_init_level level a1 a2 a3 a4 a5 z os z' :
  c_deflateInit2_ true true false level 8 15 8 0 a1 a2 a3 a4 a5 z = Some (os, z', Z_OK) -> -1 <= level <= 9.
Proof.
  intros H. rewrite bi_shape in H.
  destruct (params_ok level 8 15 8 0) eqn:P.
  - unfold LawFacts.params_ok in P. rewrite !andb_true_iff in P.
    destruct P as [[[[[[[[[[_ _] _] _] _] _] P1] P2] _] _] _].
    apply Z.leb_le in P1. apply Z.leb_le in P2.
    destruct (level =? -1) eqn:E; [apply Z.eqb_eq in E | ]; lia.
  - injection H as _ _ E. discriminate.
Qed.

(* one refill of compress2_z's loop: the space (or input) offered, [a] the stream's, [l] the bytes not given yet *)
Definition give_a (a l : Z) : Z := if a =? 0 then Z.min l umax else a.
Definition give_l (a l : Z) : Z := if a =? 0 then l - Z.min l umax else l.

Lemma give_shape src z left srcleft :
  c2_give src z left srcleft =
  (mkST src (z_next_in z) (give_a (z_avail_in z) srcleft) (z_total_in z) [] (give_a (z_avail_out z) left)
     (z_total_out z) (z_adler z) (z_msg z),
   give_l (z_avail_out z) left, give_l (z_avail_in z) srcleft,
   if give_l (z_avail_in z) srcleft =? 0 then Z_FINISH else Z_NO_FLUSH).
Proof.
  unfold c2_give, give_a, give_l.
  destruct (z_avail_out z =? 0), (z_avail_in z =? 0); reflexivity.
Qed.

Lemma give_range a l :
  0 <= a <= umax -> 0 <= l ->
  0 <= give_a a l <= umax /\ 0 <= give_l a l /\ give_a a l + give_l a l = a + l /\
  (give_a a l = 0 -> a = 0 /\ l = 0).
Proof. intros. unfold give_a, give_l, umax in *. destruct (Z.eqb_spec a 0); lia. Qed.

(** ** Arrays of bytes cut in two (deflate unit's compspecs) *)
Section Arr.
#[local] Existing Instance DCS.CS.

Lemma arr_split sh n m (l : list val) p :
  field_compatible (tarray tuchar n) [] p -> 0 <= m <= n -> Zlength l = n ->
  data_at sh (tarray tuchar n) l p =
  data_at sh (tarray tuchar m) (sublist 0 m l) p *
  data_at sh (tarray tuchar (n - m)) (sublist m n l) (offset_val m p).
Proof.
  intros FC Hm Hl. unfold tarray.
  rewrite (split2_data_at_Tarray_tuchar sh n m l p) by lia.
  rewrite fc_tuchar_off by (auto; lia). reflexivity.
Qed.

Lemma fc_rest n m p :
  field_compatible (tarray tuchar n) [] p -> 0 <= m <= n ->
  field_compatible (tarray tuchar (n - m)) [] (offset_val m p).
Proof.
  intros FC Hm. destruct (proj1 (field_compatible_Tarray_split tuchar m n p Hm) FC) as [_ F].
  unfold tarray in F. rewrite fc_tuchar_off in F by (auto; lia). exact F.
Qed.

(* the source: the bytes before next_in, deflate's input object [d, d + a), the rest *)
Lemma src_split sh (l : list Z) p d a :
  field_compatible (tarray tuchar (Zlength l)) [] p -> 0 <= d -> 0 <= a -> d + a <= Zlength l ->
  data_at sh (tarray tuchar (Zlength l)) (map vi l) p =
  data_at sh (tarray tuchar d) (sublist 0 d (map vi l)) p *
  data_at sh (tarray tuchar (Zlength (sublist d (d + a) l))) (map vi (sublist d (d + a) l)) (offset_val d p) *
  data_at sh (tarray tuchar (Zlength l - (d + a))) (sublist (d + a) (Zlength l) (map vi l)) (offset_val (d + a) p).
Proof.
  intros FC Hd Ha Hl. unfold tarray.
  rewrite (split3_data_at_Tarray_tuchar sh (Zlength l) d (d + a)) by (rewrite ?Zlength_map; lia).
  rewrite !fc_tuchar_off by (auto; lia).
  rewrite Zlength_sublist by lia. replace (d + a - d) with a by lia.
  replace (sublist d (d + a) (map vi l)) with (map vi (sublist d (d + a) l)) by (rewrite sublist_map; reflexivity).
  reflexivity.
Qed.

(* the destination: the bytes written (the last one apart when the space is used up, RTCBDest.dest_open), deflate's
   output space [k, k + a), the rest *)
Lemma dest_open3 k a cap (D : list val) dp :
  0 <= k -> 0 <= a -> k + a <= cap -> 0 < cap -> Zlength D = cap ->
  field_compatible (tarray tuchar cap) [] dp ->
  data_at Ews (tarray tuchar cap) D dp |--
  data_at Ews (tarray tuchar (kp k cap)) (sublist 0 (kp k cap) D) dp *
  data_at Ews (tarray tuchar (Zlength (sublist k (k + a) D))) (sublist k (k + a) D) (offset_val k dp) *
  data_at Ews (tarray tuchar (cap - (k + a))) (sublist (k + a) cap D) (offset_val (k + a) dp) *
  wv_at (wv_of k cap D) (offset_val k dp).
Proof.
  intros Hk Ha Hka Hc HD FC.
  sep_apply (dest_open k cap D dp ltac:(lia) Hc HD).
  rewrite (arr_split Ews (cap - k) a (sublist k cap D) (offset_val k dp)) by
    (try apply fc_rest; auto; try lia; rewrite Zlength_sublist; lia).
  rewrite offset_offset_val.
  replace (sublist 0 a (sublist k cap D)) with (sublist k (k + a) D) by list_solve.
  replace (sublist a (cap - k) (sublist k cap D)) with (sublist (k + a) cap D) by list_solve.
  rewrite Zlength_sublist by lia.
  replace (k + a - k) with a by lia. replace (cap - k - a) with (cap - (k + a)) by lia.
  replace (k + a) with (a + k) by lia.
  cancel.
Qed.

Lemma dest_close3 k a cap (D N : list val) dp :
  0 <= k -> 0 <= a -> k + a <= cap -> 0 < cap -> Zlength D = cap -> Zlength N = a ->
  field_compatible (tarray tuchar cap) [] dp ->
  data_at Ews (tarray tuchar (kp k cap)) (sublist 0 (kp k cap) D) dp *
  data_at Ews (tarray tuchar a) N (offset_val k dp) *
  data_at Ews (tarray tuchar (cap - (k + a))) (sublist (k + a) cap D) (offset_val (k + a) dp) *
  wv_at (wv_of k cap D) (offset_val k dp)
  |-- data_at Ews (tarray tuchar cap) (sublist 0 k D ++ N ++ sublist (k + a) cap D) dp.
Proof.
  intros Hk Ha Hka Hc HD HN FC.
  assert (HR : Zlength (N ++ sublist (k + a) cap D) = cap - k) by (rewrite Zlength_app, Zlength_sublist; lia).
  apply derives_trans with
    (data_at Ews (tarray tuchar (kp k cap)) (sublist 0 (kp k cap) D) dp *
     data_at Ews (tarray tuchar (cap - k)) (N ++ sublist (k + a) cap D) (offset_val k dp) *
     wv_at (wv_of k cap D) (offset_val k dp)).
  - rewrite (arr_split Ews (cap - k) a (N ++ sublist (k + a) cap D) (offset_val k dp)) by
      (try apply fc_rest; auto; lia).
    rewrite offset_offset_val.
    replace (sublist 0 a (N ++ sublist (k + a) cap D)) with N by list_solve.
    replace (sublist a (cap - k) (N ++ sublist (k + a) cap D)) with (sublist (k + a) cap D) by list_solve.
    replace (cap - k - a) with (cap - (k + a)) by lia. replace (a + k) with (k + a) by lia.
    cancel.
  - apply dest_close; auto; lia.
Qed.

(* next_in for a source that is a pointer or Z_NULL: [in_ptrN sp d] is d bytes into it, Z_NULL for Z_NULL *)
Lemma in_ptrN_0 sp : is_pointer_or_null sp -> in_ptrN sp 0 = sp.
Proof.
  intros P. unfold in_ptrN. destruct (eq_dec sp nullval) as [E|E]; [auto |].
  destruct sp; try contradiction; [simpl in P; subst; contradiction |]. simpl. rewrite Ptrofs.add_zero. reflexivity.
Qed.

Lemma in_ptrN_shift sp d k : is_pointer_or_null sp -> in_ptrN (in_ptrN sp d) k = in_ptrN sp (d + k).
Proof.
  intros P. unfold in_ptrN. destruct (eq_dec sp nullval) as [E|E].
  - rewrite if_true by auto. reflexivity.
  - destruct sp; try contradiction; [simpl in P; subst; contradiction |].
    rewrite if_false by (simpl; discriminate). rewrite offset_offset_val. reflexivity.
Qed.

Lemma in_ptrN_00 sp d : is_pointer_or_null sp -> in_ptrN (in_ptrN sp d) 0 = in_ptrN sp d.
Proof. intros P. rewrite in_ptrN_shift by auto. rewrite Z.add_0_r. reflexivity. Qed.

(* the source with bytes is a pointer *)
Lemma c2_src_ptr ssh sp src : 0 < Zlength src -> c2_src ssh sp src |-- !! isptr sp.
Proof.
  intros H. unfold c2_src. destruct (eq_dec sp nullval).
  - Intros. subst. rewrite Zlength_nil in H. lia.
  - entailer!. match goal with Hf : field_compatible _ _ _ |- _ => destruct Hf; auto end.
Qed.

(* the source around deflate's input object [d, d + a): the bytes before and after it (none for Z_NULL) *)
Definition c2_src_fr (ssh : share) (sp : val) (src : list Z) (d a : Z) : mpred :=
  if eq_dec sp nullval then !! (src = []) && emp
  else !! field_compatible (tarray tuchar (Zlength src)) [] sp &&
       (data_at ssh (tarray tuchar d) (sublist 0 d (map vi src)) sp *
        data_at ssh (tarray tuchar (Zlength src - (d + a))) (sublist (d + a) (Zlength src) (map vi src))
          (offset_val (d + a) sp)).

Lemma c2_src_open ssh sp src d a :
  0 <= d -> 0 <= a -> d + a <= Zlength src ->
  c2_src ssh sp src |-- in_objN ssh (sublist d (d + a) src) (in_ptrN sp d) * c2_src_fr ssh sp src d a.
Proof.
  intros Hd Ha Hl. unfold c2_src, c2_src_fr, in_objN, in_ptrN. destruct (eq_dec sp nullval) as [E|E].
  - rewrite if_true by auto. Intros. subst src. rewrite Zlength_nil in Hl.
    replace d with 0 by lia. replace a with 0 by lia. entailer!.
  - rewrite bytes_cd. assert_PROP (field_compatible (tarray tuchar (Zlength src)) [] sp) as FC by entailer!.
    assert (P : isptr sp) by (destruct FC; auto).
    rewrite if_false by (destruct sp; try contradiction; simpl; discriminate).
    rewrite (src_split ssh src sp d a FC Hd Ha Hl). entailer!.
Qed.

Lemma c2_src_close ssh sp src d a :
  0 <= d -> 0 <= a -> d + a <= Zlength src ->
  in_objN ssh (sublist d (d + a) src) (in_ptrN sp d) * c2_src_fr ssh sp src d a |-- c2_src ssh sp src.
Proof.
  intros Hd Ha Hl. unfold c2_src, c2_src_fr, in_objN, in_ptrN. destruct (eq_dec sp nullval) as [E|E].
  - rewrite if_true by auto. Intros. subst sp.
    entailer!.
  - Intros. rename H into FC. assert (P : isptr sp) by (destruct FC; auto).
    rewrite if_false by (destruct sp; try contradiction; simpl; discriminate).
    rewrite bytes_cd, (src_split ssh src sp d a FC Hd Ha Hl). cancel.
Qed.

End Arr.

Lemma rtcbw_compress2_z : ob_compress2_z_w.
Proof.
  unfold ob_compress2_z_w, Gprog_compress2_z_w, compress2_z_spec_w, c2w_pre, c2w_sep_pre, c2w_sep_post.
  start_function.
  rename H into Hdp, H0 into Hdc, H1 into Hcap, H2 into Hcl, SH into Hssh, H3 into Hsp, H4 into Hsl, H5 into Hby,
    H6 into Hlv, H7 into Hres.
  forward.
  assert_PROP (isptr dlp) as Hdlp by entailer!.
  assert (Hsl0 : 0 <= Zlength src) by apply Zlength_nonneg.
  forward_if (temp _t'1 (Val.of_bool false)).
  { assert_PROP (isptr sp) as Psp.
    { match goal with Hx : Int64.unsigned _ < Int64.unsigned _ |- _ => rewrite !Int64.unsigned_repr in Hx by rep_lia end.
      sep_apply (c2_src_ptr ssh sp src ltac:(lia)). entailer!. }
    forward.
    - entailer!.
      match goal with Hx : Int64.unsigned _ < Int64.unsigned _ |- _ => rewrite !Int64.unsigned_repr in Hx by rep_lia end.
      apply denote_tc_test_eq_split; [| auto with valid_pointer].
      apply derives_trans with (c2_src ssh sp src * TT); [cancel|]. rewrite c2_src_obj by auto.
      apply sepcon_valid_pointer1, buf_valid; auto; lia.
    - entailer!. destruct sp; try contradiction; reflexivity. }
  { forward. entailer!. }
  forward_if (temp _t'2 (Val.of_bool false)).
  { contradiction. }
  { forward. entailer!. destruct dlp; try contradiction; reflexivity. }
  forward_if (temp _t'3 (Val.of_bool false)).
  { contradiction. }
  { forward. forward_if (temp _t'3 (Val.of_bool false)).
    - forward.
      { entailer!.
        match goal with Hx : Int64.unsigned _ < Int64.unsigned _ |- _ => rewrite !Int64.unsigned_repr in Hx by rep_lia end.
        apply denote_tc_test_eq_split; [| auto with valid_pointer].
        apply derives_trans with (data_at Ews (tarray tuchar (Zlength dc)) dc dp * TT); [cancel|].
        apply sepcon_valid_pointer1, buf_valid; auto; apply writable_readable, writable_Ews. }
      forward. entailer!. destruct dp; try contradiction; reflexivity.
    - forward. entailer!.
    - entailer!. }
  forward_if.
  { contradiction. }
  forward. forward.
  sep_apply (strm_open v_stream).
  Intros.
  freeze FCOMP := (@data_at_ CCS (Share.comp Ews) t_strm v_stream).
  rewrite <- (fa__cd Ews deflate.code._zalloc v_stream), <- (fa__cd Ews deflate.code._zfree v_stream),
    <- (fa__cd Ews deflate.code._opaque v_stream).
  forward. forward. forward.
  fa_to_dcs. unfold cversion_lit. rewrite tschar_cd.
  forward_call (v_stream, level, gv ___stringlit_compress_1, Ers, [49;46;51;46;50;0], 112, Vundef, Vundef,
                Vundef, Vundef, Vundef, nullval, Vundef, Vundef, gv).
  { unfold reset_fields. cancel. }
  { split; [unfold s32_ok; rep_lia|]. split; [list_solve|]. split; [cbn; rep_lia|].
    intros a1 a2 a3 a4 a5. destruct (Hres a1 a2 a3 a4 a5) as (r & out & os & z1 & code & HI & _).
    exists (os, z1, code). exact HI. }
  Intros vret. destruct vret as [[[[[a1 a2] a3] a4] a5] [[os z1] code]]. cbn [fst snd] in *.
  match goal with H : c_deflateInit2_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _ |- _ => rename H into HI end.
  change (Znth 0 [49; 46; 51; 46; 50; 0] =? 49) with true in HI. change (112 =? 112) with true in HI.
  pose proof (c2_init_code _ _ _ _ _ _ _ _ _ _ HI) as Hcode.
  forward_if.
  { (* deflateInit failed *)
    assert (Hc : code <> Z_OK) by (intros ->; contradiction).
    pose proof (c2_init_none _ _ _ _ _ _ _ _ _ _ HI Hc) as ->.
    Intros st za zf op' dt' msgv'.
    thaw FCOMP. unfold reset_fields.
    change (@field_at_ DCS.CS Ews t_strm (DOT deflate.code._avail_in) v_stream)
      with (@field_at DCS.CS Ews t_strm (DOT deflate.code._avail_in) Vundef v_stream).
    change (@field_at_ DCS.CS Ews t_strm (DOT deflate.code._next_out) v_stream)
      with (@field_at DCS.CS Ews t_strm (DOT deflate.code._next_out) Vundef v_stream).
    change (@field_at_ DCS.CS Ews t_strm (DOT deflate.code._avail_out) v_stream)
      with (@field_at DCS.CS Ews t_strm (DOT deflate.code._avail_out) Vundef v_stream).
    sep_apply (strm_close v_stream).
    forward.
    Exists a1 a2 a3 a4 a5 code (@nil Z).
    unfold cversion_lit. rewrite tschar_cd.
    entailer!.
    - split; [exists None, z1, code; split; [exact HI | left; auto] | rewrite Zlength_nil; lia].
    - rewrite Zlength_nil, app_nil_l, sublist_same by lia. cancel. }
  (* deflateInit succeeded: the level is valid, so the destination is not empty *)
  assert (Hok : code = Z_OK) by (destruct Hcode as [E|[E|E]]; auto; subst code;
    match goal with Hx : Int.repr _ = Int.repr 0 |- _ => apply repr_inj_signed in Hx; try discriminate; rep_lia end).
  subst code. clear Hcode.
  assert (Hcap0 : 0 < cap) by (pose proof (c2_init_level _ _ _ _ _ _ _ _ _ HI); destruct Hcl; [auto | contradiction]).
  destruct (Hres a1 a2 a3 a4 a5) as (R & OUT & os' & z1' & code' & HI' & Hcases).
  rewrite HI in HI'. injection HI' as <- <- <-.
  destruct Hcases as [[Hc _] | [_ (s & E & SF & ZF & -> & Hgz & Hrun & HR)]]; [contradiction|].
  destruct (init_ok_strm _ _ _ _ _ _ _ _ _ _ _ _ _ HI) as (Hti & Hto & Had & _ & _ & Hmsg).
  Intros msgv'. change (Z_OK =? Z_OK) with true in *. unfold rfv.
  match goal with Hx : (if Z_OK =? Z_VERSION_ERROR then _ else _) |- _ => cbn in Hx; rewrite Hmsg in Hx; cbn in Hx; subst msgv' end.
  fa_to_ccs.
  rewrite <- (fa__cd Ews deflate.code._avail_in v_stream), <- (fa__cd Ews deflate.code._next_out v_stream),
    <- (fa__cd Ews deflate.code._avail_out v_stream).
  forward. forward. forward. forward.
  fa_to_dcs.
  assert_PROP (field_compatible (tarray tuchar cap) [] dp) as FCd by entailer!.
  forward_loop (EX s0 : dstate, EX z : strm, EX left : Z, EX srcleft : Z, EX out : list Z, EX msgv : val,
    PROP (c2_run src s0 z left srcleft out E OUT SF ZF; d_gzhead s0 = None;
          (z_next_in z + z_avail_in z + srcleft = Zlength src)%Z; (0 <= z_next_in z)%Z; (0 <= z_avail_in z)%Z;
          (0 <= srcleft)%Z; (Zlength out + z_avail_out z + left = cap)%Z; (0 <= z_avail_out z)%Z; (0 <= left)%Z;
          msg_ok (z_msg z) msgv)
    LOCAL (temp _left (vl left); temp _sourceLen (vl srcleft); temp _max (Vint (Int.neg (Int.repr 1)));
           lvar _stream (Tstruct _z_stream_s noattr) v_stream; gvars gv; temp _dest dp; temp _destLen dlp;
           temp _source sp)
    SEP (@data_at_ CCS (Share.comp Ews) t_strm v_stream; dstream 2 (Some s0) v_stream nullval gv;
         api_fields v_stream (in_ptrN sp (z_next_in z)) (z_avail_in z) (z_total_in z)
           (offset_val (Zlength out) dp) (z_avail_out z) (z_total_out z) msgv (z_adler z);
         strm_pad v_stream;
         data_at Ews (tarray tuchar cap) (map vi out ++ sublist (Zlength out) cap dc) dp;
         data_at Tsh tulong (vl 0) dlp;
         c2_src ssh sp src;
         cversion_lit gv; deflate_globals gv; mem_mgr gv))
  break: (EX msgv : val,
    PROP (E <> Z_OK; DeflateParams8.rc_ok E; (Zlength OUT <= cap)%Z; msg_ok (z_msg ZF) msgv)
    LOCAL (temp _err (vi E); temp _dest dp; temp _destLen dlp;
           lvar _stream (Tstruct _z_stream_s noattr) v_stream; gvars gv)
    SEP (@data_at_ CCS (Share.comp Ews) t_strm v_stream; dstream 2 (Some SF) v_stream nullval gv;
         api_fields v_stream (in_ptrN sp (z_next_in ZF)) (z_avail_in ZF) (z_total_in ZF)
           (offset_val (Zlength OUT) dp) (z_avail_out ZF) (z_total_out ZF) msgv (z_adler ZF);
         strm_pad v_stream;
         data_at Ews (tarray tuchar cap) (map vi OUT ++ sublist (Zlength OUT) cap dc) dp;
         data_at Tsh tulong (vl 0) dlp;
         c2_src ssh sp src;
         cversion_lit gv; deflate_globals gv; mem_mgr gv)).
  { (* entry *)
    Exists s (mkST src 0 0 (z_total_in z1) [] 0 (z_total_out z1) (z_adler z1) (z_msg z1)) cap (Zlength src)
      (@nil Z) nullval.
    thaw FCOMP. unfold cversion_lit. rewrite tschar_cd. unfold api_fields, reset_fields. cbn [DS.z_next_in DS.z_avail_in DS.z_total_in DS.z_avail_out DS.z_total_out DS.z_adler DS.z_msg].
    rewrite Hti, Hto, Hmsg, (in_ptrN_0 sp Hsp).
    entailer!.
    - unfold u32_ok, u64_ok. destruct Had as [-> | ->]; rep_lia.
    - rewrite Zlength_nil, app_nil_l, sublist_same by lia. cancel. }
  { (* the loop body *)
    Intros s0 z left srcleft out msgv.
    freeze FC2 := (@data_at_ CCS (Share.comp Ews) t_strm v_stream).
    unfold api_fields. Intros. fa_to_ccs.
    assert (Hao : z_avail_out z <= umax) by (unfold u32_ok in *; unfold umax; rep_lia).
    assert (Hai : z_avail_in z <= umax) by (unfold u32_ok in *; unfold umax; rep_lia).
    assert (Hmax : Int.unsigned (Int.neg (Int.repr 1)) = umax) by reflexivity.
    assert (Hk : 0 <= Zlength out) by apply Zlength_nonneg.
    forward.
    freeze FR := - (field_at _ _ (DOT deflate.code._avail_out) _ _) (field_at _ _ (DOT deflate.code._avail_in) _ _).
    forward_if (PROP () LOCAL (temp _left (vl (give_l (z_avail_out z) left)); temp _sourceLen (vl srcleft);
        temp _max (Vint (Int.neg (Int.repr 1))); lvar _stream (Tstruct _z_stream_s noattr) v_stream; gvars gv;
        temp _dest dp; temp _destLen dlp; temp _source sp)
      SEP (FRZL FR; field_at Ews t_strm (DOT deflate.code._avail_out) (vi (give_a (z_avail_out z) left)) v_stream;
           field_at Ews t_strm (DOT deflate.code._avail_in) (vi (z_avail_in z)) v_stream)).
    { assert (Hz : z_avail_out z = 0) by assumption.
      unfold give_a, give_l. rewrite Hz. cbn [Z.eqb].
      unfold MORE_COMMANDS, abbreviate. apply -> seq_assoc. apply semax_if_seq. forward_if.
      { try rewrite Hmax in *. try (rewrite Int64.unsigned_repr in * by (unfold umax; rep_lia)).
        forward. forward. forward. forward. entailer!.
        - unfold give_l. rewrite Hz. cbn [Z.eqb]. rewrite Z.min_r by (unfold umax in *; lia). rewrite Hmax. reflexivity.
        - unfold give_a. rewrite Hz. cbn [Z.eqb]. rewrite Z.min_r by (unfold umax in *; lia). unfold vi.
          rewrite <- (Int.repr_unsigned (Int.repr (-(1)))), Hmax. cancel. }
      { try rewrite Hmax in *. try (rewrite Int64.unsigned_repr in * by (unfold umax; rep_lia)).
        forward. forward. forward. forward. entailer!.
        - unfold give_l. rewrite Hz. cbn [Z.eqb]. rewrite Z.min_l by (unfold umax in *; lia).
          rewrite Int64.Z_mod_modulus_eq, Z.mod_small by rep_lia.
          rewrite Int.unsigned_repr by (unfold umax in *; rep_lia). unfold vl. rewrite Z.sub_diag. reflexivity.
        - unfold give_a. rewrite Hz. cbn [Z.eqb]. rewrite Z.min_l by (unfold umax in *; lia).
          rewrite Int64.Z_mod_modulus_eq, Z.mod_small by rep_lia. unfold vi. cancel. } }
    { assert (Hz : z_avail_out z <> 0) by (intros E0; rewrite E0 in *; contradiction).
      forward. unfold give_a, give_l. rewrite (proj2 (Z.eqb_neq _ _) Hz). entailer!. }
    forward.
    forward_if (PROP () LOCAL (temp _left (vl (give_l (z_avail_out z) left));
        temp _sourceLen (vl (give_l (z_avail_in z) srcleft));
        temp _max (Vint (Int.neg (Int.repr 1))); lvar _stream (Tstruct _z_stream_s noattr) v_stream; gvars gv;
        temp _dest dp; temp _destLen dlp; temp _source sp)
      SEP (FRZL FR; field_at Ews t_strm (DOT deflate.code._avail_out) (vi (give_a (z_avail_out z) left)) v_stream;
           field_at Ews t_strm (DOT deflate.code._avail_in) (vi (give_a (z_avail_in z) srcleft)) v_stream)).
    { assert (Hz : z_avail_in z = 0) by assumption.
      unfold MORE_COMMANDS, abbreviate. apply -> seq_assoc. apply semax_if_seq. forward_if.
      { try rewrite Hmax in *. try (rewrite Int64.unsigned_repr in * by (unfold umax; rep_lia)).
        forward. forward. forward. forward. entailer!.
        - unfold give_l. rewrite Hz. cbn [Z.eqb]. rewrite Z.min_r by (unfold umax in *; lia). rewrite Hmax. reflexivity.
        - unfold give_a. rewrite Hz. cbn [Z.eqb]. rewrite Z.min_r by (unfold umax in *; lia). unfold vi.
          rewrite <- (Int.repr_unsigned (Int.repr (-(1)))), Hmax. cancel. }
      { try rewrite Hmax in *. try (rewrite Int64.unsigned_repr in * by (unfold umax; rep_lia)).
        forward. forward. forward. forward. entailer!.
        - unfold give_l. rewrite Hz. cbn [Z.eqb]. rewrite Z.min_l by (unfold umax in *; lia).
          rewrite Int64.Z_mod_modulus_eq, Z.mod_small by rep_lia.
          rewrite Int.unsigned_repr by (unfold umax in *; rep_lia). unfold vl. rewrite Z.sub_diag. reflexivity.
        - unfold give_a. rewrite Hz. cbn [Z.eqb]. rewrite Z.min_l by (unfold umax in *; lia).
          rewrite Int64.Z_mod_modulus_eq, Z.mod_small by rep_lia. unfold vi. cancel. } }
    { assert (Hz : z_avail_in z <> 0) by (intros E0; rewrite E0 in *; contradiction).
      forward. unfold give_a, give_l. rewrite (proj2 (Z.eqb_neq _ _) Hz). entailer!. }
    destruct (give_range (z_avail_out z) left ltac:(lia) ltac:(lia)) as (Hgo1 & Hgo2 & Hgo3 & Hgo4).
    destruct (give_range (z_avail_in z) srcleft ltac:(lia) ltac:(lia)) as (Hgi1 & Hgi2 & Hgi3 & Hgi4).
    set (ao := give_a (z_avail_out z) left) in *. set (ai := give_a (z_avail_in z) srcleft) in *.
    set (l' := give_l (z_avail_out z) left) in *. set (sl' := give_l (z_avail_in z) srcleft) in *.
    set (fl := if sl' =? 0 then Z_FINISH else Z_NO_FLUSH).
    forward_if (temp _t'7 (vi fl)).
    { forward. entailer!.
      assert (Hs0 : sl' <> 0) by (intros E0; rewrite E0 in *; contradiction).
      subst fl. rewrite (proj2 (Z.eqb_neq _ _) Hs0). reflexivity. }
    { forward. entailer!.
      assert (Hs0 : sl' = 0).
      { match goal with Hx : Int64.repr _ = Int64.zero |- _ => apply repr_inj_unsigned64 in Hx; rep_lia end. }
      subst fl. rewrite Hs0. reflexivity. }
    thaw FR. fa_to_dcs.
    (* the model: this iteration's deflate call, on the whole source and on the slice offered *)
    pose proof (give_shape src z left srcleft) as HG. fold ao ai l' sl' fl in HG.
    destruct (c2_run_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ H1 HG) as (s' & z' & e & Hdf & Hgz' & Hst & Hnext).
    set (d := z_next_in z) in *.
    assert (Hdai : d + ai <= Zlength src) by lia.
    pose proof Hdf as Hsl'. apply (deflate_slice d ai) in Hsl'; [| cbn; lia ..].
    rewrite dstream_sp_eq. Intros ssp.
    rewrite (bytes_cd Ews cap).
    assert_PROP (@field_compatible DCS.CS (tarray tuchar cap) [] dp) as FCd' by entailer!.
    set (D := map vi out ++ sublist (Zlength out) cap dc).
    assert (HDl : Zlength D = cap) by (subst D; list_solve).
    sep_apply (c2_src_open ssh sp src d ai ltac:(lia) ltac:(lia) Hdai).
    sep_apply (dest_open3 (Zlength out) ao cap D dp ltac:(lia) ltac:(lia) ltac:(lia) Hcap0 HDl FCd').
    set (rest := sublist (Zlength out) (Zlength out + ao) D).
    assert (Hrl : Zlength rest = ao) by (subst rest; rewrite Zlength_sublist; lia).
    assert (Hzs : zmk (sublist d (d + ai) src) 0 ai (z_total_in z) (Zlength rest) (z_total_out z) (z_adler z) (z_msg z) =
                  zslice d ai (mkST src d ai (z_total_in z) [] ao (z_total_out z) (z_adler z) (z_msg z))).
    { unfold zmk, zslice. cbn. rewrite Hrl. f_equal. lia. }
    forward_call (Some s0, v_stream, nullval, ssp, (Ews, nullval, nullval, nullval), in_ptrN sp d, ssh,
                  sublist d (d + ai) src, 0, ai, z_total_in z, offset_val (Zlength out) dp, rest,
                  wv_of (Zlength out) cap D, z_total_out z, msgv, z_msg z, z_adler z, fl,
                  (Some s', zslice d ai z', e), gv).
    { rewrite (in_ptrN_00 sp d Hsp).
      rewrite Hrl. unfold hdr_at. rewrite H2. unfold api_fields.
      rewrite (prop_true_andp (u32_ok ai /\ _)) by (unfold u32_ok, u64_ok, umax in *; rep_lia).
      rewrite (prop_true_andp (nullval = nullval)) by auto. cancel. }
    { split; [intros Hz0; apply wv_of_ok; assert (Hz1 : ao = 0) by (rewrite <- Hrl; exact Hz0);
              destruct (Hgo4 Hz1); lia |].
      split; [subst fl; unfold s32_ok; destruct (sl' =? 0); [change Z_FINISH with 4 | change Z_NO_FLUSH with 0]; rep_lia |].
      split.
      - unfold strm_ranges, zmk. cbn. rewrite Zlength_sublist by lia. unfold u32_ok, u64_ok, umax in *.
        repeat split; try rep_lia; try constructor. apply Forall_sublist. exact Hby.
      - exists (fun f => f). split; [apply ef_ok_id |].
        unfold on_state, c_on_state. rewrite c_deflate_g_id. rewrite Hzs, Hsl'. reflexivity. }
    cbn [fst snd]. Intros msgv'.
    forward.
    unfold hdr_at. rewrite H2. Intros.
    pose proof (DeflateParams8.c_deflate_rc _ _ _ _ _ _ Hdf) as Hrc.
    destruct Hst as (Hs1 & Hs2 & Hs3 & Hs4); cbn [DS.z_avail_in DS.z_next_in DS.z_avail_out DS.z_out] in Hs1, Hs2, Hs3, Hs4.
    unfold zslice. cbn [DS.z_next_in DS.z_avail_in DS.z_total_in DS.z_out DS.z_avail_out DS.z_total_out DS.z_adler DS.z_msg].
    rewrite (in_ptrN_shift sp d _ Hsp), offset_offset_val. replace (d + (z_next_in z' - d)) with (z_next_in z') by lia.
    sep_apply (c2_src_close ssh sp src d ai ltac:(lia) ltac:(lia) Hdai).
    set (N := map vi (z_out z') ++ sublist (Zlength (z_out z')) (Zlength rest) rest).
    assert (HN : Zlength N = ao) by (subst N; list_solve).
    rewrite Hrl.
    sep_apply (dest_close3 (Zlength out) ao cap D N dp ltac:(lia) ltac:(lia) ltac:(lia) Hcap0 HDl HN FCd').
    assert (HD : sublist 0 (Zlength out) D ++ N ++ sublist (Zlength out + ao) cap D =
                 map vi (out ++ z_out z') ++ sublist (Zlength (out ++ z_out z')) cap dc).
    { subst N rest D. rewrite map_app, Zlength_app. list_solve. }
    rewrite HD. clear HD.
    rewrite <- (bytes_cd Ews cap).
    sep_apply (dstream_sp_fold' 2 (Some s') v_stream nullval ssp gv).
    forward_if.
    { (* Z_OK: the next iteration *)
      assert (He : e = Z_OK).
      { unfold DeflateParams8.rc_ok in Hrc.
        destruct Hrc as [-> | [-> | [-> | ->]]]; auto;
          match goal with Hx : Int.repr _ = Int.repr 0 |- _ => apply repr_inj_signed in Hx; try discriminate; rep_lia end. }
      destruct Hnext as [[_ Hrun'] | [Hne _]]; [| contradiction].
      forward.
      Exists s' z' l' sl' (out ++ z_out z') msgv'. thaw FC2. rewrite Zlength_app.
      entailer!. }
    { (* the end of the loop *)
      destruct Hnext as [[-> _] | [Hne (-> & -> & -> & ->)]]; [exfalso; match goal with Hx : Int.repr _ <> Int.repr _ |- _ => apply Hx; reflexivity end |].
      forward.
      Exists msgv'. thaw FC2. rewrite Zlength_app.
      entailer!. } }
  (* after the loop: *destLen, deflateEnd, the return value *)
  Intros msgv.
  freeze FC3 := (@data_at_ CCS (Share.comp Ews) t_strm v_stream).
  unfold api_fields. Intros. fa_to_ccs.
  forward.
  forward.
  { entailer!. destruct dp; try contradiction. simpl. unfold denote_tc_samebase. simpl. entailer!. }
  rewrite (sub_pp_val0 cap dp (Zlength OUT) FCd ltac:(pose proof (Zlength_nonneg OUT); lia)).
  fa_to_dcs.
  destruct (c_deflateEnd SF ZF) as [rr|] eqn:Hend; [| unfold c_deflateEnd in Hend; destruct (bad_state SF); discriminate].
  sep_apply (Api_toend.dstream_to_end (Some SF) v_stream nullval gv).
  forward_call (Some SF, v_stream, in_ptrN sp (z_next_in ZF), ZF, rr, gv).
  sep_apply (end_fields (fst (fst rr)) SF v_stream gv).
  Intros st za zf op dt.
  thaw FC3.
  sep_apply (strm_close v_stream).
  apply semax_if_seq. forward_if.
  { forward. forward.
    assert (HE1 : E = Z_STREAM_END).
    { unfold DeflateParams8.rc_ok in *.
      match goal with Hx : E = _ \/ _ |- _ => destruct Hx as [-> | [-> | [-> | ->]]] end; auto;
        match goal with Hx : Int.repr _ = Int.repr 1 |- _ => apply repr_inj_signed in Hx; try discriminate; rep_lia end. }
    Exists a1 a2 a3 a4 a5 Z_OK OUT.
    entailer!.
    exists (Some s), z1, Z_OK. split; [exact HI |]. right. split; [reflexivity |].
    exists s, Z_STREAM_END, SF, ZF. split; [reflexivity |]. split; [exact Hgz |]. split; [exact Hrun | reflexivity]. }
  { forward. forward.
    assert (HE1 : (E =? Z_STREAM_END) = false).
    { apply Z.eqb_neq. intros ->. match goal with Hx : Int.repr _ <> Int.repr 1 |- _ => apply Hx; reflexivity end. }
    Exists a1 a2 a3 a4 a5 E OUT.
    entailer!.
    exists (Some s), z1, Z_OK. split; [exact HI |]. right. split; [reflexivity |].
    exists s, E, SF, ZF. split; [reflexivity |]. split; [exact Hgz |]. split; [exact Hrun |]. rewrite HE1. reflexivity. }
Qed.

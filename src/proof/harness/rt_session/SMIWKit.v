(* Law rt_session (harness/rt_session.c), main's inflate loop without a header (SMLoopIW.v, SMKit.loopI_W_stmt):
   the assertions of the loop's body, its cut into parts, and the memory lemmas the parts share.

   The loop is rt_stream_trailing's (input object [iobj src ip]: the stream O, then any bytes; inflate() with
   SpecW's specification on an istreamA) with a fourth documented code, Z_NEED_DICT, and its branch: main checks
   that a dictionary was set with the zlib wrapper and that it was not asked for before, sets asked and calls
   inflateSetDictionary with dict_copy (SpecW.inflateSetDictionary_specW), which returns Z_OK (Z_MEM_ERROR ends the
   run).  The invariant is SIFacts' [P] between the calls (SMKit.il_ok); right after a call:
   - Z_OK, Z_BUF_ERROR: P at the new state (si_call);
   - Z_NEED_DICT: PN at the new state, asked = false, and the session is a zlib one with a dictionary;
     inflateSetDictionary then gives P with asked = true (si_setdict);
   - Z_STREAM_END: all of O consumed, all the data produced, asked iff the session is a zlib one with a
     dictionary.
   [cfacts] states this for a code r and a state l; [il_geo] are the positions of next_in and next_out, true
   whatever the code.  No header is attached (with_head u = false, SIFacts.si_shape, si_nshape): head_opt is emp.

   The memory lemmas are rt_stream's (ULoopIKit.v), restated at the law's compspecs SCS.CS and for SMKit's
   objects. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Zlib.proof.deflate.Api_toend.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.SpecW.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.rt_stream.ULoopIPos.
Require Import Zlib.proof.harness.rt_session.SCS.
Require Import Zlib.proof.harness.rt_session.SDFacts.
Require Import Zlib.proof.harness.rt_session.SIFacts.
Require Import Zlib.proof.harness.rt_session.SMainStmt.
Require Import Zlib.proof.harness.rt_session.SMKit.
Require Import Zlib.harness.rt_session.code.
#[local] Existing Instance SCS.CS.
Local Open Scope logic.

(** ** One inflate() call in the model *)

(* the stream main hands to inflate(): z with next_in, avail_in, next_out, avail_out set *)
Definition zoff (z : zfields) (ni : val) (ai : Z) (no : val) (ao : Z) : zfields :=
  ZF ni ai (zf_tin z) no ao (zf_tout z) (zf_msg z) (zf_dt z) (zf_adler z) (zf_res z).

(* the input object: src, offered from pos on; the output object: out written at the start of out *)
Definition ib_w (src : list Z) (ip : val) (pos : Z) : inbuf := InBuf Ews ip pos (Zlength src) (map vi src).
Definition ob_w (u : setup) (out : list Z) : outbuf :=
  OutBuf Ews (su_op u) (Zlength out) (Zlength (su_data u)) (cbytes (Zlength (su_data u)) out).

(* the position main records before the call: next_in at pos in the input, avail_in ai, next_out after the
   output out, avail_out ao, and the totals of z *)
Definition opos_w (ip : val) (u : setup) (pos : Z) (out : list Z) (z : zfields) (ai ao : Z) : LS.posz :=
  LS.mk_posz (offset_val pos ip) ai (zf_tin z) (offset_val (Zlength out) (su_op u)) ao (zf_tout z).

(* accounted(&decompressor, &at) after a call from the position [a]: it returns 1, and the two sums it compares
   are pointers into (or one past) the input object and the output object *)
Definition acc_ok_w (src : list Z) (ip : val) (u : setup) (l : ils) (a : LS.posz) : Prop :=
  LS.accounted_b (zpos (il_z l)) a = true /\ isptr (LS.pz_next_in a) /\ isptr (LS.pz_next_out a) /\
  exists ki ko, 0 <= ki <= Zlength src /\ 0 <= ko <= Zlength (su_data u) /\
    offset_val (LS.pz_avail_in a) (LS.pz_next_in a) = offset_val ki ip /\
    offset_val (LS.pz_avail_out a) (LS.pz_next_out a) = offset_val ko (su_op u).

(* the positions of next_in (pos bytes into the input) and next_out (after the output out, a prefix of the
   data), whatever the call returned *)
Definition il_geo (u : setup) (src : list Z) (ip : val) (l : ils) : Prop :=
  0 <= il_pos l <= Zlength src /\ (exists rest, su_data u = il_out l ++ rest) /\
  zf_ni (il_z l) = offset_val (il_pos l) ip /\
  zf_no (il_z l) = offset_val (Zlength (il_out l)) (su_op u).

(* what holds after a call that returned r (see the first comment) *)
Definition cfacts (P : ses_iinv) (PN : ses_ninv) (u : setup) (O src : list Z) (ip : val) (r : Z) (l : ils)
    : Prop :=
  il_geo u src ip l /\
  (r = Z_OK \/ r = Z_BUF_ERROR ->
     P (scase_of u) (su_data u) O src (il_pos l) (il_out l) (il_asked l) (il_L l) (zf_tout (il_z l)) /\
     swfW (l_s (il_L l))) /\
  (r = Z_NEED_DICT ->
     PN (scase_of u) (su_data u) O src (il_pos l) (il_out l) (il_L l) (zf_tout (il_z l)) /\
     il_asked l = false /\ sk_zdict (scase_of u)) /\
  (r = Z_STREAM_END ->
     il_out l = su_data u /\ il_pos l = Zlength O /\ (il_asked l = true <-> sk_zdict (scase_of u))).

(** ** The assertions of the loop's body *)
Section Assertions.
Context (gv : globals) (vh vg vc va vd : val).

(* the locals of the loop: the code (when known), asked, and those of II_W *)
Definition iw_locals (u : setup) (O src : list Z) (ip : val) (asked : bool) : list localdef :=
  temp _asked (vi (Z.b2z asked)) ::
  temp _compressed_len (vl (Zlength O)) :: temp _after (vl (Zlength src - Zlength O)) ::
  temp _input ip :: c_locals u ++ d_locals u (rts_iw (su_wbits u)) ++ lvs gv vh vg vc va vd.

(* the facts of II_W that do not depend on the state *)
Definition iw_props (u : setup) (O src : list Z) (ip : val) : list Prop :=
  [su_ok u; with_head u = false; sc_ok (scase_of u) (su_data u) O; Zlength O <= su_cap u; rbytes O;
   src_ok O src; isptr ip].

(* the memory of II_W but the decompressor, out and at *)
Definition iw_rest (u : setup) (O : list Z) (c : cst) (src : list Z) (ip : val) : list mpred :=
  [iobj src ip; hobj vh u; graw vg u; dictobj u; dcopy u].

(* after the call and its Z_MEM_ERROR test: inflate() returned r, one of the four documented codes, with the
   facts [cfacts], and at holds the position [a] recorded before the call: accounted holds of it, and offered
   neither input nor output space, the call did not return Z_OK and the stream is at [a] *)
Definition ICr_w (P : ses_iinv) (PN : ses_ninv) (u : setup) (O : list Z) (c : cst) (src : list Z) (ip : val)
    (r : Z) (l : ils) (a : LS.posz) : environ -> mpred :=
  PROPx (iw_props u O src ip ++
         [r = Z_OK \/ r = Z_BUF_ERROR \/ r = Z_STREAM_END \/ r = Z_NEED_DICT;
          cfacts P PN u O src ip r l;
          LS.posz_ok a;
          LS.pz_avail_in a = 0 -> LS.pz_avail_out a = 0 -> r <> Z_OK /\ zpos (il_z l) = a;
          acc_ok_w src ip u l a])
  (LOCALx (temp _code (vi r) :: iw_locals u O src ip (il_asked l))
  (SEPx ([istreamA gv Tsh vd (il_z l) Vundef (Some (il_L l)); head_opt (Some (il_L l));
          cstream gv vc (ghp vh u) c; mem_mgr gv; zfuncs gv; Rm gv; dobj u; cobj u O; oobj u (il_out l);
          data_at Tsh t_p (LS.pos_of a) va] ++ iw_rest u O c src ip))).

(* after the three tests (codes, accounted, a call offered nothing): at's contents no longer needed *)
Definition ICd_w (P : ses_iinv) (PN : ses_ninv) (u : setup) (O : list Z) (c : cst) (src : list Z) (ip : val)
    (r : Z) (l : ils) : environ -> mpred :=
  PROPx (iw_props u O src ip ++
         [r = Z_OK \/ r = Z_BUF_ERROR \/ r = Z_STREAM_END \/ r = Z_NEED_DICT;
          cfacts P PN u O src ip r l])
  (LOCALx (temp _code (vi r) :: iw_locals u O src ip (il_asked l))
  (SEPx ([istreamA gv Tsh vd (il_z l) Vundef (Some (il_L l)); head_opt (Some (il_L l));
          cstream gv vc (ghp vh u) c; mem_mgr gv; zfuncs gv; Rm gv; dobj u; cobj u O; oobj u (il_out l);
          data_at_ Tsh t_p va] ++ iw_rest u O c src ip))).

(* at the loop's test (after the Z_NEED_DICT branch): code is Z_OK, Z_BUF_ERROR or Z_STREAM_END *)
Definition ICe_w (P : ses_iinv) (PN : ses_ninv) (u : setup) (O : list Z) (c : cst) (src : list Z) (ip : val)
    (r : Z) (l : ils) : environ -> mpred :=
  PROPx (iw_props u O src ip ++
         [r = Z_OK \/ r = Z_BUF_ERROR \/ r = Z_STREAM_END;
          cfacts P PN u O src ip r l])
  (LOCALx (temp _code (vi r) :: iw_locals u O src ip (il_asked l))
  (SEPx ([istreamA gv Tsh vd (il_z l) Vundef (Some (il_L l)); head_opt (Some (il_L l));
          cstream gv vc (ghp vh u) c; mem_mgr gv; zfuncs gv; Rm gv; dobj u; cobj u O; oobj u (il_out l);
          data_at_ Tsh t_p va] ++ iw_rest u O c src ip))).

Definition IC_w (P : ses_iinv) (PN : ses_ninv) (u : setup) (O : list Z) (c : cst) (src : list Z) (ip : val)
    : environ -> mpred :=
  EX r : Z, EX l : ils, ICe_w P PN u O c src ip r l.

(* the loop's exit *)
Definition IEx_w (u : setup) (O : list Z) (c : cst) (src : list Z) (ip : val) : environ -> mpred :=
  EX z : zfields, EX L : live, IE_W gv vh vg vc va vd u O c src ip z L.

(* the postcondition of the loop's body: IC_w at the test, IE_W at the break, a return to main's
   postcondition *)
Definition RI_w (P : ses_iinv) (PN : ses_ninv) (u : setup) (O : list Z) (c : cst) (src : list Z) (ip : val)
    : ret_assert :=
  loop1_ret_assert (IC_w P PN u O c src ip)
    (overridePost (IEx_w u O c src ip) (overridePost (IEx_w u O c src ip) POST_s)).

(* the decompressor's struct while main offers the buffers: next_in at pos in the input, next_out after the
   output out, avail_in ai, avail_out ao *)
Definition oS_w (ip : val) (u : setup) (pos : Z) (out : list Z) (z : zfields) (L : live) (ai ao : val)
    : reptype t_z :=
  (offset_val pos ip, (ai, (vl (zf_tin z), (offset_val (Zlength out) (su_op u), (ao, (vl (zf_tout z),
   (msg_val gv (zf_msg z), (l_sp L, (gv Zlib.inflate.code._zcalloc, (gv Zlib.inflate.code._zcfree, (nullval,
   (vi (zf_dt z), (adler_v (raw_live (Some L)) z Vundef, zf_res z))))))))))))).

(* the state between the stores into avail_in and avail_out and the call, with the facts Q; [A] is the memory
   of at (any bytes before position_of, the recorded position after it) *)
Definition OI_w (Q : list Prop) (u : setup) (O : list Z) (c : cst) (src : list Z) (ip : val)
    (pos : Z) (out : list Z) (asked : bool) (z : zfields) (L : live) (ai ao : val) (A : mpred)
    : environ -> mpred :=
  PROPx Q
  (LOCALx (iw_locals u O src ip asked)
  (SEPx ([data_at Tsh t_z (oS_w ip u pos out z L ai ao) vd; state_mem gv vd L; head_opt (Some L);
          cstream gv vc (ghp vh u) c; mem_mgr gv; zfuncs gv; Rm gv; dobj u; cobj u O; oobj u out; A]
         ++ iw_rest u O c src ip))).

End Assertions.

(** ** The loop's body cut into its parts *)

(* the body: offer avail_in (upto the input bytes left), offer avail_out (upto the room left),
   position_of(&decompressor, &at), the inflate() call with any flush, its Z_MEM_ERROR test, the test of the
   documented codes, the test of accounted, the test of a call offered neither input nor output space, and the
   Z_NEED_DICT branch *)
Definition bodyI_w : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [loopI] in
        (match loopI with Sloop b _ => b | s => s end) in exact x).
Definition incrI_w : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [loopI] in
        (match loopI with Sloop _ i => i | s => s end) in exact x).
Definition offerIn_w : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [bodyI_w first] in (first bodyI_w) in exact x).
Definition offerOut_w : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [bodyI_w first suf] in (first (suf 1 bodyI_w)) in exact x).
Definition posI_w : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [bodyI_w first suf] in (first (suf 2 bodyI_w)) in exact x).
Definition callI_w : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [bodyI_w first suf] in (first (suf 3 bodyI_w)) in exact x).
Definition memI_w : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [bodyI_w first suf] in (first (suf 4 bodyI_w)) in exact x).
Definition codesI_w : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [bodyI_w first suf] in (first (suf 5 bodyI_w)) in exact x).
Definition accI_w : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [bodyI_w first suf] in (first (suf 6 bodyI_w)) in exact x).
Definition idleI_w : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [bodyI_w first suf] in (first (suf 7 bodyI_w)) in exact x).
Definition dictI_w : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [bodyI_w suf] in (suf 8 bodyI_w) in exact x).

Lemma loopI_w_parts :
  loopI = Sloop (Ssequence offerIn_w (Ssequence offerOut_w (Ssequence posI_w (Ssequence callI_w
            (Ssequence memI_w (Ssequence codesI_w (Ssequence accI_w (Ssequence idleI_w dictI_w)))))))) incrI_w.
Proof. reflexivity. Qed.

(** ** Memory lemmas (rt_stream's ULoopIKit.v at the law's compspecs) *)

Lemma offset_offset (p : val) (i j : Z) : offset_val j (offset_val i p) = offset_val (i + j) p.
Proof. rewrite offset_offset_val. reflexivity. Qed.

Lemma ptr_eqb_refl (p : val) : LS.ptr_eqb p p = true.
Proof. unfold LS.ptr_eqb. destruct (Val.eq p p); [reflexivity | congruence]. Qed.

Lemma cbytes_len n l : Zlength l <= n -> Zlength (cbytes n l) = n.
Proof. intros H. unfold cbytes. rewrite Zlength_app, Zlength_map, Zlength_Zrepeat; lia. Qed.

Ltac cs_tac CC := apply equal_f; apply (@data_at_change_composite _ _ CC); [apply JMeq_refl | reflexivity].

Lemma bytes_i sh n (v : list val) q :
  @data_at Zlib.units.Inflate.CS sh (tarray tuchar n) v q = data_at sh (tarray tuchar n) v q.
Proof. cs_tac CC_inflate. Qed.
Lemma tok_i sh n q :
  @malloc_token Zlib.units.Inflate.CS sh (tarray tuchar n) q = malloc_token sh (tarray tuchar n) q.
Proof. apply equal_f; apply (@malloc_token_change_composite _ _ CC_inflate). reflexivity. Qed.
Lemma strm_cs sh (v : reptype t_z) q :
  @data_at Zlib.units.Inflate.CS sh t_z v q = data_at sh t_z v q.
Proof. cs_tac CC_inflate. Qed.

(* the decompressor's struct z_stream as main reads and writes it: istreamA's struct at the law's compspecs,
   and the memory behind strm->state *)
Definition istrm_tup (gv : globals) (z : zfields) (adv sp : val) : reptype t_z :=
  (zf_ni z, (vi (zf_ai z), (vl (zf_tin z), (zf_no z, (vi (zf_ao z), (vl (zf_tout z), (msg_val gv (zf_msg z),
   (sp, (gv Zlib.inflate.code._zcalloc, (gv Zlib.inflate.code._zcfree, (nullval, (vi (zf_dt z),
   (adv, zf_res z))))))))))))).

Lemma istreamA_unfold gv shs vs z av L :
  istreamA gv shs vs z av (Some L) =
  (!! (zf_ok z /\ writable_share shs /\ live_ok L) &&
   (data_at shs t_z (istrm_tup gv z (adler_v (raw_live (Some L)) z av) (l_sp L)) vs * state_mem gv vs L)).
Proof.
  unfold istreamA, zstrm_atA. change Zlib.proof.inflate.Rep.t_strm with t_z.
  rewrite strm_cs.
  apply pred_ext; entailer!.
Qed.

Lemma istreamA_opt_ptr gv shs (vs : val) z av st :
  isptr vs -> istreamA_opt gv shs vs z av st = istreamA gv shs vs z av st.
Proof. intros Pv. unfold istreamA_opt. destruct (eq_dec vs nullval); [subst; contradiction | reflexivity]. Qed.

Lemma is_live_ptr (vs : val) st : isptr vs -> is_live vs st = st.
Proof. intros Pv. unfold is_live. destruct (eq_dec vs nullval); [subst; contradiction | reflexivity]. Qed.

(* the struct after main's stores into avail_in and avail_out: the stream inflate() takes *)
Lemma offer_fold gv vs z L ni ai no ao :
  isptr vs -> zf_ok z -> live_ok L -> 0 <= ai <= Int.max_unsigned -> 0 <= ao <= Int.max_unsigned ->
  data_at Tsh t_z
    (ni, (vi ai, (vl (zf_tin z), (no, (vi ao, (vl (zf_tout z), (msg_val gv (zf_msg z), (l_sp L,
     (gv Zlib.inflate.code._zcalloc, (gv Zlib.inflate.code._zcfree, (nullval, (vi (zf_dt z),
     (adler_v (raw_live (Some L)) z Vundef, zf_res z))))))))))))) vs * state_mem gv vs L
  |-- istreamA_opt gv Tsh vs (zoff z ni ai no ao) Vundef (Some L).
Proof.
  intros Pv Zo Lo Hai Hao.
  rewrite istreamA_opt_ptr by auto. rewrite istreamA_unfold.
  unfold istrm_tup, zoff, adler_v; simpl.
  apply andp_right; [ | apply derives_refl].
  apply prop_right. unfold zf_ok in *; simpl in *. split; [ | split; [apply writable_share_top | auto]].
  intuition.
Qed.

(* at a return: the decompressor's struct back to the stack frame *)
Lemma a_frame_opt gv shs vs z av st : isptr vs ->
  istreamA_opt gv shs vs z av st |-- data_at_ shs t_z vs * TT.
Proof.
  intros Pv. rewrite istreamA_opt_ptr by auto. unfold istreamA, zstrm_atA.
  change Zlib.proof.inflate.Rep.t_strm with t_z.
  destruct st as [L|]; rewrite strm_cs; Intros.
  - apply sepcon_derives; [apply data_at_data_at_ | apply TT_right].
  - rewrite <- (sepcon_emp (data_at _ _ _ _)). apply sepcon_derives; [apply data_at_data_at_ | apply TT_right].
Qed.

(* at a return: the compressor's struct, head and got back to the stack frame *)
Lemma cstream_frame gv vc g c : cstream gv vc g c |-- data_at_ Tsh t_z vc * TT.
Proof.
  unfold cstream, srest.
  sep_apply (BoundKit.dstream_data_at_ (Some (cs_s c)) vc g gv (cs_ni c) (cs_ain c) (cs_tin c) (cs_no c)
               (cs_aout c) (cs_tout c) (cs_msgv c) (cs_adler c) Zlib.proof.deflate.Api_toend.dstream_to_end).
  rewrite (@data_at__change_composite Zlib.proof.deflate.DCS.CS SCS.CS CC_dcs Ews Zlib.proof.deflate.Rep.t_strm)
    by reflexivity.
  rewrite (BoundKit.data_at__Tsh_split t_z vc). cancel.
Qed.

Lemma hobj_frame vh u : hobj vh u |-- data_at_ Tsh t_g vh * TT.
Proof. unfold hobj. sep_apply (data_at_data_at_ Tsh t_g (hvals u) vh). cancel. Qed.

Lemma graw_frame vg u : graw vg u |-- data_at_ Tsh t_g vg * TT.
Proof. unfold graw. sep_apply (data_at_data_at_ Tsh t_g (gval u) vg). cancel. Qed.

(* after the call: out ++ ow written *)
Lemma cbytes_after n out ow : Zlength out + Zlength ow <= n ->
  sublist 0 (Zlength out) (cbytes n out) ++ byte_vals ow ++
    sublist (Zlength out + Zlength ow) n (cbytes n out) = cbytes n (out ++ ow).
Proof.
  intros H. pose proof (Zlength_nonneg out). pose proof (Zlength_nonneg ow).
  unfold cbytes, byte_vals.
  rewrite sublist_app1 by (rewrite ?Zlength_map; lia).
  rewrite sublist_same by (rewrite ?Zlength_map; lia).
  rewrite sublist_app2 by (rewrite ?Zlength_map; lia). rewrite Zlength_map.
  rewrite map_app, <- app_assoc. f_equal. f_equal. rewrite Zlength_app.
  unfold Zrepeat. rewrite sublist_repeat by (try rewrite Zlength_repeat; lia).
  f_equal. f_equal. lia.
Qed.

(* the objects input and out as inflate()'s buffers, and back *)
Lemma bufs_pre_w vs L u src ip pos out :
  isptr vs -> Zlength out <= Zlength (su_data u) ->
  iobj src ip * oobj u out
  |-- bufs_opt (is_live vs (Some L)) (ib_w src ip pos) (Some (ob_w u out)) [] true true.
Proof.
  intros Pv Hn. rewrite is_live_ptr by auto.
  unfold bufs_opt, in_rep, out_opt, out_rep, in_tok, out_tok, ib_w, ob_w, iobj, oobj.
  rewrite (cbytes_after _ out []) by (rewrite Zlength_nil; lia). rewrite app_nil_r.
  rewrite !bytes_i, !tok_i. cancel.
Qed.

Lemma bufs_post_w vs L u src ip pos out ow :
  isptr vs -> Zlength out + Zlength ow <= Zlength (su_data u) ->
  bufs_opt (is_live vs (Some L)) (ib_w src ip pos) (Some (ob_w u out)) ow true true
  |-- iobj src ip * oobj u (out ++ ow).
Proof.
  intros Pv Hn. rewrite is_live_ptr by auto.
  unfold bufs_opt, in_rep, out_opt, out_rep, in_tok, out_tok, ib_w, ob_w, iobj, oobj.
  rewrite (cbytes_after _ out ow) by lia.
  rewrite !bytes_i, !tok_i. cancel.
Qed.

Lemma in_ok_w O src ip pos take :
  src_ok O src -> isptr ip -> 0 <= pos -> 0 <= take -> pos + take <= Zlength src ->
  in_ok (ib_w src ip pos) (sublist pos (pos + take) src).
Proof.
  intros (Hs & _ & Bs) Pip Hp Ht Hpt.
  unfold in_ok, ib_w.
  assert (Hl : Zlength (sublist pos (pos + take) src) = take) by (rewrite Zlength_sublist; lia).
  rewrite Hl. pose proof (Zlength_nonneg src).
  split; [auto | ]. split; [auto | ]. split; [lia | ]. split; [lia | ].
  split; [rewrite Zlength_map; reflexivity | ]. split; [unfold max_size in *; rep_lia | ]. split.
  - unfold byte_vals. rewrite sublist_map. reflexivity.
  - apply Forall_sublist. eapply Forall_impl; [ | exact Bs]. simpl. intros; rep_lia.
Qed.

Lemma out_ok_w u out ao :
  su_ok u -> 0 <= ao -> Zlength out + ao <= Zlength (su_data u) -> out_ok (ob_w u out) ao.
Proof.
  intros SU Ha Hao. destruct SU as (DK & _ & _ & _ & _ & _ & _ & Pop & _).
  pose proof DK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hn & _).
  unfold out_ok, ob_w. pose proof (Zlength_nonneg out).
  split; [apply writable_Ews | ]. unfold max_size in *. repeat split; auto; try rep_lia. apply cbytes_len; lia.
Qed.

(* m - (size_t) (p + k - p), as the harness computes the bytes left *)
Lemma ptr_sub (p : val) k m : isptr p -> 0 <= k <= m -> m <= Ptrofs.max_unsigned ->
  force_val (sem_sub_default tulong tulong (Vlong (Int64.repr m)) (force_val (sem_sub_pp tuchar (offset_val k p) p)))
  = Vlong (Int64.repr (m - k)).
Proof.
  intros Pp Hk Hm. destruct p; try contradiction. simpl.
  unfold sem_sub_pp, sem_sub_default. simpl. destruct (eq_block b b); [ | congruence]. simpl.
  rewrite Ptrofs.sub_add_l, Ptrofs.sub_idem, Ptrofs.add_zero_l.
  change (Ptrofs.repr 1) with Ptrofs.one. rewrite Ptrofs.divs_one by (cbv; congruence).
  unfold Vptrofs. simpl. f_equal. unfold Ptrofs.to_int64. rewrite Ptrofs.unsigned_repr by rep_lia.
  unfold Int64.sub. rewrite !Int64.unsigned_repr by rep_lia. reflexivity.
Qed.

Lemma sameblock_off (p : val) k : isptr p -> is_true (sameblock (offset_val k p) p).
Proof. intros Pp. destruct p; try contradiction. simpl. destruct (peq b b); [reflexivity | congruence]. Qed.

(* the struct as main offered the buffers, at laws_session's compspecs *)
Lemma oS_w_session gv ip u pos out z L ai ao vd :
  data_at Tsh t_z (oS_w gv ip u pos out z L (vi ai) (vi ao)) vd =
  @data_at LS.CS_session Tsh t_zs
    (LS.zs_of (opos_w ip u pos out z ai ao) (zrest gv z (adler_v (raw_live (Some L)) z Vundef) (l_sp L))) vd.
Proof. symmetry. cs_tac CC_session. Qed.

Lemma at_cs (va : val) : @data_at_ SCS.CS Tsh t_p va = @data_at_ LS.CS_session Tsh LS.t_pos va.
Proof. symmetry. apply equal_f. apply (@data_at__change_composite _ _ CC_session). reflexivity. Qed.

Lemma at_pos_cs (a : LS.posz) (va : val) :
  @data_at SCS.CS Tsh t_p (LS.pos_of a) va = @data_at LS.CS_session Tsh LS.t_pos (LS.pos_of a) va.
Proof. symmetry. cs_tac CC_session. Qed.

(* the position main records is well typed *)
Lemma opos_w_ok ip u pos out z ai ao :
  isptr ip -> su_ok u -> zf_ok z -> 0 <= ai <= Int.max_unsigned -> 0 <= ao <= Int.max_unsigned ->
  LS.posz_ok (opos_w ip u pos out z ai ao).
Proof.
  intros Pip SU Zo Hi Ho. destruct SU as (_ & _ & _ & _ & _ & _ & _ & Pop & _).
  unfold LS.posz_ok, opos_w, zf_ok in *; simpl.
  destruct ip; try contradiction; destruct (su_op u); try contradiction. simpl. intuition.
Qed.

(* the bytes of a malloc'ed object of n bytes: p + k (0 <= k <= n) is weakly valid *)
Lemma obj_wv (n k : Z) (v : list val) (p : val) : 0 <= k <= n ->
  malloc_token Ews (tarray tuchar n) p * data_at Ews (tarray tuchar n) v p |-- weak_valid_pointer (offset_val k p).
Proof.
  intros Hk. assert_PROP (isptr p) as Pp by entailer!.
  destruct (Z.eq_dec n 0) as [E | E].
  - subst n. replace k with 0 by lia.
    replace (offset_val 0 p) with p by (destruct p; try contradiction; simpl; rewrite Ptrofs.add_zero; reflexivity).
    apply sepcon_weak_valid_pointer1. eapply derives_trans; [apply malloc_token_valid_pointer | apply valid_pointer_weak]. simpl; lia.
  - apply sepcon_weak_valid_pointer2. sep_apply data_at_memory_block. simpl sizeof.
    apply memory_block_weak_valid_pointer; [rewrite Z.max_r by lia; lia | rewrite Z.max_r by lia; lia | ].
    apply readable_nonidentity, writable_readable, writable_Ews.
Qed.

(* a pointer compared with itself: defined when it is weakly valid *)
Section TestEq.
Local Transparent denote_tc_test_eq.
Lemma test_eq_self (p : val) : isptr p -> weak_valid_pointer p |-- denote_tc_test_eq p p.
Proof.
  intros Pp. destruct p; try contradiction. unfold denote_tc_test_eq, test_eq_ptrs. cbv [Archi.ptr64]. simpl.
  destruct (peq b b) as [E|NE]; [|congruence]. simpl proj_sumbool. cbv iota.
  apply andp_right; apply derives_refl.
Qed.
End TestEq.

(* the comparisons of unmoved and accounted: pointers into (or one past) the input and output objects, each
   compared with itself *)
Lemma objs_cmp_w (u : setup) (src out : list Z) (ip : val) (ki ko : Z) :
  isptr ip -> isptr (su_op u) -> 0 <= ki <= Zlength src -> 0 <= ko <= Zlength (su_data u) ->
  oobj u out * iobj src ip |--
  denote_tc_test_eq (offset_val ki ip) (offset_val ki ip) &&
  denote_tc_test_eq (offset_val ko (su_op u)) (offset_val ko (su_op u)).
Proof.
  intros Pi Po Hi Ho.
  unfold iobj, oobj.
  apply andp_right; (eapply derives_trans; [ | apply test_eq_self; rewrite isptr_offset_val; assumption]).
  - apply sepcon_weak_valid_pointer2. apply obj_wv. lia.
  - apply sepcon_weak_valid_pointer1. apply obj_wv. lia.
Qed.

(* accounted's comparisons after a call: [acc_ok_w] *)
Lemma acc_cmp_w (u : setup) (src out : list Z) (ip : val) l a :
  isptr ip -> isptr (su_op u) -> acc_ok_w src ip u l a ->
  oobj u out * iobj src ip |-- LS.accounted_cmp (zpos (il_z l)) a.
Proof.
  intros Pi Po (Hb & _ & _ & ki & ko & Hki & Hko & Ei & Eo).
  unfold LS.accounted_b in Hb. rewrite !andb_true_iff in Hb.
  destruct Hb as ((_ & Hbi) & (_ & Hbo)).
  unfold LS.ptr_eqb in Hbi, Hbo.
  destruct (Val.eq _ _) as [Ei' | ]; [ | discriminate]. destruct (Val.eq _ _) as [Eo' | ]; [ | discriminate].
  unfold LS.accounted_cmp. rewrite Ei', Eo', Ei, Eo.
  apply objs_cmp_w; auto.
Qed.

(** ** The session without a header *)

(* without a header no gz_header is attached: head_opt is emp for the states of P and PN *)
Lemma sgh_none u : with_head u = false -> sc_gh (scase_of u) = None.
Proof. intros H. unfold scase_of, sgh. simpl. rewrite H. reflexivity. Qed.

Lemma head_opt_emp L : i_head (l_s L) = false -> head_opt (Some L) = emp.
Proof. intros H. unfold head_opt, head_mem. rewrite H. reflexivity. Qed.

(* deflateInit2 accepted the parameters: windowBits is not 0 *)
Lemma wbits_nz u : su_ok u -> su_wbits u <> 0.
Proof.
  intros SU E. destruct SU as (DK & _). destruct DK as (_ & _ & _ & _ & Hp & _).
  rewrite E in Hp. unfold rparams_ok, rwb_of in Hp. rewrite !andb_true_iff in Hp.
  destruct Hp as [[[[[[[_ H8] _] _] _] _] _] _]. simpl in H8. discriminate H8.
Qed.

(* the zlib wrapper with a dictionary is exactly the case main's flag asked records *)
Lemma sk_zdict_iff u : su_ok u ->
  (sk_zdict (scase_of u) <-> (with_dict u && (0 <? su_wbits u))%bool = true).
Proof.
  intros SU. pose proof (wbits_nz u SU) as Hnz. destruct SU as (DK & _).
  pose proof DK as (_ & _ & _ & _ & _ & _ & Hd & _).
  unfold sk_zdict, scase_of, sc_wrap, sdict, rwrap_of; simpl.
  destruct (with_dict u) eqn:Ew.
  - unfold with_dict in Ew. apply andb_true_iff in Ew as (Ew & _). apply Z.leb_le in Ew.
    assert (Hne : su_dict u <> []) by (intro E; rewrite E, Zlength_nil in Hd; lia).
    simpl. destruct (Z.ltb_spec 0 (su_wbits u)); destruct (Z.ltb_spec (su_wbits u) 0); try lia;
      destruct (Z.gtb_spec (su_wbits u) 15); try lia; intuition (try discriminate; try lia).
  - simpl. split; [intros (H & _); contradiction | discriminate].
Qed.

(* at Z_STREAM_END: asked has the value main checks *)
Lemma asked_end u (asked : bool) : su_ok u ->
  (asked = true <-> sk_zdict (scase_of u)) -> asked = (with_dict u && (0 <? su_wbits u))%bool.
Proof.
  intros SU H. rewrite (sk_zdict_iff u SU) in H.
  destruct asked, ((with_dict u && (0 <? su_wbits u))%bool); intuition.
Qed.

(* at Z_NEED_DICT: with_dict and window_bits > 0 (main's window_bits is rts_iw (su_wbits u)) *)
Lemma zdict_flags u : su_ok u -> sk_zdict (scase_of u) ->
  with_dict u = true /\ 0 < rts_iw (su_wbits u).
Proof.
  intros SU H. apply (sk_zdict_iff u SU) in H. apply andb_true_iff in H as (H1 & H2).
  apply Z.ltb_lt in H2. split; [exact H1 | ]. unfold rts_iw. destruct (su_wbits u =? 8); lia.
Qed.

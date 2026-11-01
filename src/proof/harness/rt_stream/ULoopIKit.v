(* Law rt_stream (data of any length), main's inflate loop (ULoopI.v): one inflate() call in the model, the
   memory of a call, the assertions of the loop's body, and the tactics of the loop's proof.  Round 1's kit of
   the bounded harness (MainLoopIKit.v) with the call facts of UIFacts.v: a call takes at most 2^32 - 1 bytes of
   input and of output space (clip()).

   Before each call main records the decompressor's position in its local struct position [at]
   (position_of(&decompressor, &at), laws_session.h); after the test of the codes, a call that was offered
   neither input nor output space (at.avail_in == 0 && at.avail_out == 0) must not have returned Z_OK and must
   have moved nothing (unmoved(&decompressor, &at)).  The position main records is [opos]; [call_step] gives,
   for such a call, a code other than Z_OK and the stream's six members equal to it (UIFacts.ui_call's last
   clause). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Zlib.proof.deflate.Obligations.
Require Zlib.proof.deflate.Api_toend.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.SpecW.
Require Import Zlib.proof.harness.rt_stream.UIFacts.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.rt_stream.LawCS.
Require Import Zlib.proof.harness.rt_stream.UMainStmt.
Require Import Zlib.proof.harness.rt_stream.UMainKit.
Require Import Zlib.harness.rt_stream.code.
Require Import Zlib.proof.harness.rt_stream.ULoopIPos.
#[local] Existing Instance LawCS.CS.
Local Open Scope logic.

(** ** One inflate() call in the model *)

(* the stream main hands to inflate(): z with next_in, avail_in, next_out, avail_out set *)
Definition zoff (z : zfields) (ni : val) (ai : Z) (no : val) (ao : Z) : zfields :=
  ZF ni ai (zf_tin z) no ao (zf_tout z) (zf_msg z) (zf_dt z) (zf_adler z) (zf_res z).

(* the input object: O at the start of compressed, offered from pos on; the output object: out written at the
   start of out *)
Definition ib_of (u : setup) (O : list Z) (pos : Z) : inbuf :=
  InBuf Ews (su_cp u) pos (su_cap u) (cbytes (su_cap u) O).
Definition ob_of (u : setup) (out : list Z) : outbuf :=
  OutBuf Ews (su_op u) (Zlength out) (Zlength (su_data u)) (cbytes (Zlength (su_data u)) out).

(* the position main records before the call: next_in at pos in compressed, avail_in ai, next_out after the
   output out, avail_out ao, and the totals of z *)
Definition opos (u : setup) (pos : Z) (out : list Z) (z : zfields) (ai ao : Z) : LS.posz :=
  LS.mk_posz (offset_val pos (su_cp u)) ai (zf_tin z) (offset_val (Zlength out) (su_op u)) ao (zf_tout z).

Lemma cbytes_len n l : Zlength l <= n -> Zlength (cbytes n l) = n.
Proof. intros H. unfold cbytes. rewrite Zlength_app, Zlength_map, Zlength_Zrepeat; lia. Qed.

(* a call that did not run out of memory: a documented code, and the invariant's facts at the new position
   (pos + bytes consumed) with the new output (out ++ bytes written); offered neither input nor output space,
   not Z_OK and the stream's position unchanged *)
Lemma call_step P u O l vd take room flush r z' st' ow :
  urts_ifacts P -> su_ok u -> Zlength O <= su_cap u -> il_ok P u O l -> live_ok (il_L l) ->
  zf_ok (il_z l) -> 0 <= take <= Int.max_unsigned -> il_pos l + take <= Zlength O ->
  0 <= room <= Zlength (su_data u) - Zlength (il_out l) -> room <= Int.max_unsigned -> isptr vd ->
  inflate_rel flush vd
    (zoff (il_z l) (in_ptr (ib_of u O (il_pos l)) 0) take (out_ptr (ob_of u (il_out l)) 0) room)
    (Some (il_L l)) (ib_of u O (il_pos l)) (sublist (il_pos l) (il_pos l + take) O)
    (Some (ob_of u (il_out l))) r z' st' ow ->
  (forall L', st' = Some L' -> swfW (l_s L')) ->
  r <> Z_MEM_ERROR ->
  exists l', st' = Some (il_L l') /\ il_z l' = z' /\ il_out l' = il_out l ++ ow /\
    (r = Z_OK \/ r = Z_BUF_ERROR \/ r = Z_STREAM_END) /\
    Zlength (il_out l) + Zlength ow <= Zlength (su_data u) /\
    il_ok P u O l' /\
    (r = Z_STREAM_END -> il_out l' = su_data u /\ il_pos l' = Zlength O) /\
    (take = 0 -> room = 0 -> r <> Z_OK /\ zpos z' = opos u (il_pos l) (il_out l) (il_z l) take room).
Proof.
  intros PF SU HO IL LO ZO Ht Hpt Hroom Hroom' Pvd REL Hsw' Hr.
  destruct l as [pos out L z]; simpl in *.
  destruct IL as (HP & Hsw & Hpos & (rest & Erest) & Eni & Eno).
  cbn [il_pos il_out il_L il_z] in *.
  destruct SU as (_ & _ & _ & _ & Hn & _ & Hcap & _).
  destruct REL as [(Hbad & _) | (_ & L0 & o0 & res & winp & EL & Eo & Hrun & Hsnx & Er & Eow & Ez & _ & Est)].
  { exfalso. unfold inflate_bad, is_live in Hbad. destruct (eq_dec vd nullval) as [E|_]; [subst; contradiction | ].
    destruct Hbad as [H|[H|[H _]]]; discriminate. }
  injection EL as <-. injection Eo as <-.
  set (inp := sublist pos (pos + take) O) in *.
  assert (Hinp : Zlength inp = take) by (unfold inp; rewrite Zlength_sublist; lia).
  set (zo := zoff z (in_ptr (ib_of u O pos) 0) take (out_ptr (ob_of u out) 0) room) in *.
  assert (HD : Zlength (su_data u) = Zlength out + Zlength rest) by (rewrite Erest, Zlength_app; lia).
  destruct (ui_call P PF (su_data u) O pos out L zo inp flush res)
    as [Hm | (Hc & Hsnx' & Hsow & Hao & (rest' & Erest') & HP' & Hend & Hidle)].
  - exact HP.
  - exact LO.
  - unfold zf_ok in *; simpl. pose proof (Zlength_nonneg rest). rep_lia.
  - simpl. rep_lia.
  - rep_lia.
  - lia.
  - lia.
  - rewrite Hinp. reflexivity.
  - exact Hrun.
  - subst r. contradiction.
  - set (m := r_m res) in *.
    set (L' := Live (l_sp L) winp (m_s m) (m_h m) (l_headp L) (l_hsh L) (l_xb L) (l_nb L) (l_cb L)).
    assert (HDl : Zlength (su_data u) = Zlength out + Zlength ow + Zlength rest')
      by (subst ow; rewrite Erest', !Zlength_app; lia).
    pose proof (Zlength_nonneg rest').
    exists (mkIL (pos + m_snx m) (out ++ ow) L' z'). simpl.
    split; [exact Est | ]. split; [reflexivity | ]. split; [reflexivity | ].
    split; [subst r; exact Hc | ]. split; [lia | ].
    split; [ | split].
    + unfold il_ok; simpl. subst z' ow. simpl.
      split; [exact HP' | ]. split; [exact (Hsw' L' Est) | ]. split; [lia | ].
      split; [exists rest'; rewrite <- app_assoc; exact Erest' | ].
      split; [reflexivity | ].
      simpl. f_equal. rewrite Zlength_app. fold m. lia.
    + intros E. subst r. destruct (Hend E) as (E1 & E2). subst ow. split; auto.
    + intros Ht0 Hr0.
      destruct (Hidle ltac:(lia) ltac:(unfold zo; simpl; exact Hr0)) as (Hok & Eow0 & Etin & Etout).
      assert (Es0 : m_snx m = 0) by lia.
      pose proof (run2_inp _ _ _ _ _ Hrun) as Ei0. fold m in Ei0.
      split; [subst r; exact Hok | ].
      subst z'. unfold zo, zpos, opos, z_after, ib_of, ob_of. fold m. simpl.
      rewrite Etin, Etout, Es0, Hsow, Eow0, Ei0, Hao, Hinp. simpl.
      rewrite !Z.add_0_r, Zlength_nil, !Z.sub_0_r. reflexivity.
Qed.

(** ** The memory of one call *)

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

(* at a return: the compressor's struct back to the stack frame *)
Lemma cstream_frame gv vc c : cstream gv vc c |-- data_at_ Tsh t_z vc * TT.
Proof.
  unfold cstream, srest.
  sep_apply (BoundKit.dstream_data_at_ (Some (cs_s c)) vc nullval gv (cs_ni c) (cs_ain c) (cs_tin c) (cs_no c)
               (cs_aout c) (cs_tout c) (cs_msgv c) (cs_adler c) Api_toend.dstream_to_end).
  rewrite (@data_at__change_composite DCS.CS LawCS.CS CC_dcs Ews Zlib.proof.deflate.Rep.t_strm) by reflexivity.
  rewrite (BoundKit.data_at__Tsh_split t_z vc). cancel.
Qed.

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

(* the objects compressed and out as inflate()'s buffers, and back *)
Lemma bufs_pre vs L u O pos out :
  isptr vs -> Zlength O <= su_cap u -> Zlength out <= Zlength (su_data u) ->
  cobj u O * oobj u out
  |-- bufs_opt (is_live vs (Some L)) (ib_of u O pos) (Some (ob_of u out)) [] true true.
Proof.
  intros Pv Hb Hn. rewrite is_live_ptr by auto.
  unfold bufs_opt, in_rep, out_opt, out_rep, in_tok, out_tok, ib_of, ob_of, cobj, oobj.
  rewrite (cbytes_after _ out []) by (rewrite Zlength_nil; lia). rewrite app_nil_r.
  rewrite !bytes_i, !tok_i. cancel.
Qed.

Lemma bufs_post vs L u O pos out ow :
  isptr vs -> Zlength out + Zlength ow <= Zlength (su_data u) ->
  bufs_opt (is_live vs (Some L)) (ib_of u O pos) (Some (ob_of u out)) ow true true
  |-- cobj u O * oobj u (out ++ ow).
Proof.
  intros Pv Hn. rewrite is_live_ptr by auto.
  unfold bufs_opt, in_rep, out_opt, out_rep, in_tok, out_tok, ib_of, ob_of, cobj, oobj.
  rewrite (cbytes_after _ out ow) by lia.
  rewrite !bytes_i, !tok_i. cancel.
Qed.

Lemma in_ok_of u O pos take :
  su_ok u -> Zlength O <= su_cap u -> Zlib.proof.roundtrip.RTDIface.rbytes O -> 0 <= pos -> 0 <= take -> pos + take <= Zlength O ->
  in_ok (ib_of u O pos) (sublist pos (pos + take) O).
Proof.
  intros SU HO BO Hp Ht Hpt. destruct SU as (_ & _ & _ & _ & _ & _ & Hcap & _ & Pcp & _).
  unfold in_ok, ib_of.
  assert (Hs : Zlength (sublist pos (pos + take) O) = take) by (rewrite Zlength_sublist; lia).
  rewrite Hs. pose proof (Zlength_nonneg O).
  split; [auto | ]. split; [auto | ]. split; [lia | ]. split; [lia | ].
  split; [apply cbytes_len; lia | ]. split; [unfold UDFacts.max_size in *; rep_lia | ]. split.
  - unfold cbytes. rewrite sublist_app1 by (rewrite ?Zlength_map; lia).
    unfold byte_vals. rewrite sublist_map. reflexivity.
  - apply Forall_sublist. eapply Forall_impl; [ | exact BO]. simpl. intros; rep_lia.
Qed.

Lemma out_ok_of u out ao :
  su_ok u -> 0 <= ao -> Zlength out + ao <= Zlength (su_data u) -> out_ok (ob_of u out) ao.
Proof.
  intros SU Ha Hao. destruct SU as (_ & _ & _ & _ & Hn & _ & _ & _ & _ & Pop).
  unfold out_ok, ob_of. pose proof (Zlength_nonneg out).
  split; [apply writable_Ews | ]. unfold UDFacts.max_size in *. repeat split; auto; try rep_lia. apply cbytes_len; lia.
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

(** ** The loop *)

(* after the call and its Z_MEM_ERROR test: inflate() returned r (Z_OK, Z_BUF_ERROR or Z_STREAM_END), the
   invariant's facts hold at the new state, Z_STREAM_END came with all of O consumed and all the data produced,
   and at holds the position [a] recorded before the call: offered neither input nor output space, the call did
   not return Z_OK and the stream is at [a] *)
Definition ICr (gv : globals) (vc vd va : val) (P : rts_iinv) (u : setup) (O : list Z) (c : cst) (r : Z) (l : ils)
  (a : LS.posz) : environ -> mpred :=
  PROPx [su_ok u; Zlength O <= su_cap u; Zlib.proof.roundtrip.RTDIface.rbytes O; il_ok P u O l;
        r = Z_OK \/ r = Z_BUF_ERROR \/ r = Z_STREAM_END;
        r = Z_STREAM_END -> il_out l = su_data u /\ il_pos l = Zlength O;
        LS.posz_ok a;
        LS.pz_avail_in a = 0 -> LS.pz_avail_out a = 0 -> r <> Z_OK /\ zpos (il_z l) = a]
  (LOCALx (temp _code (vi r) :: temp _compressed_len (vl (Zlength O)) :: su_locals u (rts_iw (su_wbits u)) ++
           lv_locals gv vc vd va)
  (SEPx [istreamA gv Tsh vd (il_z l) Vundef (Some (il_L l)); head_opt (Some (il_L l));
        cstream gv vc c; mem_mgr gv; zfuncs gv; Rm gv; dobj u; cobj u O; oobj u (il_out l);
        @data_at LawCS.CS Tsh t_p (LS.pos_of a) va])).

(* at the loop's test: as ICr, at's contents no longer needed *)
Definition ICe (gv : globals) (vc vd va : val) (P : rts_iinv) (u : setup) (O : list Z) (c : cst) (r : Z) (l : ils)
  : environ -> mpred :=
  PROPx [su_ok u; Zlength O <= su_cap u; Zlib.proof.roundtrip.RTDIface.rbytes O; il_ok P u O l;
        r = Z_OK \/ r = Z_BUF_ERROR \/ r = Z_STREAM_END;
        r = Z_STREAM_END -> il_out l = su_data u /\ il_pos l = Zlength O]
  (LOCALx (temp _code (vi r) :: temp _compressed_len (vl (Zlength O)) :: su_locals u (rts_iw (su_wbits u)) ++
           lv_locals gv vc vd va)
  (SEPx [istreamA gv Tsh vd (il_z l) Vundef (Some (il_L l)); head_opt (Some (il_L l));
        cstream gv vc c; mem_mgr gv; zfuncs gv; Rm gv; dobj u; cobj u O; oobj u (il_out l); data_at_ Tsh t_p va])).

Definition IC (gv : globals) (vc vd va : val) (P : rts_iinv) (u : setup) (O : list Z) (c : cst)
  : environ -> mpred :=
  EX r : Z, EX l : ils, ICe gv vc vd va P u O c r l.

(* the postcondition of the loop's body: IC at the test, IE at the break, a return to main's postcondition *)
Definition RI (gv : globals) (vc vd va : val) (P : rts_iinv) (u : setup) (O : list Z) (c : cst) : ret_assert :=
  loop1_ret_assert (IC gv vc vd va P u O c)
    (overridePost (EX z : zfields, EX L : live, IE gv vc vd va u O c z L)
       (overridePost (EX z : zfields, EX L : live, IE gv vc vd va u O c z L) POST_m)).

(** ** The loop's body cut into its parts *)

(* the body: offer avail_in (upto the compressed bytes left), offer avail_out (upto the room left),
   position_of(&decompressor, &at), the inflate() call with any flush, its Z_MEM_ERROR test, the test of the
   documented codes and the test of a call offered neither input nor output space *)
Definition bodyI : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [loopI] in (match loopI with Sloop b _ => b | s => s end) in exact x).
Definition incrI : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [loopI] in (match loopI with Sloop _ i => i | s => s end) in exact x).
Definition offerIn : statement := ltac:(let x := eval cbv beta iota zeta delta [bodyI first] in (first bodyI) in exact x).
Definition offerOut : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [bodyI first suf] in (first (suf 1 bodyI)) in exact x).
Definition posI : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [bodyI first suf] in (first (suf 2 bodyI)) in exact x).
Definition callI : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [bodyI first suf] in (first (suf 3 bodyI)) in exact x).
Definition memI : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [bodyI first suf] in (first (suf 4 bodyI)) in exact x).
Definition codesI : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [bodyI first suf] in (first (suf 5 bodyI)) in exact x).
Definition idleI : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [bodyI suf] in (suf 6 bodyI) in exact x).

Lemma loopI_parts :
  loopI = Sloop (Ssequence offerIn (Ssequence offerOut (Ssequence posI (Ssequence callI
            (Ssequence memI (Ssequence codesI idleI)))))) incrI.
Proof. reflexivity. Qed.

(* the decompressor's struct while main offers the buffers: next_in at pos in compressed, next_out after
   the output out, avail_in ai, avail_out ao *)
Definition oS (gv : globals) (u : setup) (pos : Z) (out : list Z) (z : zfields) (L : live) (ai ao : val)
  : reptype t_z :=
  (offset_val pos (su_cp u), (ai, (vl (zf_tin z), (offset_val (Zlength out) (su_op u), (ao, (vl (zf_tout z),
   (msg_val gv (zf_msg z), (l_sp L, (gv Zlib.inflate.code._zcalloc, (gv Zlib.inflate.code._zcfree, (nullval,
   (vi (zf_dt z), (adler_v (raw_live (Some L)) z Vundef, zf_res z))))))))))))).

(* the state between the stores into avail_in and avail_out and the call, with the facts Q; [A] is the memory
   of at (any bytes before position_of, the recorded position after it) *)
Definition OI (Q : list Prop) (gv : globals) (vc vd va : val) (u : setup) (O : list Z) (c : cst)
  (pos : Z) (out : list Z) (z : zfields) (L : live) (ai ao : val) (A : mpred) : environ -> mpred :=
  PROPx Q
  (LOCALx (temp _compressed_len (vl (Zlength O)) :: su_locals u (rts_iw (su_wbits u)) ++ lv_locals gv vc vd va)
  (SEPx [data_at Tsh t_z (oS gv u pos out z L ai ao) vd; state_mem gv vd L; head_opt (Some L);
        cstream gv vc c; mem_mgr gv; zfuncs gv; Rm gv; dobj u; cobj u O; oobj u out; A])).

(** ** The decompressor and at for position_of and unmoved *)

(* the struct as main offered the buffers, at laws_session's compspecs *)
Lemma oS_session gv u pos out z L ai ao vd :
  data_at Tsh t_z (oS gv u pos out z L (vi ai) (vi ao)) vd =
  @data_at LS.CS_session Tsh t_zs
    (LS.zs_of (opos u pos out z ai ao) (zrest gv z (adler_v (raw_live (Some L)) z Vundef) (l_sp L))) vd.
Proof. symmetry. cs_tac CC_session. Qed.

Lemma at_cs (va : val) : @data_at_ LawCS.CS Tsh t_p va = @data_at_ LS.CS_session Tsh LS.t_pos va.
Proof. symmetry. apply equal_f. apply (@data_at__change_composite _ _ CC_session). reflexivity. Qed.

Lemma at_pos_cs (a : LS.posz) (va : val) :
  @data_at LawCS.CS Tsh t_p (LS.pos_of a) va = @data_at LS.CS_session Tsh LS.t_pos (LS.pos_of a) va.
Proof. symmetry. cs_tac CC_session. Qed.

(* the position main records is well typed *)
Lemma opos_ok u pos out z ai ao :
  su_ok u -> zf_ok z -> 0 <= ai <= Int.max_unsigned -> 0 <= ao <= Int.max_unsigned ->
  LS.posz_ok (opos u pos out z ai ao).
Proof.
  intros SU Zo Hi Ho. destruct SU as (_ & _ & _ & _ & _ & _ & _ & _ & Pcp & Pop).
  unfold LS.posz_ok, opos, zf_ok in *; simpl.
  destruct (su_cp u); try contradiction; destruct (su_op u); try contradiction. simpl. intuition.
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

(* unmoved's comparisons when next_in (in compressed) and next_out (in out) are compared with themselves *)
Lemma objs_cmp (u : setup) (O out : list Z) (pos : Z) :
  isptr (su_cp u) -> isptr (su_op u) -> 0 <= pos <= su_cap u -> Zlength out <= Zlength (su_data u) ->
  cobj u O * oobj u out |--
  denote_tc_test_eq (offset_val pos (su_cp u)) (offset_val pos (su_cp u)) &&
  denote_tc_test_eq (offset_val (Zlength out) (su_op u)) (offset_val (Zlength out) (su_op u)).
Proof.
  intros Pc Po Hp Ho. pose proof (Zlength_nonneg out).
  unfold cobj, oobj.
  apply andp_right; (eapply derives_trans; [ | apply test_eq_self; rewrite isptr_offset_val; assumption]).
  - apply sepcon_weak_valid_pointer1. apply obj_wv. lia.
  - apply sepcon_weak_valid_pointer2. apply obj_wv. lia.
Qed.


(* a branch that cannot be taken *)
Ltac infeas := exfalso; first [ match goal with H : ?a <> ?b |- _ => solve [apply H; reflexivity] end
                              | match goal with H : _ |- _ => solve [discriminate H] end
                              | contradiction
                              | match goal with H : Int.repr _ = Int.repr _ |- _ =>
                                  apply repr_inj_signed in H; [lia | rep_lia | rep_lia] end
                              | lia ].
(* `if (c) t = 1; else t = (expr);` with the value v of t known *)
Ltac ifk t v := match goal with |- semax _ (PROPx _ (LOCALx ?Q (SEPx ?R))) _ _ =>
  forward_if (PROPx [] (LOCALx (temp t (Vint (Int.repr v)) :: Q) (SEPx R))) end;
  [ first [infeas | forward; entailer!] | first [infeas | forward; entailer!] | ].

(* the side conditions of upto(m - (size_t) (p + k - p)) *)
Ltac upto_side := first
  [ unfold UDFacts.max_size in *; rep_lia
  | entailer!; unfold UDFacts.max_size in *;
    first [apply sameblock_off; auto | unfold vl; rewrite ptr_sub by (auto; rep_lia); reflexivity] ].


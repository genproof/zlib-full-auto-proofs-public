(* Law rt_session (harness/rt_session.c), main's inflate loop with a gzip header (SMLoopI9.v): one inflate() call
   in the model, the memory of a call, the assertions of the loop's body and the tactics of its proof.

   The loop is rt_stream_trailing's inflate loop with the Z_NEED_DICT branch: each call is offered the next piece
   of the input object [src] (the stream O, then any bytes) and any room left in out, position_of records the
   decompressor's position in at before the call, and after it main checks the documented codes, accounted, and
   (offered neither input nor output space) code != Z_OK and unmoved.  With a header, inflate() has RTH9Spec's
   specification: the stream is an [istream8] (live_ok8) and got, attached by inflateGetHeader, is held as
   [head_mem9].  The facts of a call come from SIFacts.si_call; Z_NEED_DICT is never returned, since it needs the
   zlib wrapper (sk_zdict) while a session with a header has the gzip wrapper (sc_ok).

   position_of, unmoved and accounted read the struct at laws_session's compspecs: [istream8_session] and
   [oS9_session] are the conversions (rt_stream's ULoopIPos.istreamA_session for istream8). *)
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
Require Zlib.proof.roundtrip.RTH8Spec.
Require Zlib.proof.roundtrip.RTH9Spec.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.rt_session.SCS.
Require Import Zlib.proof.harness.rt_session.SDFacts.
Require Import Zlib.proof.harness.rt_session.SIFacts.
Require Import Zlib.proof.harness.rt_session.SMainStmt.
Require Import Zlib.proof.harness.rt_session.SMKit.
Require Import Zlib.proof.harness.rt_stream.ULoopIPos.
Require Zlib.proof.harness.rt_stream.ULoopIKit.
Require Import Zlib.harness.rt_session.code.
#[local] Existing Instance SCS.CS.
Local Open Scope logic.
Module R8 := Zlib.proof.roundtrip.RTH8Spec.
Module R9 := Zlib.proof.roundtrip.RTH9Spec.
Module UK := Zlib.proof.harness.rt_stream.ULoopIKit.

(** ** One inflate() call in the model *)

(* the stream main hands to inflate(): z with next_in, avail_in, next_out, avail_out set *)
Definition zoff9 (z : zfields) (ni : val) (ai : Z) (no : val) (ao : Z) : zfields :=
  ZF ni ai (zf_tin z) no ao (zf_tout z) (zf_msg z) (zf_dt z) (zf_adler z) (zf_res z).

(* the input object: src, offered from pos on; the output object: out written at the start of out *)
Definition ib9 (src : list Z) (ip : val) (pos : Z) : inbuf := InBuf Ews ip pos (Zlength src) (map vi src).
Definition ob9 (u : setup) (out : list Z) : outbuf :=
  OutBuf Ews (su_op u) (Zlength out) (Zlength (su_data u)) (cbytes (Zlength (su_data u)) out).

(* the position main records before the call: next_in at pos in the input, avail_in ai, next_out after the output
   out, avail_out ao, and the totals of z *)
Definition opos9 (ip : val) (u : setup) (pos : Z) (out : list Z) (z : zfields) (ai ao : Z) : LS.posz :=
  LS.mk_posz (offset_val pos ip) ai (zf_tin z) (offset_val (Zlength out) (su_op u)) ao (zf_tout z).

(* accounted(&decompressor, &at) after a call from the position [a]: it returns 1, and the two sums it compares
   are pointers into (or one past) the input object and the output object *)
Definition acc_ok9 (src : list Z) (ip : val) (u : setup) (l : ils) (a : LS.posz) : Prop :=
  LS.accounted_b (zpos (il_z l)) a = true /\ isptr (LS.pz_next_in a) /\ isptr (LS.pz_next_out a) /\
  exists ki ko, 0 <= ki <= Zlength src /\ 0 <= ko <= Zlength (su_data u) /\
    offset_val (LS.pz_avail_in a) (LS.pz_next_in a) = offset_val ki ip /\
    offset_val (LS.pz_avail_out a) (LS.pz_next_out a) = offset_val ko (su_op u).

(* where the stream is between the calls: next_in in the input object, next_out after the output so far *)
Definition il_mem9 (u : setup) (src : list Z) (ip : val) (l : ils) : Prop :=
  0 <= il_pos l <= Zlength src /\ Zlength (il_out l) <= Zlength (su_data u) /\
  zf_ni (il_z l) = offset_val (il_pos l) ip /\ zf_no (il_z l) = offset_val (Zlength (il_out l)) (su_op u).

(* after the call that returned Z_STREAM_END: all of O consumed, all the data produced, no dictionary asked for,
   got holds the header *)
Definition end9 (u : setup) (O : list Z) (l : ils) : Prop :=
  il_out l = su_data u /\ il_pos l = Zlength O /\ il_asked l = false /\
  g2_hdr_out (gh_of u) (h0 u) (l_s (il_L l)) (l_h (il_L l)).

Lemma offset_offset9 (p : val) (i j : Z) : offset_val j (offset_val i p) = offset_val (i + j) p.
Proof. rewrite offset_offset_val. reflexivity. Qed.

Lemma ptr_eqb_refl9 (p : val) : LS.ptr_eqb p p = true.
Proof. unfold LS.ptr_eqb. destruct (Val.eq p p); [reflexivity | congruence]. Qed.

(* the session of a setup with a header: the header is set, so the wrapper is gzip's and not zlib's *)
Lemma sgh_head u : with_head u = true -> sgh u = Some (gh_of u).
Proof. intros H. unfold sgh. rewrite H. reflexivity. Qed.

Lemma head_not_zdict u D O : with_head u = true -> sc_ok (scase_of u) D O -> ~ sk_zdict (scase_of u).
Proof.
  intros H (_ & _ & _ & Hw & _) (_ & Hz).
  assert (E : sc_gh (scase_of u) <> None) by (cbn; rewrite sgh_head by exact H; discriminate).
  specialize (Hw E). rewrite Hz in Hw. discriminate.
Qed.

(* a setup with a header has no dictionary: main's flag asked must stay 0 *)
Lemma head_no_dict u : with_head u = true -> with_dict u = false.
Proof.
  unfold with_head, with_dict. intros H. apply andb_prop in H. destruct H as (H1 & H2).
  apply Z.ltb_lt in H1. rewrite H2, andb_true_r. apply Z.leb_gt. exact H1.
Qed.

(* a call that did not run out of memory: Z_OK, Z_BUF_ERROR or Z_STREAM_END; the stream moved to the new position
   (pos + bytes consumed) with the new output (out ++ bytes written) and the same gz_header pointers; the
   invariant after Z_OK and Z_BUF_ERROR, the end facts after Z_STREAM_END; accounted holds of the position
   recorded before the call; offered neither input nor output space, not Z_OK and the stream's position
   unchanged *)
Lemma call_step9 P PN u O src ip l vd take room flush r z' st' ow :
  ses_ifacts (fun _ => True) P PN -> su_ok u -> with_head u = true -> sc_ok (scase_of u) (su_data u) O ->
  src_ok O src -> isptr ip -> il_ok P u O src ip l -> R8.live_ok8 (il_L l) ->
  zf_ok (il_z l) -> 0 <= take <= Int.max_unsigned -> il_pos l + take <= Zlength src ->
  0 <= room <= Zlength (su_data u) - Zlength (il_out l) -> room <= Int.max_unsigned -> isptr vd ->
  inflate_rel flush vd
    (zoff9 (il_z l) (in_ptr (ib9 src ip (il_pos l)) 0) take (out_ptr (ob9 u (il_out l)) 0) room)
    (Some (il_L l)) (ib9 src ip (il_pos l)) (sublist (il_pos l) (il_pos l + take) src)
    (Some (ob9 u (il_out l))) r z' st' ow ->
  (forall L', st' = Some L' -> swfW (l_s L')) ->
  r <> Z_MEM_ERROR ->
  exists l', st' = Some (il_L l') /\ il_z l' = z' /\ il_out l' = il_out l ++ ow /\ il_asked l' = il_asked l /\
    l_headp (il_L l') = l_headp (il_L l) /\ l_hsh (il_L l') = l_hsh (il_L l) /\
    l_xb (il_L l') = l_xb (il_L l) /\ l_nb (il_L l') = l_nb (il_L l) /\ l_cb (il_L l') = l_cb (il_L l) /\
    (r = Z_OK \/ r = Z_BUF_ERROR \/ r = Z_STREAM_END) /\
    Zlength (il_out l) + Zlength ow <= Zlength (su_data u) /\
    il_mem9 u src ip l' /\
    (r <> Z_STREAM_END -> il_ok P u O src ip l') /\
    (r = Z_STREAM_END -> end9 u O l') /\
    (take = 0 -> room = 0 -> r <> Z_OK /\ zpos z' = opos9 ip u (il_pos l) (il_out l) (il_z l) take room) /\
    acc_ok9 src ip u l' (opos9 ip u (il_pos l) (il_out l) (il_z l) take room).
Proof.
  intros PF SU HH SC SO Pip IL LO ZO Ht Hpt Hroom Hroom' Pvd REL Hsw' Hr.
  destruct l as [pos out asked L z]; simpl in *.
  destruct IL as (HP & Hsw & Hpos & (rest & Erest) & Eni & Eno).
  cbn [il_pos il_out il_asked il_L il_z] in *.
  pose proof SU as (_ & _ & _ & _ & _ & _ & _ & Pop & _).
  destruct REL as [(Hbad & _) | (_ & L0 & o0 & res & winp & EL & Eo & Hrun & Hsnx & Er & Eow & Ez & _ & Est)].
  { exfalso. unfold inflate_bad, is_live in Hbad. destruct (eq_dec vd nullval) as [E|_]; [subst; contradiction | ].
    destruct Hbad as [H|[H|[H _]]]; discriminate. }
  injection EL as <-. injection Eo as <-.
  set (inp := sublist pos (pos + take) src) in *.
  assert (Hinp : Zlength inp = take) by (unfold inp; rewrite Zlength_sublist; lia).
  set (zo := zoff9 z (in_ptr (ib9 src ip pos) 0) take (out_ptr (ob9 u out) 0) room) in *.
  assert (HD : Zlength (su_data u) = Zlength out + Zlength rest) by (rewrite Erest, Zlength_app; lia).
  assert (LC : live_c (scase_of u) L) by (unfold live_c; cbn; rewrite sgh_head by exact HH; exact LO).
  destruct (si_call _ _ _ PF (scase_of u) (su_data u) O src pos out asked L zo inp flush res winp)
    as [Hm | (Hc & Hsnx' & Hsow & Hao & (rest' & Erest') & HP' & Hneed & Hend & Hidle)].
  - exact I.
  - exact SC.
  - exact SO.
  - exact HP.
  - exact LC.
  - exact Hsw.
  - unfold zf_ok in *; simpl. pose proof (Zlength_nonneg rest). rep_lia.
  - simpl. rep_lia.
  - rep_lia.
  - lia.
  - lia.
  - rewrite Hinp. reflexivity.
  - exact Hrun.
  - subst r. contradiction.
  - set (m := r_m res) in *.
    set (L' := Live (l_sp L) winp (m_s m) (m_h m) (l_headp L) (l_hsh L) (l_xb L) (l_nb L) (l_cb L)) in *.
    assert (HDl : Zlength (su_data u) = Zlength out + Zlength ow + Zlength rest')
      by (subst ow; rewrite Erest', !Zlength_app; lia).
    pose proof (Zlength_nonneg rest').
    pose proof (run2_inp _ _ _ _ _ Hrun) as Ei0. fold m in Ei0.
    assert (Hc3 : r = Z_OK \/ r = Z_BUF_ERROR \/ r = Z_STREAM_END).
    { subst r. destruct Hc as [E|[E|[E|E]]]; auto.
      exfalso. destruct (Hneed E) as (Hz & _). exact (head_not_zdict u _ _ HH SC Hz). }
    exists (mkIL (pos + m_snx m) (out ++ ow) asked L' z'). simpl.
    split; [exact Est | ]. split; [reflexivity | ]. split; [reflexivity | ]. split; [reflexivity | ].
    do 5 (split; [reflexivity | ]).
    split; [exact Hc3 | ]. split; [lia | ].
    split; [ | split; [ | split; [ | split]]].
    + unfold il_mem9; simpl. subst z' ow. simpl.
      split; [lia | ]. split; [rewrite Zlength_app; lia | ]. split; [reflexivity | ].
      simpl. f_equal. rewrite Zlength_app. fold m. lia.
    + intros Hne. unfold il_ok; simpl. subst z' ow. simpl.
      assert (Hob : r_ret res = Z_OK \/ r_ret res = Z_BUF_ERROR)
        by (subst r; destruct Hc3 as [E|[E|E]]; auto; contradiction).
      split; [exact (HP' Hob) | ]. split; [exact (Hsw' L' Est) | ]. split; [lia | ].
      split; [exists rest'; rewrite <- app_assoc; exact Erest' | ].
      split; [reflexivity | ].
      simpl. f_equal. rewrite Zlength_app. fold m. lia.
    + intros E. subst r. destruct (Hend E) as (E1 & E2 & E3 & E4). subst ow.
      unfold end9; simpl. split; [exact E1 | ]. split; [exact E2 | ]. split.
      * destruct asked; [ | reflexivity]. exfalso. apply (head_not_zdict u _ _ HH SC). apply E3. reflexivity.
      * apply E4. cbn. apply sgh_head. exact HH.
    + intros Ht0 Hr0.
      destruct (Hidle ltac:(lia) ltac:(unfold zo; simpl; exact Hr0)) as (Hok & Eow0 & Etin & Etout).
      assert (Es0 : m_snx m = 0) by lia.
      split; [subst r; exact Hok | ].
      subst z'. unfold zo, zpos, opos9, z_after, ib9, ob9. fold m. simpl.
      rewrite Etin, Etout, Es0, Hsow, Eow0, Ei0, Hao, Hinp. simpl.
      rewrite !Z.add_0_r, Zlength_nil, !Z.sub_0_r. reflexivity.
    + (* accounted: next_in' + avail_in' = ip + pos + take, next_out' + avail_out' = out + |out| + room *)
      subst z'. unfold acc_ok9, zpos, opos9, z_after, ib9, ob9, LS.accounted_b. fold m.
      cbn [il_z zf_ni zf_ai zf_no zf_ao in_ptr out_ptr LS.pz_next_in LS.pz_avail_in LS.pz_next_out
           LS.pz_avail_out].
      rewrite Ei0, Hinp, Hao. unfold zo; cbn [zoff9 zf_ao].
      rewrite !offset_offset9.
      pose proof (Zlength_nonneg (m_ow m)).
      rewrite ?Z.add_0_r, ?Z.add_0_l.
      replace (pos + m_snx m + (take - m_snx m)) with (pos + take) by lia.
      replace (Zlength out + m_sow m + (room - m_sow m)) with (Zlength out + room) by lia.
      rewrite !ptr_eqb_refl9.
      assert (Hle1 : (take - m_snx m <=? take) = true) by (apply Z.leb_le; lia).
      assert (Hle2 : (room - m_sow m <=? room) = true) by (apply Z.leb_le; lia).
      rewrite Hle1, Hle2. simpl.
      split; [reflexivity | ].
      split; [rewrite isptr_offset_val; exact Pip | ].
      split; [rewrite isptr_offset_val; exact Pop | ].
      exists (pos + take), (Zlength out + room). pose proof (Zlength_nonneg out).
      split; [lia | ]. split; [lia | ]. split; reflexivity.
Qed.

(** ** The memory of one call *)

Ltac cs_tac9 CC := apply equal_f; apply (@data_at_change_composite _ _ CC); [apply JMeq_refl | reflexivity].

Lemma bytes_i9 sh n (v : list val) q :
  @data_at Zlib.units.Inflate.CS sh (tarray tuchar n) v q = data_at sh (tarray tuchar n) v q.
Proof. cs_tac9 CC_inflate. Qed.
Lemma tok_i9 sh n q :
  @malloc_token Zlib.units.Inflate.CS sh (tarray tuchar n) q = malloc_token sh (tarray tuchar n) q.
Proof. apply equal_f; apply (@malloc_token_change_composite _ _ CC_inflate). reflexivity. Qed.
Lemma strm_cs9 sh (v : reptype t_z) q :
  @data_at Zlib.units.Inflate.CS sh t_z v q = data_at sh t_z v q.
Proof. cs_tac9 CC_inflate. Qed.

(* the decompressor's struct z_stream as main reads and writes it: istream8's struct at the law's compspecs *)
Definition tup9 (gv : globals) (z : zfields) (sp : val) : reptype t_z :=
  (zf_ni z, (vi (zf_ai z), (vl (zf_tin z), (zf_no z, (vi (zf_ao z), (vl (zf_tout z), (msg_val gv (zf_msg z),
   (sp, (gv Zlib.inflate.code._zcalloc, (gv Zlib.inflate.code._zcfree, (nullval, (vi (zf_dt z),
   (vl (zf_adler z), zf_res z))))))))))))).

Lemma istream8_unfold gv shs vs z L :
  R8.istream8 gv shs vs z (Some L) =
  (!! (zf_ok z /\ writable_share shs /\ R8.live_ok8 L) &&
   (data_at shs t_z (tup9 gv z (l_sp L)) vs * state_mem gv vs L)).
Proof.
  unfold R8.istream8, zstrm_at, Zlib.proof.inflate.Rep.strm_rep. change Zlib.proof.inflate.Rep.t_strm with t_z.
  rewrite strm_cs9.
  apply pred_ext; entailer!.
Qed.

Lemma istream8_opt_ptr gv shs (vs : val) z st :
  isptr vs -> R8.istream8_opt gv shs vs z st = R8.istream8 gv shs vs z st.
Proof. intros Pv. unfold R8.istream8_opt. destruct (eq_dec vs nullval); [subst; contradiction | reflexivity]. Qed.

Lemma is_live_ptr9 (vs : val) st : isptr vs -> is_live vs st = st.
Proof. intros Pv. unfold is_live. destruct (eq_dec vs nullval); [subst; contradiction | reflexivity]. Qed.

(* the struct after main's stores into avail_in and avail_out: the stream inflate() takes *)
Lemma offer_fold9 gv vs z L ni ai no ao :
  isptr vs -> zf_ok z -> R8.live_ok8 L -> 0 <= ai <= Int.max_unsigned -> 0 <= ao <= Int.max_unsigned ->
  data_at Tsh t_z
    (ni, (vi ai, (vl (zf_tin z), (no, (vi ao, (vl (zf_tout z), (msg_val gv (zf_msg z), (l_sp L,
     (gv Zlib.inflate.code._zcalloc, (gv Zlib.inflate.code._zcfree, (nullval, (vi (zf_dt z),
     (vl (zf_adler z), zf_res z))))))))))))) vs * state_mem gv vs L
  |-- R8.istream8_opt gv Tsh vs (zoff9 z ni ai no ao) (Some L).
Proof.
  intros Pv Zo Lo Hai Hao.
  rewrite istream8_opt_ptr by auto. rewrite istream8_unfold.
  unfold tup9, zoff9; simpl.
  apply andp_right; [ | apply derives_refl].
  apply prop_right. unfold zf_ok in *; simpl in *. split; [ | split; [apply writable_share_top | auto]].
  intuition.
Qed.

(* at a return: the decompressor's struct back to the stack frame *)
Lemma istream8_frame gv shs vs z st : isptr vs ->
  R8.istream8_opt gv shs vs z st |-- data_at_ shs t_z vs * TT.
Proof.
  intros Pv. rewrite istream8_opt_ptr by auto.
  unfold R8.istream8, zstrm_at, Zlib.proof.inflate.Rep.strm_rep.
  change Zlib.proof.inflate.Rep.t_strm with t_z.
  destruct st as [L|]; rewrite strm_cs9; Intros.
  - apply sepcon_derives; [apply data_at_data_at_ | apply TT_right].
  - rewrite <- (sepcon_emp (data_at _ _ _ _)). apply sepcon_derives; [apply data_at_data_at_ | apply TT_right].
Qed.

(* at a return: the compressor's struct back to the stack frame *)
Lemma cstream_frame9 gv vc ghp c : cstream gv vc ghp c |-- data_at_ Tsh t_z vc * TT.
Proof.
  unfold cstream, srest.
  sep_apply (BoundKit.dstream_data_at_ (Some (cs_s c)) vc ghp gv (cs_ni c) (cs_ain c) (cs_tin c) (cs_no c)
               (cs_aout c) (cs_tout c) (cs_msgv c) (cs_adler c) Zlib.proof.deflate.Api_toend.dstream_to_end).
  rewrite (@data_at__change_composite Zlib.proof.deflate.DCS.CS SCS.CS CC_dcs Ews Zlib.proof.deflate.Rep.t_strm)
    by reflexivity.
  rewrite (BoundKit.data_at__Tsh_split t_z vc). cancel.
Qed.

Lemma head_cs9 sh (v : @reptype Zlib.units.Inflate.CS Zlib.proof.inflate.Rep.t_head) q :
  @data_at Zlib.units.Inflate.CS sh Zlib.proof.inflate.Rep.t_head v q |-- @data_at_ SCS.CS sh t_g q.
Proof.
  erewrite (@data_at_change_composite _ _ CC_inflate sh Zlib.proof.inflate.Rep.t_head v);
    [ apply data_at_data_at_ | apply JMeq_refl | reflexivity ].
Qed.

(* at a return: got, while the stream holds it, back to the stack frame *)
Lemma head_mem9_frame L vg :
  l_headp L = vg -> l_hsh L = Tsh -> R9.head_mem9 L |-- data_at_ Tsh t_g vg * TT.
Proof.
  intros Hp Hs. unfold R9.head_mem9. rewrite Hp, Hs.
  rewrite !sepcon_assoc. rewrite !distrib_orp_sepcon. repeat apply orp_left.
  - unfold Zlib.proof.roundtrip.RTHSpec.head_rep6, Zlib.proof.roundtrip.RTHSpec.head_rep6p. Intros.
    Intros vt vtm vxf vos vxl vhc lx ln lc. sep_apply head_cs9. cancel.
  - unfold R8.head_rep8a, Zlib.proof.roundtrip.RTHSpec.head_rep6p. Intros.
    Intros vt vtm vxf vos vxl vhc lx ln lc. sep_apply head_cs9. cancel.
  - unfold Zlib.proof.roundtrip.RTHSpec.hraw6. Intros. Intros vt vtm vxf vos vxl vhc vdn lx ln lc.
    sep_apply head_cs9. cancel.
Qed.

(* the loop's exit: a header passed (out of the header modes, done 1) is IE_9's head_mem8 *)
Lemma head_exit9 L :
  i_head (l_s L) = true -> Zlib.proof.roundtrip.RTHSpec.hdr_mode (i_mode (l_s L)) = false ->
  h_done (l_h L) = 1 -> R9.head_mem9 L |-- R8.head_mem8 L.
Proof.
  intros Hh Hm Hd. sep_apply (R9.head_mem9_passed L Hm Hd). unfold R8.head_mem8. rewrite Hh.
  apply sepcon_derives; [apply sepcon_derives; [apply sepcon_derives |] |]; try apply derives_refl.
  apply orp_right2. apply andp_right; [apply prop_right; exact Hm | apply derives_refl].
Qed.

(* after the call: out ++ ow written *)
Lemma cbytes_after9 n out ow : Zlength out + Zlength ow <= n ->
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
Lemma bufs_pre9 vs L u src ip pos out :
  isptr vs -> Zlength out <= Zlength (su_data u) ->
  iobj src ip * oobj u out
  |-- bufs_opt (is_live vs (Some L)) (ib9 src ip pos) (Some (ob9 u out)) [] true true.
Proof.
  intros Pv Hn. rewrite is_live_ptr9 by auto.
  unfold bufs_opt, in_rep, out_opt, out_rep, in_tok, out_tok, ib9, ob9, iobj, oobj.
  rewrite (cbytes_after9 _ out []) by (rewrite Zlength_nil; lia). rewrite app_nil_r.
  rewrite !bytes_i9, !tok_i9. cancel.
Qed.

Lemma bufs_post9 vs L u src ip pos out ow :
  isptr vs -> Zlength out + Zlength ow <= Zlength (su_data u) ->
  bufs_opt (is_live vs (Some L)) (ib9 src ip pos) (Some (ob9 u out)) ow true true
  |-- iobj src ip * oobj u (out ++ ow).
Proof.
  intros Pv Hn. rewrite is_live_ptr9 by auto.
  unfold bufs_opt, in_rep, out_opt, out_rep, in_tok, out_tok, ib9, ob9, iobj, oobj.
  rewrite (cbytes_after9 _ out ow) by lia.
  rewrite !bytes_i9, !tok_i9. cancel.
Qed.

Lemma in_ok9 O src ip pos take :
  src_ok O src -> isptr ip -> 0 <= pos -> 0 <= take -> pos + take <= Zlength src ->
  in_ok (ib9 src ip pos) (sublist pos (pos + take) src).
Proof.
  intros (Hs & _ & Bs) Pip Hp Ht Hpt.
  unfold in_ok, ib9.
  assert (Hl : Zlength (sublist pos (pos + take) src) = take) by (rewrite Zlength_sublist; lia).
  rewrite Hl. pose proof (Zlength_nonneg src).
  split; [auto | ]. split; [auto | ]. split; [lia | ]. split; [lia | ].
  split; [rewrite Zlength_map; reflexivity | ]. split; [unfold Zlib.proof.harness.rt_stream.UDFacts.max_size in *; rep_lia | ]. split.
  - unfold byte_vals. rewrite sublist_map. reflexivity.
  - apply Forall_sublist. eapply Forall_impl; [ | exact Bs]. simpl. intros; rep_lia.
Qed.

Lemma cbytes_len9 n l : Zlength l <= n -> Zlength (cbytes n l) = n.
Proof. intros H. unfold cbytes. rewrite Zlength_app, Zlength_map, Zlength_Zrepeat; lia. Qed.

Lemma out_ok9 u out ao :
  su_ok u -> 0 <= ao -> Zlength out + ao <= Zlength (su_data u) -> out_ok (ob9 u out) ao.
Proof.
  intros SU Ha Hao. pose proof SU as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hn & _) & _).
  pose proof SU as (_ & _ & _ & _ & _ & _ & _ & Pop & _).
  unfold out_ok, ob9. pose proof (Zlength_nonneg out).
  split; [apply writable_Ews | ]. unfold Zlib.proof.harness.rt_stream.UDFacts.max_size in *. repeat split; auto; try rep_lia.
  apply cbytes_len9; lia.
Qed.

(** ** The decompressor and at for position_of, unmoved and accounted *)

#[local] Instance CC_is9 : change_composite_env LS.CS_session Zlib.units.Inflate.CS.
  make_cs_preserve LS.CS_session Zlib.units.Inflate.CS. Defined.

(* a live stream between the calls, its struct at laws_session's compspecs *)
Lemma istream8_session gv shs p z L :
  R8.istream8 gv shs p z (Some L) =
  !! (zf_ok z /\ writable_share shs /\ R8.live_ok8 L) &&
  (@data_at LS.CS_session shs t_zs (LS.zs_of (zpos z) (zrest gv z (vl (zf_adler z)) (l_sp L))) p *
   state_mem gv p L).
Proof.
  unfold R8.istream8, zstrm_at, Zlib.proof.inflate.Rep.strm_rep.
  replace (@data_at Zlib.units.Inflate.CS shs Zlib.proof.inflate.Rep.t_strm _ p) with
    (@data_at LS.CS_session shs t_zs (LS.zs_of (zpos z) (zrest gv z (vl (zf_adler z)) (l_sp L))) p).
  - apply pred_ext; entailer!.
  - apply equal_f. apply (@data_at_change_composite _ _ CC_is9); [apply JMeq_refl | reflexivity].
Qed.

(* the decompressor's struct while main offers the buffers: next_in at pos in the input, next_out after the
   output out, avail_in ai, avail_out ao *)
Definition oS9 (gv : globals) (ip : val) (u : setup) (pos : Z) (out : list Z) (z : zfields) (L : live)
  (ai ao : val) : reptype t_z :=
  (offset_val pos ip, (ai, (vl (zf_tin z), (offset_val (Zlength out) (su_op u), (ao, (vl (zf_tout z),
   (msg_val gv (zf_msg z), (l_sp L, (gv Zlib.inflate.code._zcalloc, (gv Zlib.inflate.code._zcfree, (nullval,
   (vi (zf_dt z), (vl (zf_adler z), zf_res z))))))))))))).

(* the struct as main offered the buffers, at laws_session's compspecs *)
Lemma oS9_session gv ip u pos out z L ai ao vd :
  data_at Tsh t_z (oS9 gv ip u pos out z L (vi ai) (vi ao)) vd =
  @data_at LS.CS_session Tsh t_zs
    (LS.zs_of (opos9 ip u pos out z ai ao) (zrest gv z (vl (zf_adler z)) (l_sp L))) vd.
Proof. symmetry. cs_tac9 CC_session. Qed.

Lemma at_cs9 (va : val) : @data_at_ SCS.CS Tsh t_p va = @data_at_ LS.CS_session Tsh LS.t_pos va.
Proof. symmetry. apply equal_f. apply (@data_at__change_composite _ _ CC_session). reflexivity. Qed.

Lemma at_pos_cs9 (a : LS.posz) (va : val) :
  @data_at SCS.CS Tsh t_p (LS.pos_of a) va = @data_at LS.CS_session Tsh LS.t_pos (LS.pos_of a) va.
Proof. symmetry. cs_tac9 CC_session. Qed.

(* the position main records is well typed *)
Lemma opos9_ok ip u pos out z ai ao :
  isptr ip -> su_ok u -> zf_ok z -> 0 <= ai <= Int.max_unsigned -> 0 <= ao <= Int.max_unsigned ->
  LS.posz_ok (opos9 ip u pos out z ai ao).
Proof.
  intros Pip SU Zo Hi Ho. pose proof SU as (_ & _ & _ & _ & _ & _ & _ & Pop & _).
  unfold LS.posz_ok, opos9, zf_ok in *; simpl.
  destruct ip; try contradiction; destruct (su_op u); try contradiction. simpl. intuition.
Qed.

(* the bytes of a malloc'ed object of n bytes: p + k (0 <= k <= n) is weakly valid *)
Lemma obj_wv9 (n k : Z) (v : list val) (p : val) : 0 <= k <= n ->
  malloc_token Ews (tarray tuchar n) p * data_at Ews (tarray tuchar n) v p |-- weak_valid_pointer (offset_val k p).
Proof.
  intros Hk. assert_PROP (isptr p) as Pp by entailer!.
  destruct (Z.eq_dec n 0) as [E | E].
  - subst n. replace k with 0 by lia.
    replace (offset_val 0 p) with p by (destruct p; try contradiction; simpl; rewrite Ptrofs.add_zero; reflexivity).
    apply sepcon_weak_valid_pointer1. eapply derives_trans; [apply malloc_token_valid_pointer | apply valid_pointer_weak].
    simpl; lia.
  - apply sepcon_weak_valid_pointer2. sep_apply data_at_memory_block. simpl sizeof.
    apply memory_block_weak_valid_pointer; [rewrite Z.max_r by lia; lia | rewrite Z.max_r by lia; lia | ].
    apply readable_nonidentity, writable_readable, writable_Ews.
Qed.

(* the comparisons of unmoved and accounted: pointers into (or one past) the input and output objects, each
   compared with itself *)
Lemma objs_cmp9 (u : setup) (src out : list Z) (ip : val) (ki ko : Z) :
  isptr ip -> isptr (su_op u) -> 0 <= ki <= Zlength src -> 0 <= ko <= Zlength (su_data u) ->
  oobj u out * iobj src ip |--
  denote_tc_test_eq (offset_val ki ip) (offset_val ki ip) &&
  denote_tc_test_eq (offset_val ko (su_op u)) (offset_val ko (su_op u)).
Proof.
  intros Pi Po Hi Ho.
  unfold iobj, oobj.
  apply andp_right; (eapply derives_trans; [ | apply UK.test_eq_self; rewrite isptr_offset_val; assumption]).
  - apply sepcon_weak_valid_pointer2. apply obj_wv9. lia.
  - apply sepcon_weak_valid_pointer1. apply obj_wv9. lia.
Qed.

(* accounted's comparisons after a call: [acc_ok9] *)
Lemma acc_cmp9 (u : setup) (src out : list Z) (ip : val) l a :
  isptr ip -> isptr (su_op u) -> acc_ok9 src ip u l a ->
  oobj u out * iobj src ip |-- LS.accounted_cmp (zpos (il_z l)) a.
Proof.
  intros Pi Po (Hb & _ & _ & ki & ko & Hki & Hko & Ei & Eo).
  unfold LS.accounted_b in Hb. rewrite !andb_true_iff in Hb.
  destruct Hb as ((_ & Hbi) & (_ & Hbo)).
  unfold LS.ptr_eqb in Hbi, Hbo.
  destruct (Val.eq _ _) as [Ei' | ]; [ | discriminate]. destruct (Val.eq _ _) as [Eo' | ]; [ | discriminate].
  unfold LS.accounted_cmp. rewrite Ei', Eo', Ei, Eo.
  apply objs_cmp9; auto.
Qed.

(** ** The assertions of the loop's body *)
Section Assertions9.
Context (gv : globals) (vh vg vc va vd : val) (P : ses_iinv) (u : setup) (O : list Z) (c : cst)
  (src : list Z) (ip : val).

(* the temporaries in the loop (II_9's), with the flag asked *)
Definition i9_locals (asked : bool) : list localdef :=
  temp _asked (vi (Z.b2z asked)) ::
  temp _compressed_len (vl (Zlength O)) :: temp _after (vl (Zlength src - Zlength O)) ::
  temp _input ip :: c_locals u ++ d_locals u (rts_iw (su_wbits u)) ++ lvs gv vh vg vc va vd.

(* the state between the stores into avail_in and avail_out and the call, with the facts Q; [A] is the memory
   of at (any bytes before position_of, the recorded position after it) *)
Definition OI9 (Q : list Prop) (pos : Z) (out : list Z) (asked : bool) (z : zfields) (L : live) (ai ao : val)
  (A : mpred) : environ -> mpred :=
  PROPx Q
  (LOCALx (i9_locals asked)
  (SEPx [data_at Tsh t_z (oS9 gv ip u pos out z L ai ao) vd; state_mem gv vd L; R9.head_mem9 L; gtoks u;
         cstream gv vc (ghp vh u) c; mem_mgr gv; zfuncs gv; Rm gv; dobj u; cobj u O; oobj u out; A;
         iobj src ip; hobj vh u; dictobj u; dcopy u])).

(* after the call and its Z_MEM_ERROR test: inflate() returned r (Z_OK, Z_BUF_ERROR or Z_STREAM_END) with the
   stream l; the invariant after Z_OK and Z_BUF_ERROR, the end facts after Z_STREAM_END; at holds the position
   [a] recorded before the call: accounted holds of it, and offered neither input nor output space, the call did
   not return Z_OK and the stream is at [a] *)
Definition ICr9 (r : Z) (l : ils) (a : LS.posz) : environ -> mpred :=
  PROPx [su_ok u; with_head u = true; sc_ok (scase_of u) (su_data u) O; Zlength O <= su_cap u; rbytes O;
         il_mem9 u src ip l; got_at u vg (il_L l);
         r = Z_OK \/ r = Z_BUF_ERROR \/ r = Z_STREAM_END;
         r <> Z_STREAM_END -> il_ok P u O src ip l;
         r = Z_STREAM_END -> end9 u O l;
         LS.posz_ok a;
         LS.pz_avail_in a = 0 -> LS.pz_avail_out a = 0 -> r <> Z_OK /\ zpos (il_z l) = a;
         acc_ok9 src ip u l a; SIFacts.src_ok O src; isptr ip]
  (LOCALx (temp _code (vi r) :: i9_locals (il_asked l))
  (SEPx [R8.istream8 gv Tsh vd (il_z l) (Some (il_L l)); R9.head_mem9 (il_L l); gtoks u;
         cstream gv vc (ghp vh u) c; mem_mgr gv; zfuncs gv; Rm gv; dobj u; cobj u O; oobj u (il_out l);
         data_at Tsh t_p (LS.pos_of a) va; iobj src ip; hobj vh u; dictobj u; dcopy u])).

(* at the loop's test: as ICr9, at's contents no longer needed *)
Definition ICe9 (r : Z) (l : ils) : environ -> mpred :=
  PROPx [su_ok u; with_head u = true; sc_ok (scase_of u) (su_data u) O; Zlength O <= su_cap u; rbytes O;
         il_mem9 u src ip l; got_at u vg (il_L l);
         r = Z_OK \/ r = Z_BUF_ERROR \/ r = Z_STREAM_END;
         r <> Z_STREAM_END -> il_ok P u O src ip l;
         r = Z_STREAM_END -> end9 u O l;
         SIFacts.src_ok O src; isptr ip]
  (LOCALx (temp _code (vi r) :: i9_locals (il_asked l))
  (SEPx [R8.istream8 gv Tsh vd (il_z l) (Some (il_L l)); R9.head_mem9 (il_L l); gtoks u;
         cstream gv vc (ghp vh u) c; mem_mgr gv; zfuncs gv; Rm gv; dobj u; cobj u O; oobj u (il_out l);
         data_at_ Tsh t_p va; iobj src ip; hobj vh u; dictobj u; dcopy u])).

Definition IC9 : environ -> mpred := EX r : Z, EX l : ils, ICe9 r l.

(* the postcondition of the loop's body: IC9 at the test, IE_9 at the break, a return to main's postcondition *)
Definition RI9 : ret_assert :=
  loop1_ret_assert IC9
    (overridePost (EX z : zfields, EX L : live, IE_9 gv vh vg vc va vd u O c src ip z L)
       (overridePost (EX z : zfields, EX L : live, IE_9 gv vh vg vc va vd u O c src ip z L) POST_s)).

End Assertions9.

(** ** The loop's body cut into its parts *)

(* the body: offer avail_in (upto the input bytes left), offer avail_out (upto the room left),
   position_of(&decompressor, &at), the inflate() call with any flush, its Z_MEM_ERROR test, the test of the
   documented codes, the test of accounted, the test of a call offered neither input nor output space, and the
   Z_NEED_DICT branch *)
Definition bodyI9 : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [loopI] in
        (match loopI with Sloop b _ => b | s => s end) in exact x).
Definition incrI9 : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [loopI] in
        (match loopI with Sloop _ i => i | s => s end) in exact x).
Definition offerIn9 : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [bodyI9 first] in (first bodyI9) in exact x).
Definition offerOut9 : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [bodyI9 first suf] in (first (suf 1 bodyI9)) in exact x).
Definition posI9 : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [bodyI9 first suf] in (first (suf 2 bodyI9)) in exact x).
Definition callI9 : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [bodyI9 first suf] in (first (suf 3 bodyI9)) in exact x).
Definition memI9 : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [bodyI9 first suf] in (first (suf 4 bodyI9)) in exact x).
Definition codesI9 : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [bodyI9 first suf] in (first (suf 5 bodyI9)) in exact x).
Definition accI9 : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [bodyI9 first suf] in (first (suf 6 bodyI9)) in exact x).
Definition idleI9 : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [bodyI9 first suf] in (first (suf 7 bodyI9)) in exact x).
Definition needI9 : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [bodyI9 suf] in (suf 8 bodyI9) in exact x).

Lemma loopI9_parts :
  loopI = Sloop (Ssequence offerIn9 (Ssequence offerOut9 (Ssequence posI9 (Ssequence callI9
            (Ssequence memI9 (Ssequence codesI9 (Ssequence accI9 (Ssequence idleI9 needI9)))))))) incrI9.
Proof. reflexivity. Qed.

(** ** Tactics *)

(* VST's after_forward_call simplifies remove_localdef_temp with `simpl rlt_ident_eq`, which runs away on main's
   identifiers (_i against _input); each identifier comparison is decided by vm_compute instead. *)
Ltac rlt_fix9 u :=
  lazymatch u with
  | context C [rlt_ident_eq ?a ?b] =>
      let v := eval vm_compute in (rlt_ident_eq a b) in
      let u2 := context C [v] in rlt_fix9 u2
  | _ => u
  end.

Ltac simplify_remove_localdef_temp ::=
  match goal with |- context [remove_localdef_temp ?i ?L] =>
    let u := constr:(remove_localdef_temp i L) in
    let u' := eval lazy delta [remove_localdef_temp] beta iota in u in
    let u' := rlt_fix9 u' in
    let u' := eval lazy beta iota in u' in
    let u' := eval lazy zeta in u' in
    change u with u'
  end.

(* a branch that cannot be taken *)
Ltac infeas9 := exfalso; first [ match goal with H : ?a <> ?b |- _ => solve [apply H; reflexivity] end
                               | match goal with H : _ |- _ => solve [discriminate H] end
                               | contradiction
                               | match goal with H : Int.repr _ = Int.repr _ |- _ =>
                                   apply repr_inj_signed in H; [lia | rep_lia | rep_lia] end
                               | lia ].
(* `if (c) t = 1; else t = (expr);` with the value v of t known *)
Ltac ifk9 t v := match goal with |- semax _ (PROPx _ (LOCALx ?Q (SEPx ?R))) _ _ =>
  forward_if (PROPx [] (LOCALx (temp t (Vint (Int.repr v)) :: Q) (SEPx R))) end;
  [ first [infeas9 | forward; entailer!] | first [infeas9 | forward; entailer!] | ].

(* the side conditions of upto(m - (size_t) (p + k - p)) *)
Ltac upto_side9 := first
  [ unfold Zlib.proof.harness.rt_stream.UDFacts.max_size in *; rep_lia
  | entailer!; unfold Zlib.proof.harness.rt_stream.UDFacts.max_size in *;
    first [apply UK.sameblock_off; auto | unfold vl; rewrite UK.ptr_sub by (auto; rep_lia); reflexivity] ].

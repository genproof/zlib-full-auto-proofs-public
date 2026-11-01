(* Law rt_stream_trailing, main's inflate loop (TLoopI.v): one inflate() call in the model, the memory of a call,
   the assertions of the loop's body, and the tactics of the loop's proof.  rt_stream's kit (rt_stream/ULoopIKit.v)
   with the input object [iobj src ip] (the stream O, then any bytes) in place of compressed, and the facts of
   TIFacts.trl_ifacts.  The lemmas of rt_stream's kit that do not depend on rt_stream's main (the decompressor's
   struct, the output object, pointer arithmetic) are reused from it ([UK.]).

   After the test of the codes main checks gp_assert(accounted(&decompressor, &at)): the call moved next_in and
   next_out exactly as far as it lowered avail_in and avail_out.  [call_step_t] gives the counters of the call
   (next_in' = next_in + consumed, avail_in' = take - consumed, the same for the output), so that
   next_in' + avail_in' = ip + pos + take and next_out' + avail_out' = out + |out| + room: [acc_ok] states this for
   the position [a] main recorded, and [acc_cmp] lends the memory of the input and output objects in which these
   one-past-the-end pointers are comparable. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.SpecW.
Require Import Zlib.proof.harness.rt_stream.UDFacts.
Require Import Zlib.proof.harness.rt_stream.UIFacts.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.rt_stream.LawCS.
Require Import Zlib.proof.harness.rt_stream.UMainKit.
Require Import Zlib.proof.harness.rt_stream.ULoopIPos.
Require Zlib.proof.harness.rt_stream.ULoopIKit.
Require Import Zlib.proof.harness.rt_stream_trailing.TIFacts.
Require Import Zlib.proof.harness.rt_stream_trailing.TMainStmt.
Require Import Zlib.proof.harness.rt_stream_trailing.TMainKit.
Require Import Zlib.harness.rt_stream_trailing.code.
#[local] Existing Instance LawCS.CS.
Local Open Scope logic.
Module UK := Zlib.proof.harness.rt_stream.ULoopIKit.

(** ** One inflate() call in the model *)

(* the input object: src, offered from pos on *)
Definition ib_t (src : list Z) (ip : val) (pos : Z) : inbuf := InBuf Ews ip pos (Zlength src) (map vi src).

(* the position main records before the call: next_in at pos in the input, avail_in ai, next_out after the
   output out, avail_out ao, and the totals of z *)
Definition opos_t (ip : val) (u : setup) (pos : Z) (out : list Z) (z : zfields) (ai ao : Z) : LS.posz :=
  LS.mk_posz (offset_val pos ip) ai (zf_tin z) (offset_val (Zlength out) (su_op u)) ao (zf_tout z).

(* accounted(&decompressor, &at) after a call from the position [a]: it returns 1, and the two sums it compares
   are pointers into (or one past) the input object and the output object *)
Definition acc_ok (src : list Z) (ip : val) (u : setup) (l : ils) (a : LS.posz) : Prop :=
  LS.accounted_b (zpos (il_z l)) a = true /\ isptr (LS.pz_next_in a) /\ isptr (LS.pz_next_out a) /\
  exists ki ko, 0 <= ki <= Zlength src /\ 0 <= ko <= Zlength (su_data u) /\
    offset_val (LS.pz_avail_in a) (LS.pz_next_in a) = offset_val ki ip /\
    offset_val (LS.pz_avail_out a) (LS.pz_next_out a) = offset_val ko (su_op u).

Lemma offset_offset (p : val) (i j : Z) : offset_val j (offset_val i p) = offset_val (i + j) p.
Proof. rewrite offset_offset_val. reflexivity. Qed.

Lemma ptr_eqb_refl (p : val) : LS.ptr_eqb p p = true.
Proof. unfold LS.ptr_eqb. destruct (Val.eq p p); [reflexivity | congruence]. Qed.

(* a call that did not run out of memory: a documented code, and the invariant's facts at the new position
   (pos + bytes consumed) with the new output (out ++ bytes written); accounted holds of the position recorded
   before the call; offered neither input nor output space, not Z_OK and the stream's position unchanged *)
Lemma call_step_t P u O src ip l vd take room flush r z' st' ow :
  trl_ifacts P -> su_ok u -> isptr ip -> il_ok_t P u O src ip l -> live_ok (il_L l) ->
  zf_ok (il_z l) -> 0 <= take <= Int.max_unsigned -> il_pos l + take <= Zlength src ->
  0 <= room <= Zlength (su_data u) - Zlength (il_out l) -> room <= Int.max_unsigned -> isptr vd ->
  inflate_rel flush vd
    (UK.zoff (il_z l) (in_ptr (ib_t src ip (il_pos l)) 0) take (out_ptr (UK.ob_of u (il_out l)) 0) room)
    (Some (il_L l)) (ib_t src ip (il_pos l)) (sublist (il_pos l) (il_pos l + take) src)
    (Some (UK.ob_of u (il_out l))) r z' st' ow ->
  (forall L', st' = Some L' -> swfW (l_s L')) ->
  r <> Z_MEM_ERROR ->
  exists l', st' = Some (il_L l') /\ il_z l' = z' /\ il_out l' = il_out l ++ ow /\
    (r = Z_OK \/ r = Z_BUF_ERROR \/ r = Z_STREAM_END) /\
    Zlength (il_out l) + Zlength ow <= Zlength (su_data u) /\
    il_ok_t P u O src ip l' /\
    (r = Z_STREAM_END -> il_out l' = su_data u /\ il_pos l' = Zlength O) /\
    (take = 0 -> room = 0 -> r <> Z_OK /\ zpos z' = opos_t ip u (il_pos l) (il_out l) (il_z l) take room) /\
    acc_ok src ip u l' (opos_t ip u (il_pos l) (il_out l) (il_z l) take room).
Proof.
  intros PF SU Pip IL LO ZO Ht Hpt Hroom Hroom' Pvd REL Hsw' Hr.
  destruct l as [pos out L z]; simpl in *.
  destruct IL as (HP & Hsw & Hpos & (rest & Erest) & Eni & Eno).
  cbn [il_pos il_out il_L il_z] in *.
  pose proof SU as (_ & _ & _ & _ & Hn & _ & Hcap & _ & _ & Pop).
  destruct REL as [(Hbad & _) | (_ & L0 & o0 & res & winp & EL & Eo & Hrun & Hsnx & Er & Eow & Ez & _ & Est)].
  { exfalso. unfold inflate_bad, is_live in Hbad. destruct (eq_dec vd nullval) as [E|_]; [subst; contradiction | ].
    destruct Hbad as [H|[H|[H _]]]; discriminate. }
  injection EL as <-. injection Eo as <-.
  set (inp := sublist pos (pos + take) src) in *.
  assert (Hinp : Zlength inp = take) by (unfold inp; rewrite Zlength_sublist; lia).
  set (zo := UK.zoff z (in_ptr (ib_t src ip pos) 0) take (out_ptr (UK.ob_of u out) 0) room) in *.
  assert (HD : Zlength (su_data u) = Zlength out + Zlength rest) by (rewrite Erest, Zlength_app; lia).
  destruct (ti_call P PF (su_data u) O src pos out L zo inp flush res)
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
    pose proof (run2_inp _ _ _ _ _ Hrun) as Ei0. fold m in Ei0.
    exists (mkIL (pos + m_snx m) (out ++ ow) L' z'). simpl.
    split; [exact Est | ]. split; [reflexivity | ]. split; [reflexivity | ].
    split; [subst r; exact Hc | ]. split; [lia | ].
    split; [ | split; [ | split]].
    + unfold il_ok_t; simpl. subst z' ow. simpl.
      split; [exact HP' | ]. split; [exact (Hsw' L' Est) | ]. split; [lia | ].
      split; [exists rest'; rewrite <- app_assoc; exact Erest' | ].
      split; [reflexivity | ].
      simpl. f_equal. rewrite Zlength_app. fold m. lia.
    + intros E. subst r. destruct (Hend E) as (E1 & E2). subst ow. split; auto.
    + intros Ht0 Hr0.
      destruct (Hidle ltac:(lia) ltac:(unfold zo; simpl; exact Hr0)) as (Hok & Eow0 & Etin & Etout).
      assert (Es0 : m_snx m = 0) by lia.
      split; [subst r; exact Hok | ].
      subst z'. unfold zo, zpos, opos_t, z_after, ib_t, UK.ob_of. fold m. simpl.
      rewrite Etin, Etout, Es0, Hsow, Eow0, Ei0, Hao, Hinp. simpl.
      rewrite !Z.add_0_r, Zlength_nil, !Z.sub_0_r. reflexivity.
    + (* accounted: next_in' + avail_in' = ip + pos + take, next_out' + avail_out' = out + |out| + room *)
      subst z'. unfold acc_ok, zpos, opos_t, z_after, ib_t, UK.ob_of, LS.accounted_b. fold m.
      cbn [il_z zf_ni zf_ai zf_no zf_ao in_ptr out_ptr LS.pz_next_in LS.pz_avail_in LS.pz_next_out
           LS.pz_avail_out].
      rewrite Ei0, Hinp, Hao. unfold zo; cbn [UK.zoff zf_ao].
      rewrite !offset_offset.
      pose proof (Zlength_nonneg (m_ow m)).
      rewrite ?Z.add_0_r, ?Z.add_0_l.
      replace (pos + m_snx m + (take - m_snx m)) with (pos + take) by lia.
      replace (Zlength out + m_sow m + (room - m_sow m)) with (Zlength out + room) by lia.
      rewrite !ptr_eqb_refl.
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

(* the objects input and out as inflate()'s buffers, and back *)
Lemma bufs_pre_t vs L u src ip pos out :
  isptr vs -> Zlength out <= Zlength (su_data u) ->
  iobj src ip * oobj u out
  |-- bufs_opt (is_live vs (Some L)) (ib_t src ip pos) (Some (UK.ob_of u out)) [] true true.
Proof.
  intros Pv Hn. rewrite UK.is_live_ptr by auto.
  unfold bufs_opt, in_rep, out_opt, out_rep, in_tok, out_tok, ib_t, UK.ob_of, iobj, oobj.
  rewrite (UK.cbytes_after _ out []) by (rewrite Zlength_nil; lia). rewrite app_nil_r.
  rewrite !UK.bytes_i, !UK.tok_i. cancel.
Qed.

Lemma bufs_post_t vs L u src ip pos out ow :
  isptr vs -> Zlength out + Zlength ow <= Zlength (su_data u) ->
  bufs_opt (is_live vs (Some L)) (ib_t src ip pos) (Some (UK.ob_of u out)) ow true true
  |-- iobj src ip * oobj u (out ++ ow).
Proof.
  intros Pv Hn. rewrite UK.is_live_ptr by auto.
  unfold bufs_opt, in_rep, out_opt, out_rep, in_tok, out_tok, ib_t, UK.ob_of, iobj, oobj.
  rewrite (UK.cbytes_after _ out ow) by lia.
  rewrite !UK.bytes_i, !UK.tok_i. cancel.
Qed.

Lemma in_ok_t O src ip pos take :
  src_ok O src -> isptr ip -> 0 <= pos -> 0 <= take -> pos + take <= Zlength src ->
  in_ok (ib_t src ip pos) (sublist pos (pos + take) src).
Proof.
  intros (Hs & _ & Bs) Pip Hp Ht Hpt.
  unfold in_ok, ib_t.
  assert (Hl : Zlength (sublist pos (pos + take) src) = take) by (rewrite Zlength_sublist; lia).
  rewrite Hl. pose proof (Zlength_nonneg src).
  split; [auto | ]. split; [auto | ]. split; [lia | ]. split; [lia | ].
  split; [rewrite Zlength_map; reflexivity | ]. split; [unfold UDFacts.max_size in *; rep_lia | ]. split.
  - unfold byte_vals. rewrite sublist_map. reflexivity.
  - apply Forall_sublist. exact Bs.
Qed.

(* the comparisons of unmoved and accounted: pointers into (or one past) the input and output objects, each
   compared with itself *)
Lemma objs_cmp_t (u : setup) (src out : list Z) (ip : val) (ki ko : Z) :
  isptr ip -> isptr (su_op u) -> 0 <= ki <= Zlength src -> 0 <= ko <= Zlength (su_data u) ->
  oobj u out * iobj src ip |--
  denote_tc_test_eq (offset_val ki ip) (offset_val ki ip) &&
  denote_tc_test_eq (offset_val ko (su_op u)) (offset_val ko (su_op u)).
Proof.
  intros Pi Po Hi Ho.
  unfold iobj, oobj.
  apply andp_right; (eapply derives_trans; [ | apply UK.test_eq_self; rewrite isptr_offset_val; assumption]).
  - apply sepcon_weak_valid_pointer2. apply UK.obj_wv. lia.
  - apply sepcon_weak_valid_pointer1. apply UK.obj_wv. lia.
Qed.

(* accounted's comparisons after a call: [acc_ok] *)
Lemma acc_cmp (u : setup) (src out : list Z) (ip : val) l a :
  isptr ip -> isptr (su_op u) -> acc_ok src ip u l a ->
  oobj u out * iobj src ip |-- LS.accounted_cmp (zpos (il_z l)) a.
Proof.
  intros Pi Po (Hb & _ & _ & ki & ko & Hki & Hko & Ei & Eo).
  unfold LS.accounted_b in Hb. rewrite !andb_true_iff in Hb.
  destruct Hb as ((_ & Hbi) & (_ & Hbo)).
  unfold LS.ptr_eqb in Hbi, Hbo.
  destruct (Val.eq _ _) as [Ei' | ]; [ | discriminate]. destruct (Val.eq _ _) as [Eo' | ]; [ | discriminate].
  unfold LS.accounted_cmp. rewrite Ei', Eo', Ei, Eo.
  apply objs_cmp_t; auto.
Qed.

(** ** The loop *)

(* after the call and its Z_MEM_ERROR test: inflate() returned r (Z_OK, Z_BUF_ERROR or Z_STREAM_END), the
   invariant's facts hold at the new state, Z_STREAM_END came with all of O consumed and all the data produced,
   and at holds the position [a] recorded before the call: accounted holds of it, and offered neither input nor
   output space, the call did not return Z_OK and the stream is at [a] *)
Definition ICr_t (gv : globals) (vc vd va : val) (P : trl_iinv) (u : setup) (O : list Z) (c : cst)
  (src : list Z) (ip : val) (r : Z) (l : ils) (a : LS.posz) : environ -> mpred :=
  PROPx [su_ok u; Zlength O <= su_cap u; rbytes O; il_ok_t P u O src ip l;
        r = Z_OK \/ r = Z_BUF_ERROR \/ r = Z_STREAM_END;
        r = Z_STREAM_END -> il_out l = su_data u /\ il_pos l = Zlength O;
        LS.posz_ok a;
        LS.pz_avail_in a = 0 -> LS.pz_avail_out a = 0 -> r <> Z_OK /\ zpos (il_z l) = a;
        acc_ok src ip u l a; src_ok O src; isptr ip]
  (LOCALx (temp _code (vi r) :: temp _compressed_len (vl (Zlength O)) ::
           temp _after (vl (Zlength src - Zlength O)) :: temp _input ip ::
           su_locals u (rts_iw (su_wbits u)) ++ lv_locals gv vc vd va)
  (SEPx [istreamA gv Tsh vd (il_z l) Vundef (Some (il_L l)); head_opt (Some (il_L l));
        cstream gv vc c; mem_mgr gv; zfuncs gv; Rm_t gv; dobj u; cobj u O; oobj u (il_out l);
        @data_at LawCS.CS Tsh t_p (LS.pos_of a) va; iobj src ip])).

(* at the loop's test: as ICr_t, at's contents no longer needed *)
Definition ICe_t (gv : globals) (vc vd va : val) (P : trl_iinv) (u : setup) (O : list Z) (c : cst)
  (src : list Z) (ip : val) (r : Z) (l : ils) : environ -> mpred :=
  PROPx [su_ok u; Zlength O <= su_cap u; rbytes O; il_ok_t P u O src ip l;
        r = Z_OK \/ r = Z_BUF_ERROR \/ r = Z_STREAM_END;
        r = Z_STREAM_END -> il_out l = su_data u /\ il_pos l = Zlength O;
        src_ok O src; isptr ip]
  (LOCALx (temp _code (vi r) :: temp _compressed_len (vl (Zlength O)) ::
           temp _after (vl (Zlength src - Zlength O)) :: temp _input ip ::
           su_locals u (rts_iw (su_wbits u)) ++ lv_locals gv vc vd va)
  (SEPx [istreamA gv Tsh vd (il_z l) Vundef (Some (il_L l)); head_opt (Some (il_L l));
        cstream gv vc c; mem_mgr gv; zfuncs gv; Rm_t gv; dobj u; cobj u O; oobj u (il_out l);
        data_at_ Tsh t_p va; iobj src ip])).

Definition IC_t (gv : globals) (vc vd va : val) (P : trl_iinv) (u : setup) (O : list Z) (c : cst)
  (src : list Z) (ip : val) : environ -> mpred :=
  EX r : Z, EX l : ils, ICe_t gv vc vd va P u O c src ip r l.

(* the postcondition of the loop's body: IC_t at the test, IE_t at the break, a return to main's postcondition *)
Definition RI_t (gv : globals) (vc vd va : val) (P : trl_iinv) (u : setup) (O : list Z) (c : cst)
  (src : list Z) (ip : val) : ret_assert :=
  loop1_ret_assert (IC_t gv vc vd va P u O c src ip)
    (overridePost (EX z : zfields, EX L : live, IE_t gv vc vd va u O c src ip z L)
       (overridePost (EX z : zfields, EX L : live, IE_t gv vc vd va u O c src ip z L) POST_t)).

(** ** The loop's body cut into its parts *)

(* the body: offer avail_in (upto the input bytes left), offer avail_out (upto the room left),
   position_of(&decompressor, &at), the inflate() call with any flush, its Z_MEM_ERROR test, the test of the
   documented codes, the test of accounted, and the test of a call offered neither input nor output space *)
Definition bodyI_t : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [loopI_t] in
        (match loopI_t with Sloop b _ => b | s => s end) in exact x).
Definition incrI_t : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [loopI_t] in
        (match loopI_t with Sloop _ i => i | s => s end) in exact x).
Definition offerIn_t : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [bodyI_t first] in (first bodyI_t) in exact x).
Definition offerOut_t : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [bodyI_t first suf] in (first (suf 1 bodyI_t)) in exact x).
Definition posI_t : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [bodyI_t first suf] in (first (suf 2 bodyI_t)) in exact x).
Definition callI_t : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [bodyI_t first suf] in (first (suf 3 bodyI_t)) in exact x).
Definition memI_t : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [bodyI_t first suf] in (first (suf 4 bodyI_t)) in exact x).
Definition codesI_t : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [bodyI_t first suf] in (first (suf 5 bodyI_t)) in exact x).
Definition accI_t : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [bodyI_t first suf] in (first (suf 6 bodyI_t)) in exact x).
Definition idleI_t : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [bodyI_t suf] in (suf 7 bodyI_t) in exact x).

Lemma loopI_t_parts :
  loopI_t = Sloop (Ssequence offerIn_t (Ssequence offerOut_t (Ssequence posI_t (Ssequence callI_t
              (Ssequence memI_t (Ssequence codesI_t (Ssequence accI_t idleI_t))))))) incrI_t.
Proof. reflexivity. Qed.

(* the decompressor's struct while main offers the buffers: next_in at pos in the input, next_out after the
   output out, avail_in ai, avail_out ao *)
Definition oS_t (gv : globals) (ip : val) (u : setup) (pos : Z) (out : list Z) (z : zfields) (L : live)
  (ai ao : val) : reptype t_z :=
  (offset_val pos ip, (ai, (vl (zf_tin z), (offset_val (Zlength out) (su_op u), (ao, (vl (zf_tout z),
   (msg_val gv (zf_msg z), (l_sp L, (gv Zlib.inflate.code._zcalloc, (gv Zlib.inflate.code._zcfree, (nullval,
   (vi (zf_dt z), (adler_v (raw_live (Some L)) z Vundef, zf_res z))))))))))))).

(* the state between the stores into avail_in and avail_out and the call, with the facts Q; [A] is the memory
   of at (any bytes before position_of, the recorded position after it) *)
Definition OI_t (Q : list Prop) (gv : globals) (vc vd va : val) (u : setup) (O : list Z) (c : cst)
  (src : list Z) (ip : val) (pos : Z) (out : list Z) (z : zfields) (L : live) (ai ao : val) (A : mpred)
  : environ -> mpred :=
  PROPx Q
  (LOCALx (temp _compressed_len (vl (Zlength O)) :: temp _after (vl (Zlength src - Zlength O)) ::
           temp _input ip :: su_locals u (rts_iw (su_wbits u)) ++ lv_locals gv vc vd va)
  (SEPx [data_at Tsh t_z (oS_t gv ip u pos out z L ai ao) vd; state_mem gv vd L; head_opt (Some L);
        cstream gv vc c; mem_mgr gv; zfuncs gv; Rm_t gv; dobj u; cobj u O; oobj u out; A; iobj src ip])).

(** ** The decompressor and at for position_of, unmoved and accounted *)

(* the struct as main offered the buffers, at laws_session's compspecs *)
Lemma oS_t_session gv ip u pos out z L ai ao vd :
  data_at Tsh t_z (oS_t gv ip u pos out z L (vi ai) (vi ao)) vd =
  @data_at LS.CS_session Tsh t_zs
    (LS.zs_of (opos_t ip u pos out z ai ao) (zrest gv z (adler_v (raw_live (Some L)) z Vundef) (l_sp L))) vd.
Proof. symmetry. UK.cs_tac CC_session. Qed.

(* the position main records is well typed *)
Lemma opos_t_ok ip u pos out z ai ao :
  isptr ip -> su_ok u -> zf_ok z -> 0 <= ai <= Int.max_unsigned -> 0 <= ao <= Int.max_unsigned ->
  LS.posz_ok (opos_t ip u pos out z ai ao).
Proof.
  intros Pip SU Zo Hi Ho. destruct SU as (_ & _ & _ & _ & _ & _ & _ & _ & Pcp & Pop).
  unfold LS.posz_ok, opos_t, zf_ok in *; simpl.
  destruct ip; try contradiction; destruct (su_op u); try contradiction. simpl. intuition.
Qed.

(* VST's after_forward_call simplifies remove_localdef_temp with `simpl rlt_ident_eq`, which runs away on main's
   identifiers (_i against _input); each identifier comparison is decided by vm_compute instead. *)
Ltac rlt_fix u :=
  lazymatch u with
  | context C [rlt_ident_eq ?a ?b] =>
      let v := eval vm_compute in (rlt_ident_eq a b) in
      let u2 := context C [v] in rlt_fix u2
  | _ => u
  end.

Ltac simplify_remove_localdef_temp ::=
  match goal with |- context [remove_localdef_temp ?i ?L] =>
    let u := constr:(remove_localdef_temp i L) in
    let u' := eval lazy delta [remove_localdef_temp] beta iota in u in
    let u' := rlt_fix u' in
    let u' := eval lazy beta iota in u' in
    let u' := eval lazy zeta in u' in
    change u with u'
  end.

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
    first [apply UK.sameblock_off; auto | unfold vl; rewrite UK.ptr_sub by (auto; rep_lia); reflexivity] ].

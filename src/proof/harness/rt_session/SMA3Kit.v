(* Law rt_session (harness/rt_session.c), main's statements 47-56 (SMKit.segA3): the cut of the segment, the state
   between its statements and the memory lemmas.

   segA3 is new_stream(&compressor), deflateInit2_ and its two tests (statements 47-50, SMSegA3.v), the
   dictionary (51, SMA3Dict.v), the header (52, SMA3Head.v) and the stores before the deflate loop (53-56,
   SMA3Stores.v).  Between these statements main's state is [AS]: the compressor holds a live state on which
   the deflate invariant J holds with no data consumed and no output yet, for the dictionary [dict] and the header
   [gh] set so far, the state's gzhead pointer is [ghp]; the caller's fields of the compressor are any, except
   next_in and next_out (Z_NULL, as new_stream left them).  [Hd] is what main keeps of head: head itself before
   deflateSetHeader, the header part of the state and the rest of head after it ([Ph]: they give head back). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.deflate.DSpec9.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.rt_session.SCS.
Require Import Zlib.proof.harness.rt_session.SDFacts.
Require Import Zlib.proof.harness.rt_session.SMainStmt.
Require Import Zlib.proof.harness.rt_session.SMKit.
Require Import Zlib.harness.rt_session.code.
Require Zlib.deflate.code.
#[local] Existing Instance SCS.CS.
Local Open Scope logic.

Module DC := Zlib.deflate.code.

(** ** The cut points of segA3 *)
(* from statement 51 (the dictionary), 52 (the header) and 53 (the stores) on *)
Definition segA3_dict : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [suf segA3] in (suf 4 segA3) in exact x).
Definition segA3_head : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [suf segA3] in (suf 5 segA3) in exact x).
Definition segA3_stores : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [suf segA3] in (suf 6 segA3) in exact x).

(** ** The state between the statements *)
Section State.
Context (gv : globals) (vh vg vc va vd : val).

Definition AS (J : ses_dinv) (u : setup) (dict : list Z) (gh : option DS7.gzh) (ghp : val) (c : cst)
    (msg : option Z) (Ph : Prop) (Hd : list mpred) : environ -> mpred :=
  PROPx [su_ok u; J (su_wbits u) dict gh [] [] None (cs_s c) (cs_tin c) (cs_tout c) (cs_adler c);
         msg_ok msg (cs_msgv c); cs_ni c = nullval; cs_no c = nullval; Ph]
  (LOCALx (c_locals u ++ d_locals u (su_wbits u) ++ lvs gv vh vg vc va vd)
  (SEPx ([cstream gv vc ghp c; data_at_ Tsh t_z vd; mem_mgr gv; Rm gv; dobj u; cobj u []; oobj u [];
          data_at_ Tsh t_p va] ++ Hd ++ [graw vg u; dictobj u; dcopy u]))).

(* the postcondition of the parts after statement 50 (they do not return) *)
Definition POST_A3 (J : ses_dinv) (u : setup) : ret_assert :=
  normal_ret_assert (EX l : dls, EX hx : share * val * val * val, EX Hr : mpred,
                       DI gv vh vg vc va vd J u l hx Hr).

End State.

(* the three continuations *)
Definition a3_dict_stmt : Prop :=
  forall {Espec : OracleKind} J gv vh vg vc va vd u c msg, ses_dfacts J ->
  semax Delta_s (AS gv vh vg vc va vd J u [] None nullval c msg True [hobj vh u]) segA3_dict
    (POST_A3 gv vh vg vc va vd J u).

Definition a3_head_stmt : Prop :=
  forall {Espec : OracleKind} J gv vh vg vc va vd u c msg, ses_dfacts J ->
  semax Delta_s (AS gv vh vg vc va vd J u (sdict u) None nullval c msg True [hobj vh u]) segA3_head
    (POST_A3 gv vh vg vc va vd J u).

Definition a3_stores_stmt : Prop :=
  forall {Espec : OracleKind} J gv vh vg vc va vd u c msg hx Hr, ses_dfacts J ->
  semax Delta_s
    (AS gv vh vg vc va vd J u (sdict u) (sgh u) (ghp vh u) c msg (hclose vh u (cs_s c) hx Hr)
       [hdr_at (Some (cs_s c)) (ghp vh u) hx; Hr]) segA3_stores
    (POST_A3 gv vh vg vc va vd J u).

(** ** Facts on the setup *)

Lemma with_dict_wrap (u : setup) : with_dict u = true -> rwrap_of (su_wbits u) <> 2.
Proof.
  unfold with_dict, rwrap_of. intros H. apply andb_prop in H as [H _]. apply Z.leb_le in H.
  destruct (su_wbits u <? 0); [discriminate | ]. destruct (su_wbits u >? 15) eqn:E; [ | discriminate].
  apply Z.gtb_lt in E. lia.
Qed.

Lemma with_head_wrap (u : setup) : with_head u = true -> rwrap_of (su_wbits u) = 2.
Proof.
  unfold with_head, rwrap_of. intros H. apply andb_prop in H as [H _]. apply Z.ltb_lt in H.
  destruct (su_wbits u <? 0) eqn:E; [apply Z.ltb_lt in E; lia | ].
  replace (su_wbits u >? 15) with true by (symmetry; apply Z.gtb_lt; lia). reflexivity.
Qed.

Lemma with_dict_head (u : setup) : with_dict u = true -> with_head u = false.
Proof.
  unfold with_dict, with_head. intros H. apply andb_prop in H as [H _]. apply Z.leb_le in H.
  replace (15 <? su_wbits u) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Lemma nz_bytes0 (l : list Z) : nzbytes l -> Forall (fun x => 0 <= x < 256) (l ++ [0]).
Proof.
  intros H. apply Forall_app. split; [ | constructor; [lia | constructor]].
  eapply Forall_impl; [ | exact H]. intros; simpl in *; lia.
Qed.

(* the header main gives deflateSetHeader is one deflate accepts (RTK7.rhdr_ok7) and gzh_at holds *)
Lemma gh_of_ok7 (u : setup) : su_ok u -> rhdr_ok7 (gh_of u).
Proof.
  intros ((_ & _ & _ & _ & _ & _ & _ & _ & Hxl & Hxb & Hnl & Hnb & Hcl & Hcb & _ & _ & _ & Htx & Htm & Hos & Hhc & _) & _).
  unfold rhdr_ok7, gh_of, selo; cbn [DS7.gz_text DS7.gz_hcrc DS7.gz_os DS7.gz_time DS7.gz_extra_len DS7.gz_extra
    DS7.gz_name DS7.gz_comment].
  split; [exact Htx | ]. split; [exact Hhc | ]. split; [exact Hos | ]. split; [lia | ].
  split; [split; [apply Zlength_nonneg | lia] | ].
  split; [intros x Hx; destruct (has u 2); inversion Hx; subst; split; [reflexivity | exact Hxb] | ].
  split; intros x Hx; [destruct (has u 4) | destruct (has u 8)]; inversion Hx; subst; eexists; split; eauto.
Qed.

Lemma gh_of_gzh (u : setup) : su_ok u -> gzh_ok (gh_of u).
Proof.
  intros ((_ & _ & _ & _ & _ & _ & _ & _ & Hxl & _ & _ & _ & _ & _ & _ & _ & _ & Htx & Htm & Hos & Hhc & _) & _).
  unfold gzh_ok, gh_of, rs32 in *; cbn. pose proof (Zlength_nonneg (su_xf u)). rep_lia.
Qed.

(** ** The local compressor *)

(* laws_common's new_stream sees the compressor at the compress unit's compspecs *)
Lemma a3_cs_compress sh (v : @reptype Zlib.units.Compress.CS t_zs) (p : val) :
  @data_at Zlib.units.Compress.CS sh t_zs v p = @data_at CS sh t_z v p.
Proof.
  apply equal_f. apply (@data_at_change_composite _ _ CC_compress); [apply JMeq_refl | reflexivity].
Qed.

(* the uninitialized Ews part of the local as new_stream's precondition *)
Lemma a3_strm_undef (p : val) :
  data_at_ Ews t_z p |--
  @data_at Zlib.units.Compress.CS Ews t_zs
    (zs_val Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef) p.
Proof. rewrite a3_cs_compress. apply derives_refl. Qed.

(* the Ews part back at main's compspecs, and the complement: the local *)
Lemma a3_rejoin (p : val) :
  @data_at_ Zlib.proof.deflate.DCS.CS Ews t_strm p * data_at_ BoundKit.Ecomp t_z p |-- data_at_ Tsh t_z p.
Proof.
  rewrite (@data_at__change_composite Zlib.proof.deflate.DCS.CS CS CC_dcs Ews t_strm) by reflexivity.
  rewrite (BoundKit.data_at__Tsh_split t_z p). cancel.
Qed.

(* the fields next_in and next_out of the compressor, as deflate.c's specifications hold them and as main stores
   into them *)
Lemma a3_next_in_cs (v : val) (p : val) :
  @field_at Zlib.proof.deflate.DCS.CS Ews t_strm (DOT DC._next_in) v p = @field_at CS Ews t_z (DOT _next_in) v p.
Proof. apply equal_f. apply (@field_at_change_composite _ _ CC_dcs); [apply JMeq_refl | reflexivity]. Qed.

Lemma a3_next_out_cs (v : val) (p : val) :
  @field_at Zlib.proof.deflate.DCS.CS Ews t_strm (DOT DC._next_out) v p = @field_at CS Ews t_z (DOT _next_out) v p.
Proof. apply equal_f. apply (@field_at_change_composite _ _ CC_dcs); [apply JMeq_refl | reflexivity]. Qed.

(* the harness's ZLIB_VERSION literal as deflateInit2_'s version argument *)
Lemma a3_version gv :
  Zlib.proof.deflate.GlobalsInit.version_at gv ___stringlit_rt_session_1 =
  @data_at Zlib.proof.deflate.DCS.CS Ers (tarray tschar (Zlength [49; 46; 51; 46; 50; 0]))
    (map vi [49; 46; 51; 46; 50; 0]) (gv ___stringlit_rt_session_1).
Proof. reflexivity. Qed.

(* deflateSetHeader takes strm->next_in apart from the caller's other fields *)
Definition af_rest (sp : val) (ain tin : Z) (nout : val) (aout tout : Z) (msgv : val) (adler : Z) : mpred :=
  !! (u32_ok ain /\ u64_ok tin /\ u32_ok aout /\ u64_ok tout /\ u64_ok adler) &&
  (@field_at Zlib.proof.deflate.DCS.CS Ews t_strm (DOT DC._avail_in) (vi ain) sp *
   @field_at Zlib.proof.deflate.DCS.CS Ews t_strm (DOT DC._total_in) (vl tin) sp *
   @field_at Zlib.proof.deflate.DCS.CS Ews t_strm (DOT DC._next_out) nout sp *
   @field_at Zlib.proof.deflate.DCS.CS Ews t_strm (DOT DC._avail_out) (vi aout) sp *
   @field_at Zlib.proof.deflate.DCS.CS Ews t_strm (DOT DC._total_out) (vl tout) sp *
   @field_at Zlib.proof.deflate.DCS.CS Ews t_strm (DOT DC._msg) msgv sp *
   @field_at Zlib.proof.deflate.DCS.CS Ews t_strm (DOT DC._adler) (vl adler) sp).

Lemma af_split (sp nin : val) (ain tin : Z) (nout : val) (aout tout : Z) (msgv : val) (adler : Z) :
  api_fields sp nin ain tin nout aout tout msgv adler =
  @field_at Zlib.proof.deflate.DCS.CS Ews t_strm (DOT DC._next_in) nin sp *
  af_rest sp ain tin nout aout tout msgv adler.
Proof. unfold api_fields, af_rest. apply pred_ext; entailer!. Qed.

(** ** head while deflate holds it *)

(* the objects at main's compspecs are deflate's objects *)
Lemma bobj_obj (q : val) (l : list Z) : bobj q l = BoundKit.obj q l.
Proof.
  unfold bobj, BoundKit.obj.
  erewrite (@malloc_token_change_composite Zlib.proof.deflate.DCS.CS CS CC_dcs) by reflexivity.
  erewrite (@data_at_change_composite Zlib.proof.deflate.DCS.CS CS CC_dcs); [ reflexivity | apply JMeq_refl | reflexivity ].
Qed.

(* what the selected object of head does not hand to deflate: its token, or the whole object if the field
   is absent *)
Definition sel_rest (u : setup) (m : Z) (q : val) (l : list Z) : mpred :=
  if has u m then BoundKit.obj_rest q l else bobj q l.

Lemma bobj_sel (u : setup) (m : Z) (q : val) (l : list Z) :
  Forall (fun x => 0 <= x < 256) l -> bobj q l = opt_obj Ews (selo u m l) (selp u m q) * sel_rest u m q l.
Proof.
  intros HB. unfold selo, selp, sel_rest. destruct (has u m).
  - rewrite bobj_obj. apply BoundKit.obj_opt_obj. exact HB.
  - unfold opt_obj. apply pred_ext; entailer!.
Qed.

(* what deflate does not hold of head's objects, and the copies *)
Definition hrest (u : setup) : mpred :=
  sel_rest u 2 (su_xp u) (su_xf u) * sel_rest u 4 (su_np u) (su_nm u ++ [0]) *
  sel_rest u 8 (su_cmp u) (su_cm u ++ [0]) * hcopies u.

(* head's fields at deflate's compspecs *)
Definition hval_d (u : setup) : @reptype Zlib.proof.deflate.DCS.CS t_gzh :=
  (vi (su_text u), (vl (su_time u), (Vundef, (vi (su_os u), (selp u 2 (su_xp u), (vi (Zlength (su_xf u)),
   (Vundef, (selp u 4 (su_np u), (Vundef, (selp u 8 (su_cmp u), (Vundef, (vi (su_hcrc u), Vundef)))))))))))).

Lemma head_cs (u : setup) (vh : val) :
  data_at Ews t_g (hvals u) vh = @data_at Zlib.proof.deflate.DCS.CS Ews t_gzh (hval_d u) vh.
Proof.
  erewrite (@data_at_change_composite Zlib.proof.deflate.DCS.CS CS CC_dcs Ews t_gzh (hval_d u));
    [ reflexivity | apply JMeq_refl | reflexivity ].
Qed.

Definition hx_of (u : setup) : share * val * val * val :=
  (Ews, selp u 2 (su_xp u), selp u 4 (su_np u), selp u 8 (su_cmp u)).

(* head while deflate holds it: the complement of Ews of the struct, its padding and what deflate does not hold
   of the three objects *)
Definition Hr_of (u : setup) (vh : val) : mpred :=
  data_at BoundKit.Ecomp t_g (hvals u) vh * BoundKit.gzh_pad vh * hrest u.

(* head's Ews part and its three objects hold the header gh_of u (the absent objects stay with main) *)
Lemma head_to_gzh (u : setup) (vh : val) : su_ok u ->
  @data_at Zlib.proof.deflate.DCS.CS Ews t_gzh (hval_d u) vh * hobjs u
  |-- gzh_at Ews (gh_of u) vh (selp u 2 (su_xp u)) (selp u 4 (su_np u)) (selp u 8 (su_cmp u)) *
      BoundKit.gzh_pad vh * hrest u.
Proof.
  intros OK. pose proof OK as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & Bx & _ & Bn & _ & Bc & _) & _).
  unfold hobjs, hrest.
  rewrite (bobj_sel u 2 (su_xp u) (su_xf u) Bx), (bobj_sel u 4 (su_np u) _ (nz_bytes0 _ Bn)),
    (bobj_sel u 8 (su_cmp u) _ (nz_bytes0 _ Bc)).
  sep_apply (BoundKit.gzh_of_stores (gh_of u) vh (selp u 2 (su_xp u)) (selp u 4 (su_np u)) (selp u 8 (su_cmp u))
    Vundef Vundef Vundef Vundef Vundef (gh_of_gzh u OK)).
  cancel.
Qed.

(* and back, whatever deflate left in the fields gzh_at does not fix (main never wrote them) *)
Lemma gzh_to_head (u : setup) (vh : val) : su_ok u ->
  gzh_at Ews (gh_of u) vh (selp u 2 (su_xp u)) (selp u 4 (su_np u)) (selp u 8 (su_cmp u)) *
  BoundKit.gzh_pad vh * hrest u
  |-- @data_at Zlib.proof.deflate.DCS.CS Ews t_gzh (hval_d u) vh * hobjs u.
Proof.
  intros OK. pose proof OK as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & Bx & _ & Bn & _ & Bc & _) & _).
  unfold hobjs, hrest.
  rewrite (bobj_sel u 2 (su_xp u) (su_xf u) Bx), (bobj_sel u 4 (su_np u) _ (nz_bytes0 _ Bn)),
    (bobj_sel u 8 (su_cmp u) _ (nz_bytes0 _ Bc)).
  unfold gzh_at, BoundKit.gzh_pad. Intros v1 v2 v3 v4 v5.
  unfold_data_at (@data_at Zlib.proof.deflate.DCS.CS _ _ _ vh). unfold hval_d. cbn [fst snd].
  cancel. apply derives_refl.
Qed.

(* head (Tsh) and its objects: what deflateSetHeader takes, and the rest *)
Lemma head_open (u : setup) (vh : val) : su_ok u ->
  hobj vh u
  |-- gzh_at Ews (gh_of u) vh (selp u 2 (su_xp u)) (selp u 4 (su_np u)) (selp u 8 (su_cmp u)) * Hr_of u vh.
Proof.
  intros OK. unfold hobj. rewrite <- (data_at_share_join Ews BoundKit.Ecomp Tsh _ _ _ BoundKit.join_Ews_Ecomp).
  rewrite head_cs. unfold Hr_of. sep_apply (head_to_gzh u vh OK). cancel.
Qed.

(* with a header: head comes back while the state keeps the header *)
Lemma head_close (u : setup) (vh : val) (s : dstate) :
  su_ok u -> with_head u = true -> d_gzhead s = Some (gh_of u) -> hclose vh u s (hx_of u) (Hr_of u vh).
Proof.
  intros OK W E s' E'. unfold hdr_at, hx_of, ghp. rewrite E', E, W.
  unfold Hr_of, hobj. sep_apply (gzh_to_head u vh OK). rewrite <- head_cs.
  rewrite <- (data_at_share_join Ews BoundKit.Ecomp Tsh _ _ _ BoundKit.join_Ews_Ecomp). cancel.
Qed.

(* without a header: the state's gzhead is Z_NULL, head stays with main *)
Lemma head_none (u : setup) (vh : val) (s : dstate) (hx : share * val * val * val) :
  with_head u = false -> d_gzhead s = None -> hclose vh u s hx (hobj vh u).
Proof.
  intros W E s' E'. unfold hdr_at, ghp. rewrite E', E, W. entailer!.
Qed.

Lemma hdr_none (u : setup) (vh : val) (s : dstate) (hx : share * val * val * val) :
  with_head u = false -> d_gzhead s = None -> hdr_at (Some s) (ghp vh u) hx = emp.
Proof.
  intros W E. unfold hdr_at, ghp. rewrite E, W. apply pred_ext; entailer!.
Qed.

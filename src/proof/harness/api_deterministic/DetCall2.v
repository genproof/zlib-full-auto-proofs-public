(* Law api_deterministic (data of any length): deflate on both streams (DetKit2.det_call_stmt): the same model run (DetFacts2.df2_deflate),
   so the same state, fields, code and output. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Rep.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.deflate.DSpec9.
Require Import Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.deflate.DetFacts2.
Require Zlib.proof.deflate.DModel5.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.api_deterministic.DetCS2.
Require Import Zlib.proof.harness.api_deterministic.DetMainStmt2.
Require Import Zlib.proof.harness.api_deterministic.DetKit2.
Require Import Zlib.harness.api_deterministic.code.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.

(** ** The output space of one stream at deflate's call

    deflate gets the output space after the [O] bytes already written: [room - |O|] bytes at
    [offset_val |O| q], and, when there are none, a witness that this pointer is weakly valid: for an empty
    object the object's malloc token, for a full one its last byte (DSpec.wv_at).  [ohead] is what is left of
    the object: its token (unless lent as the witness) and the written bytes (but the last one if lent). *)
Definition owit (room : Z) (O : list Z) : wvw :=
  if room =? 0 then WVtok (tarray tuchar 0)
  else if Zlength O =? room then WVbefore Ews (vi (Znth (room - 1) O)) else WVnone.

Definition ohead (q : val) (room : Z) (O : list Z) : mpred :=
  (if room =? 0 then emp else malloc_token Ews (tarray tuchar room) q) *
  (if andb (room >? 0) (Zlength O =? room)
   then data_at Ews (tarray tuchar (room - 1)) (map vi (sublist 0 (room - 1) O)) q
   else data_at Ews (tarray tuchar (Zlength O)) (map vi O) q).

Lemma owit_ok (room : Z) (O : list Z) : 0 <= room -> room - Zlength O = 0 -> wv_ok (owit room O).
Proof.
  intros H0 H1. unfold owit. destruct (room =? 0) eqn:E; [simpl; lia |].
  rewrite (proj2 (Z.eqb_eq _ _)) by lia. simpl. auto.
Qed.

(* the object as the part kept and the part given to deflate, whatever the latter's contents [L] *)
Lemma out_split (q : val) (room : Z) (O : list Z) (L : list val) :
  0 <= Zlength O <= room -> Zlength L = room - Zlength O -> field_compatible (tarray tuchar room) [] q ->
  out_at q room (map vi O ++ L) =
  ohead q room O * data_at Ews (tarray tuchar (room - Zlength O)) L (offset_val (Zlength O) q) *
  wv_at (owit room O) (offset_val (Zlength O) q).
Proof.
  intros HO HL FC. unfold out_at, ohead, owit, wv_at.
  rewrite (split2_data_at_Tarray_app (Zlength O)); [| rewrite Zlength_map; reflexivity | exact HL].
  rewrite arr_field_address0 by (auto; lia). change (sizeof tuchar) with 1. rewrite Z.mul_1_l.
  assert (Hp : isptr q) by (destruct FC; auto).
  destruct (room =? 0) eqn:E0.
  - apply Z.eqb_eq in E0. subst room.
    assert (Zlength O = 0) by lia. rewrite H. rewrite isptr_offset_val_zero by auto.
    simpl. rewrite emp_sepcon. apply pred_ext; cancel.
  - apply Z.eqb_neq in E0.
    destruct (Zlength O =? room) eqn:E1.
    + apply Z.eqb_eq in E1. rewrite (proj2 (Z.gtb_lt _ _)) by lia. simpl andb. cbv iota.
      rewrite E1.
      assert (Hs : map vi O = map vi (sublist 0 (room - 1) O) ++ map vi (sublist (room - 1) room O)).
      { rewrite <- map_app, <- sublist_split by lia. rewrite sublist_same by lia. reflexivity. }
      rewrite Hs.
      rewrite (split2_data_at_Tarray_app (room - 1)) by (rewrite ?Zlength_map, ?Zlength_sublist; lia).
      replace (sublist (room - 1) room O) with [Znth (room - 1) O]
        by (rewrite <- sublist_len_1 by lia; f_equal; lia).
      replace (room - (room - 1)) with 1 by lia.
      rewrite arr_field_address0 by (auto; lia). change (sizeof tuchar) with 1. rewrite Z.mul_1_l.
      simpl map. rewrite (data_at_singleton_array_eq _ tuchar (vi (Znth (room - 1) O))) by reflexivity.
      rewrite offset_offset_val. replace (room + -1) with (room - 1) by lia.
      apply pred_ext; cancel.
    + rewrite andb_false_r. rewrite sepcon_emp. apply pred_ext; cancel.
Qed.

(* after the call: [zo] written at the start of the part given to deflate *)
Lemma out_join (q : val) (room : Z) (O zo : list Z) :
  Zlength O + Zlength zo <= room -> field_compatible (tarray tuchar room) [] q ->
  ohead q room O *
  data_at Ews (tarray tuchar (room - Zlength O))
    (map vi zo ++ sublist (Zlength zo) (room - Zlength O) (Zrepeat Vundef (room - Zlength O)))
    (offset_val (Zlength O) q) *
  wv_at (owit room O) (offset_val (Zlength O) q)
  |-- out_at q room (out_vals room (O ++ zo)).
Proof.
  intros H FC. pose proof (Zlength_nonneg O). pose proof (Zlength_nonneg zo).
  unfold out_vals. rewrite map_app, <- app_assoc.
  rewrite (out_split q room O); [| lia | | auto].
  - apply derives_refl'. f_equal. f_equal. f_equal. f_equal. rewrite Zlength_app.
    rewrite sublist_Zrepeat by lia. f_equal. lia.
  - rewrite !Zlength_app, Zlength_map, Zlength_Zrepeat; lia.
Qed.

(* without a gzip header, deflate's hdr_at is empty *)
Lemma hdr_none (s : dstate) (hx : share * val * val * val) :
  d_gzhead s = None -> hdr_at (Some s) nullval hx = emp.
Proof. intros E. unfold hdr_at. rewrite E. rewrite prop_true_andp by auto. reflexivity. Qed.

(* Floyd's simplify_remove_localdef_temp (simpl on ident_eq of the large $"..." idents of main's locals) takes
   minutes here: remove the temp by rewriting instead *)
Lemma rlt_nil i : remove_localdef_temp i [] = [].
Proof. reflexivity. Qed.
Lemma rlt_gvars i g l : remove_localdef_temp i (gvars g :: l) = gvars g :: remove_localdef_temp i l.
Proof. reflexivity. Qed.
Lemma rlt_lvar i j t v l : remove_localdef_temp i (lvar j t v :: l) = lvar j t v :: remove_localdef_temp i l.
Proof. reflexivity. Qed.
Lemma rlt_same i v l : remove_localdef_temp i (temp i v :: l) = remove_localdef_temp i l.
Proof. simpl. unfold rlt_ident_eq. rewrite if_true by auto. reflexivity. Qed.
Lemma rlt_cons i j v l :
  i <> j -> remove_localdef_temp i (temp j v :: l) = temp j v :: remove_localdef_temp i l.
Proof. intros. simpl. unfold rlt_ident_eq. rewrite if_false by auto. reflexivity. Qed.

Ltac simplify_remove_localdef_temp ::=
  repeat first [ rewrite rlt_nil | rewrite rlt_gvars | rewrite rlt_lvar | rewrite rlt_same
               | rewrite rlt_cons by (let X := fresh in intro X; discriminate X) ].

(* the PROP part of deflate's precondition at main's two calls *)
Ltac pre_tac :=
  match goal with
  | Hinb : Zlength _ = _, Hinbb : bytes _, Hrun : c_deflate _ _ _ = _ |- _ =>
    rewrite Zlength_Zrepeat by lia;
    split; [| split; [| split]];
    [ intros; apply owit_ok; lia
    | unfold s32_ok; rep_lia
    | unfold strm_ranges, zmk; simpl; rewrite Zlength_nil, Hinb; unfold bytes in Hinbb; unfold ci_take in *;
      unfold u32_ok, u64_ok, u64r in *; repeat split; auto; try rep_lia
    | exists (fun f => f); split; [apply ef_ok_id |]; unfold on_state, c_on_state;
      rewrite DModel5.c_deflate_g_id; change (zmk ?a ?b ?c ?d ?e ?f ?g ?h) with (zcall a b c d e f g h);
      rewrite Hrun; reflexivity ]
  end.

Lemma det_call : det_call_stmt.
Proof.
  intros Espec J n data datap v1 v2 sp1 sp2 gv ls ci c HK.
  (* the two calls end in D_at for the model run of df2_deflate; the rest is the continuation *)
  unfold lsuf11. apply seq_assoc.
  eapply semax_seq' with (P' := EX d : dres, D_at J n data datap v1 v2 sp1 sp2 gv ls ci c d).
  2: { apply extract_exists_pre; intro d. apply HK. }
  clear HK.
  unfold C_at, C_sep, B_loc.
  Intros.
  pose proof H as [[Hdf [Hn [Hlen [Hbytes Hdp]]]] [_ [_ [Hrd _]]]].
  pose proof H0 as (Hoff & Hfl & Hfl4 & Hfin & Hroom & Pi1 & Pi2 & Po1 & Po2).
  pose proof H1 as (HJc & Hgz & Hnin & HO & HOb & HR & Htout & Hm1 & Hm2).
  assert (Hinb : Zlength (ci_inb data ls ci) = ci_take ls ci)
    by (unfold ci_inb, ci_take; rewrite Zlength_sublist; lia).
  assert (Hinbb : bytes (ci_inb data ls ci)) by (apply Forall_sublist; auto).
  destruct (df2_deflate J Hdf (cs_fin c) (cs_s c) (ls_read ls + cs_nin c) (cs_adler c) (ci_inb data ls ci)
              (cs_nin c) (ci_room ci - Zlength (cs_out c)) (cs_tout c) (ci_flush ci) (cs_msg c))
    as (s' & z' & code & Hrun & Hcall & HJ');
    try solve [auto | rewrite Hinb; lia | rewrite Hinb; unfold ci_take; lia |
               pose proof (Zlength_nonneg (cs_out c)); lia | intros R0 HR0; rewrite Hinb; apply HR; auto].
  rewrite Hinb in Hrun, HJ'.
  pose proof (df2_adler J Hdf _ _ _ _ HJc) as Had.
  assert (HOn : 0 <= Zlength (cs_out c)) by apply Zlength_nonneg.
  assert_PROP (field_compatible (tarray tuchar (ci_room ci)) [] (ci_out1 ci) /\
               field_compatible (tarray tuchar (ci_room ci)) [] (ci_out2 ci)) as FC
    by (unfold out_at; entailer!).
  destruct FC as [FC1 FC2].
  unfold out_vals.
  rewrite (out_split (ci_out1 ci) (ci_room ci) (cs_out c)) by (rewrite ?Zlength_Zrepeat by lia; auto; lia).
  rewrite (out_split (ci_out2 ci) (ci_room ci) (cs_out c)) by (rewrite ?Zlength_Zrepeat by lia; auto; lia).
  unfold strm_at, BoundKit.obj.
  flatten_sepcon_in_SEP.
  (* abbreviate the rest of the body first: forward_call on the whole statement is slow *)
  abbreviate_semax.
  forward_call (Some (cs_s c), v1, nullval, sp1, (Ews, nullval, nullval, nullval), ci_in1 ci, Ews,
                ci_inb data ls ci, cs_nin c, ci_take ls ci - cs_nin c, ls_read ls + cs_nin c,
                offset_val (Zlength (cs_out c)) (ci_out1 ci), Zrepeat Vundef (ci_room ci - Zlength (cs_out c)),
                owit (ci_room ci) (cs_out c), cs_tout c, cs_msgv1 c, cs_msg c, cs_adler c, ci_flush ci,
                (Some s', z', code), gv).
  { rewrite (hdr_none (cs_s c)) by auto. rewrite Hinb, Zlength_Zrepeat by lia. cancel. }
  { pre_tac. }
  cbn [fst snd]. Intros msgv1'.
  forward_call (Some (cs_s c), v2, nullval, sp2, (Ews, nullval, nullval, nullval), ci_in2 ci, Ews,
                ci_inb data ls ci, cs_nin c, ci_take ls ci - cs_nin c, ls_read ls + cs_nin c,
                offset_val (Zlength (cs_out c)) (ci_out2 ci), Zrepeat Vundef (ci_room ci - Zlength (cs_out c)),
                owit (ci_room ci) (cs_out c), cs_tout c, cs_msgv2 c, cs_msg c, cs_adler c, ci_flush ci,
                (Some s', z', code), gv).
  { rewrite Hinb, Zlength_Zrepeat by lia. cancel. }
  { pre_tac. }
  cbn [fst snd]. Intros msgv2'.
  forward.
  Exists (mkDR s' z' code msgv1' msgv2').
  unfold D_at, D_sep, B_loc, dr_ok, strm_at, d_call. cbn [dr_s dr_z dr_code dr_msgv1 dr_msgv2].
  rewrite !Zlength_Zrepeat by lia. rewrite Hinb.
  rewrite (hdr_none (cs_s c)) by auto.
  pose proof Hcall as (Hzin & Hnx & Hav & Htin & Haout & Hzout & Htot & Hzb).
  sep_apply (out_join (ci_out1 ci) (ci_room ci) (cs_out c) (z_out z') ltac:(lia) FC1).
  sep_apply (out_join (ci_out2 ci) (ci_room ci) (cs_out c) (z_out z') ltac:(lia) FC2).
  rewrite !offset_offset_val, Zlength_app.
  replace (Zlength (z_out z') + Zlength (cs_out c)) with (Zlength (cs_out c) + Zlength (z_out z')) by lia.
  entailer!.
  unfold BoundKit.obj. rewrite Hinb. cancel.
Qed.

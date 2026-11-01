(* Law rt_gzip_header on the round-2 harness, main's body, segment 4 (statements 40-43: the do-while of
   deflate(Z_FINISH) calls with clip()-sized output pieces): the kit of G2MS4Call.v and G2MainSeg4.v.
   - the pieces of the segment's statement (the loop, its body, the call at the end of the body);
   - the compressor's caller fields at the law's compspecs (main's own load of next_out, its stores of next_out and
     avail_out), the compressor given back as the local's memory;
   - the output window of one call: the next clip(b - |O|) bytes of the compressed object after the bytes O already
     produced, with deflate_specN's witness that next_out is weakly valid when that window is empty;
   - the pointer differences next_out - compressed;
   - the loop's assertions: [s4_LI] at the head of the body, [s4_X1] right before the call, [s4_LC] after the call
     (also the assertion after the loop). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.harness.rt_gzip_header.CS.
Require Import Zlib.proof.harness.rt_gzip_header.G2MainDefs.
Require Import Zlib.proof.deflate.Rep.
Require Import Zlib.proof.deflate.DSpec Zlib.proof.deflate.DSpecN.
Require Zlib.proof.deflate.Api_toend.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.harness.rt_gzip_header.G2DFacts.
Require Import Zlib.proof.harness.rt_gzip_header.G2MainKit.
Require Import Zlib.harness.rt_gzip_header.code.
#[local] Existing Instance Zlib.proof.harness.rt_gzip_header.CS.CS.
Local Open Scope logic.

(** ** The pieces of statements 40-43 *)

(* the do-while (statement 33) *)
Definition s4_loop : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [seg4] in
          (match seg4 with Ssequence _ (Ssequence l _) => l | _ => Sskip end) in exact x).

(* its body *)
Definition s4_body : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [s4_loop] in
          (match s4_loop with Sloop b _ => b | _ => Sskip end) in exact x).

(* the end of the body: the call deflate(&compressor, Z_FINISH) and code = its result *)
Definition s4_call : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [s4_body] in
          (match s4_body with Ssequence _ d => d | _ => Sskip end) in exact x).

(* statements 34-35 *)
Definition s4_end : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [seg4] in
          (match seg4 with Ssequence _ (Ssequence _ e) => e | _ => Sskip end) in exact x).

(** ** VST's removal of a temporary *)
(* VST's after_forward_call simplifies remove_localdef_temp with `simpl rlt_ident_eq`, which runs away on main's
   identifiers; each identifier comparison is decided by vm_compute instead (G2MS4Call.v, G2MainSeg4.v redefine
   simplify_remove_localdef_temp with it). *)
Ltac s4_rlt_fix u :=
  lazymatch u with
  | context C [rlt_ident_eq ?a ?b] =>
      let v := eval vm_compute in (rlt_ident_eq a b) in
      let u2 := context C [v] in s4_rlt_fix u2
  | _ => u
  end.

Ltac s4_rlt :=
  match goal with |- context [remove_localdef_temp ?i ?L] =>
    let u := constr:(remove_localdef_temp i L) in
    let u' := eval lazy delta [remove_localdef_temp] beta iota in u in
    let u' := s4_rlt_fix u' in
    let u' := eval lazy beta iota in u' in
    let u' := eval lazy zeta in u' in
    change u with u'
  end.

(** ** The compressor's fields at the law's compspecs *)

(* DSpec.api_fields (at deflate's compspecs) at main's *)
Definition s4_fieldsL (strmp nextin : val) (ain tin : Z) (nextout : val) (aout tout : Z) (msgv : val)
    (adler : Z) : mpred :=
  !! (u32_ok ain /\ u64_ok tin /\ u32_ok aout /\ u64_ok tout /\ u64_ok adler) &&
  (field_at Ews t_z (DOT _next_in) nextin strmp *
   field_at Ews t_z (DOT _avail_in) (vi ain) strmp *
   field_at Ews t_z (DOT _total_in) (vl tin) strmp *
   field_at Ews t_z (DOT _next_out) nextout strmp *
   field_at Ews t_z (DOT _avail_out) (vi aout) strmp *
   field_at Ews t_z (DOT _total_out) (vl tout) strmp *
   field_at Ews t_z (DOT _msg) msgv strmp *
   field_at Ews t_z (DOT _adler) (vl adler) strmp).

Ltac s4_fa_cs := match goal with |- context [@field_at Zlib.proof.deflate.DCS.CS ?sh ?t ?g ?v ?q] =>
  rewrite (@field_at_change_composite Zlib.proof.deflate.DCS.CS CS CC_dcs sh t g v v (JMeq_refl _) eq_refl) end.

Lemma s4_fields_L strmp nextin ain tin nextout aout tout msgv adler :
  api_fields strmp nextin ain tin nextout aout tout msgv adler =
  s4_fieldsL strmp nextin ain tin nextout aout tout msgv adler.
Proof. unfold api_fields, s4_fieldsL. repeat s4_fa_cs. reflexivity. Qed.

Lemma s4_fields_fold strmp nextin ain tin nextout aout tout msgv adler :
  u32_ok ain -> u64_ok tin -> u32_ok aout -> u64_ok tout -> u64_ok adler ->
  field_at Ews t_z (DOT _next_in) nextin strmp *
  field_at Ews t_z (DOT _avail_in) (vi ain) strmp *
  field_at Ews t_z (DOT _total_in) (vl tin) strmp *
  field_at Ews t_z (DOT _next_out) nextout strmp *
  field_at Ews t_z (DOT _avail_out) (vi aout) strmp *
  field_at Ews t_z (DOT _total_out) (vl tout) strmp *
  field_at Ews t_z (DOT _msg) msgv strmp *
  field_at Ews t_z (DOT _adler) (vl adler) strmp
  |-- api_fields strmp nextin ain tin nextout aout tout msgv adler.
Proof. intros. rewrite s4_fields_L. unfold s4_fieldsL. entailer!. Qed.

(* the compressor, whatever its state, gives back the local's memory *)
Lemma s4_comp_back (vc : val) (gv : globals) (os : option dstate) (ghp nin : val) (ain tin : Z) (nout : val)
    (aout tout : Z) (msgv : val) (adler : Z) :
  dstream 2 os vc ghp gv * api_fields vc nin ain tin nout aout tout msgv adler * srest vc
  |-- data_at_ Tsh t_z vc * TT.
Proof.
  unfold srest.
  sep_apply (BoundKit.dstream_data_at_ os vc ghp gv nin ain tin nout aout tout msgv adler
               Zlib.proof.deflate.Api_toend.dstream_to_end).
  rewrite (@data_at__change_composite DCS.CS CS CC_dcs Ews Zlib.proof.deflate.Rep.t_strm) by reflexivity.
  rewrite (BoundKit.data_at__Tsh_split t_z vc). cancel.
Qed.

(* the header part of the state depends on its gzhead only *)
Lemma s4_hdr_at_eq (s s' : dstate) ghp hx :
  d_gzhead s' = d_gzhead s -> hdr_at (Some s') ghp hx = hdr_at (Some s) ghp hx.
Proof. intros E. unfold hdr_at. rewrite E. reflexivity. Qed.

Lemma s4_hclose_step vh g (s s' : dstate) hx Hr :
  hclose vh g s hx Hr -> d_gzhead s' = d_gzhead s -> hclose vh g s' hx Hr.
Proof. intros H E s'' E'. apply H. congruence. Qed.

(* no input object at Z_NULL *)
Lemma s4_in_obj (ish : share) : in_objN ish [] nullval = emp.
Proof. unfold in_objN. rewrite if_true by reflexivity. apply pred_ext; entailer!. Qed.

Lemma s4_in_ptr (n : Z) : in_ptrN nullval n = nullval.
Proof. unfold in_ptrN. rewrite if_true by reflexivity. reflexivity. Qed.

(** ** The output window of one call *)

(* an array of bytes cut at a and c *)
Lemma s4_cut3 {cs : compspecs} sh n a c (l : list val) q :
  0 <= a <= c -> c <= n -> Zlength l = n ->
  @data_at cs sh (tarray tuchar n) l q |--
  @data_at cs sh (tarray tuchar a) (sublist 0 a l) q *
  @data_at cs sh (tarray tuchar (c - a)) (sublist a c l) (offset_val a q) *
  @data_at cs sh (tarray tuchar (n - c)) (sublist c n l) (offset_val c q).
Proof.
  intros Ha Hc Hl. assert_PROP (field_compatible (tarray tuchar n) [] q) as FC by entailer!.
  unfold tarray. rewrite (split3_data_at_Tarray_tuchar sh n a c l q) by lia.
  rewrite !field_address0_offset by auto with field_compatible.
  simpl nested_field_offset. rewrite !Z.add_0_l, !Z.mul_1_l. cancel.
Qed.

Lemma s4_glue3 {cs : compspecs} sh n a c (l : list val) q :
  0 <= a <= c -> c <= n -> Zlength l = n -> field_compatible (tarray tuchar n) [] q ->
  @data_at cs sh (tarray tuchar a) (sublist 0 a l) q *
  @data_at cs sh (tarray tuchar (c - a)) (sublist a c l) (offset_val a q) *
  @data_at cs sh (tarray tuchar (n - c)) (sublist c n l) (offset_val c q)
  |-- @data_at cs sh (tarray tuchar n) l q.
Proof.
  intros Ha Hc Hl FC.
  unfold tarray. rewrite (split3_data_at_Tarray_tuchar sh n a c l q) by lia.
  rewrite !field_address0_offset by auto with field_compatible.
  simpl nested_field_offset. rewrite !Z.add_0_l, !Z.mul_1_l. cancel.
Qed.

Lemma s4_bytes_dcs sh n (v : list val) q :
  @data_at Zlib.proof.deflate.DCS.CS sh (tarray tuchar n) v q = @data_at CS sh (tarray tuchar n) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_dcs); [apply JMeq_refl | reflexivity]. Qed.

Lemma s4_tok_dcs sh n q :
  @malloc_token Zlib.proof.deflate.DCS.CS sh (tarray tuchar n) q = @malloc_token CS sh (tarray tuchar n) q.
Proof. apply equal_f; apply (@malloc_token_change_composite _ _ CC_dcs). reflexivity. Qed.

Lemma s4_tuchar_dcs sh (v : val) q :
  @data_at Zlib.proof.deflate.DCS.CS sh tuchar v q = @data_at CS sh tuchar v q.
Proof. apply equal_f. apply (@data_at_change_composite _ _ CC_dcs); [apply JMeq_refl | reflexivity]. Qed.

(* the compressed object of b bytes, O produced so far *)
Definition s4_comp (b : Z) (O : list Z) (cbp : val) : mpred :=
  malloc_token Ews (tarray tuchar b) cbp * data_at Ews (tarray tuchar b) (cbytes b O) cbp.

(* the output space of the call: aout bytes after O in the object of b bytes; W the witness that next_out is weakly
   valid when aout = 0; the rest Rr closes the object again with any bytes zo the call writes *)
Definition s4_win (b : Z) (O : list Z) (cbp : val) (aout : Z) : mpred :=
  EX W : wvw, EX Rr : mpred,
  !! ((aout = 0 -> wv_ok W) /\
      forall zo : list Z, 0 <= Zlength zo <= aout ->
        Rr * wv_at W (offset_val (Zlength O) cbp) *
        @data_at Zlib.proof.deflate.DCS.CS Ews (tarray tuchar aout)
          (map vi zo ++ sublist (Zlength zo) aout (Zrepeat Vundef aout)) (offset_val (Zlength O) cbp)
        |-- s4_comp b (O ++ zo) cbp) &&
  (@data_at Zlib.proof.deflate.DCS.CS Ews (tarray tuchar aout) (Zrepeat Vundef aout) (offset_val (Zlength O) cbp) *
   wv_at W (offset_val (Zlength O) cbp) * Rr).

(* some space: no witness needed *)
Lemma s4_win_space b (O : list Z) cbp aout :
  0 <= Zlength O -> 0 < aout <= b - Zlength O ->
  s4_comp b O cbp |-- s4_win b O cbp aout.
Proof.
  intros HO Ha. unfold s4_comp, cbytes, s4_win.
  assert_PROP (field_compatible (tarray tuchar b) [] cbp) as FC by entailer!.
  set (L := map vi O ++ Zrepeat Vundef (b - Zlength O)).
  assert (HL : Zlength L = b) by (unfold L; list_solve).
  sep_apply (s4_cut3 Ews b (Zlength O) (Zlength O + aout) L cbp); try lia.
  replace (Zlength O + aout - Zlength O) with aout by lia.
  assert (E1 : sublist 0 (Zlength O) L = map vi O) by (unfold L; list_solve).
  assert (E2 : sublist (Zlength O) (Zlength O + aout) L = Zrepeat Vundef aout) by (unfold L; list_solve).
  assert (E3 : sublist (Zlength O + aout) b L = Zrepeat Vundef (b - (Zlength O + aout))) by (unfold L; list_solve).
  rewrite E1, E2, E3.
  Exists WVnone (malloc_token Ews (tarray tuchar b) cbp *
                 data_at Ews (tarray tuchar (Zlength O)) (map vi O) cbp *
                 data_at Ews (tarray tuchar (b - (Zlength O + aout))) (Zrepeat Vundef (b - (Zlength O + aout)))
                   (offset_val (Zlength O + aout) cbp)).
  unfold wv_at. rewrite s4_bytes_dcs.
  apply andp_right; [ apply prop_right; split | cancel ].
  { intros; lia. }
  intros zo Hz. rewrite s4_bytes_dcs.
  set (L' := map vi (O ++ zo) ++ Zrepeat Vundef (b - Zlength (O ++ zo))).
  assert (HL' : Zlength L' = b) by (unfold L'; list_solve).
  unfold s4_comp, cbytes. fold L'.
  eapply derives_trans; [ | apply sepcon_derives; [ apply derives_refl |
     apply (s4_glue3 Ews b (Zlength O) (Zlength O + aout) L' cbp); auto; try lia ] ].
  replace (Zlength O + aout - Zlength O) with aout by lia.
  replace (sublist 0 (Zlength O) L') with (map vi O) by (unfold L'; list_solve).
  replace (sublist (Zlength O) (Zlength O + aout) L')
    with (map vi zo ++ sublist (Zlength zo) aout (Zrepeat Vundef aout)) by (unfold L', vi; list_solve).
  replace (sublist (Zlength O + aout) b L') with (Zrepeat Vundef (b - (Zlength O + aout)))
    by (unfold L'; list_solve).
  cancel.
Qed.

(* no space and nothing produced (b = 0): the 0-byte object's token *)
Lemma s4_win_none cbp :
  s4_comp 0 [] cbp |-- s4_win 0 [] cbp 0.
Proof.
  unfold s4_comp, cbytes, s4_win.
  change (map vi [] ++ Zrepeat Vundef (0 - Zlength (@nil Z))) with (@nil val).
  assert_PROP (isptr cbp) as Pc by entailer!.
  Exists (WVtok (tarray tuchar 0)) emp.
  unfold wv_at. rewrite isptr_offset_val_zero by exact Pc.
  rewrite s4_tok_dcs, s4_bytes_dcs.
  apply andp_right; [ apply prop_right; split | cancel ].
  { intros _. unfold wv_ok. rewrite sizeof_tarray_tuchar by lia. lia. }
  intros zo Hz.
  assert (Zlength zo = 0) by lia. destruct zo; [ | rewrite Zlength_cons in *; rep_lia ].
  unfold s4_comp, cbytes.
  change (map vi [] ++ sublist (Zlength (@nil Z)) 0 (Zrepeat Vundef 0)) with (@nil val).
  change (map vi ([] ++ []) ++ Zrepeat Vundef (0 - Zlength (@nil Z ++ []))) with (@nil val).
  cancel.
Qed.

(* no space after O (b = |O| > 0): the last byte of O *)
Lemma s4_win_last b (O : list Z) cbp :
  0 < Zlength O -> Zlength O = b ->
  s4_comp b O cbp |-- s4_win b O cbp 0.
Proof.
  intros HO Hb. unfold s4_comp, cbytes, s4_win.
  assert_PROP (field_compatible (tarray tuchar b) [] cbp) as FC by entailer!.
  set (L := map vi O ++ Zrepeat Vundef (b - Zlength O)).
  assert (HL : Zlength L = b) by (unfold L; list_solve).
  sep_apply (s4_cut3 Ews b (b - 1) b L cbp); try lia.
  replace (b - (b - 1)) with 1 by lia. rewrite Z.sub_diag.
  set (v := Znth (b - 1) L).
  replace (sublist (b - 1) b L) with [v] by (unfold v; list_solve).
  rewrite (data_at_singleton_array_eq Ews tuchar v [v]) by reflexivity.
  replace (sublist b b L) with (Zrepeat Vundef 0) by (rewrite sublist_nil; reflexivity).
  Exists (WVbefore Ews v)
         (malloc_token Ews (tarray tuchar b) cbp *
          data_at Ews (tarray tuchar (b - 1)) (sublist 0 (b - 1) L) cbp).
  unfold wv_at. rewrite s4_bytes_dcs, s4_tuchar_dcs.
  replace (offset_val (-1) (offset_val (Zlength O) cbp)) with (offset_val (b - 1) cbp)
    by (rewrite offset_offset_val; f_equal; lia).
  rewrite Hb.
  apply andp_right; [ apply prop_right; split | cancel ].
  { intros _. unfold wv_ok. auto. }
  intros zo Hz.
  assert (Zlength zo = 0) by lia. destruct zo; [ | rewrite Zlength_cons in *; rep_lia ].
  change (map vi [] ++ sublist (Zlength (@nil Z)) 0 (Zrepeat Vundef 0)) with (Zrepeat Vundef 0).
  rewrite s4_bytes_dcs, app_nil_r. unfold s4_comp, cbytes. fold L.
  replace (offset_val (-1) (offset_val b cbp)) with (offset_val (b - 1) cbp)
    by (rewrite offset_offset_val; f_equal; lia).
  eapply derives_trans; [ | apply sepcon_derives; [ apply derives_refl |
     apply (s4_glue3 Ews b (b - 1) b L cbp); auto; try lia ] ].
  replace (b - (b - 1)) with 1 by lia. rewrite Z.sub_diag.
  replace (sublist (b - 1) b L) with [v] by (unfold v; list_solve).
  rewrite (data_at_singleton_array_eq Ews tuchar v [v]) by reflexivity.
  replace (sublist b b L) with (Zrepeat Vundef 0) by (rewrite sublist_nil; reflexivity).
  cancel.
Qed.

(* clip(b - |O|) is 0 only when the object is full *)
Lemma s4_clip_cases b (O : list Z) :
  0 <= Zlength O <= b ->
  (clipz (b - Zlength O) = 0 /\ Zlength O = b) \/ 0 < clipz (b - Zlength O) <= b - Zlength O.
Proof. intros H. unfold clipz, umax. lia. Qed.

Lemma s4_out_open b (O : list Z) cbp :
  0 <= Zlength O <= b ->
  s4_comp b O cbp |-- s4_win b O cbp (clipz (b - Zlength O)).
Proof.
  intros HO.
  destruct (s4_clip_cases b O HO) as [(A0 & Hb') | Ha].
  - rewrite A0. destruct O as [ | x O' ].
    + rewrite Zlength_nil in Hb'. subst b. apply s4_win_none.
    + apply s4_win_last; [ rewrite Zlength_cons; pose proof (Zlength_nonneg O'); lia | exact Hb' ].
  - apply s4_win_space; lia.
Qed.

(** ** next_out - compressed *)

Lemma s4_sub_ptr (q : val) k : isptr q -> 0 <= k <= Ptrofs.max_unsigned ->
  force_val (sem_binary_operation' Osub (tptr tuchar) (tptr tuchar) (offset_val k q) q) = Vlong (Int64.repr k).
Proof.
  intros Pq Hk. destruct q; try contradiction. simpl.
  unfold sem_sub_pp. simpl. rewrite if_true by auto. simpl.
  f_equal. rewrite Ptrofs.sub_add_l, Ptrofs.sub_idem, Ptrofs.add_zero_l.
  unfold Ptrofs.divs. rewrite (Ptrofs.signed_repr 1) by rep_lia. rewrite Z.quot_1_r, Ptrofs.repr_signed.
  rewrite Vptrofs_unfold_true by reflexivity. unfold Ptrofs.to_int64.
  rewrite Ptrofs.unsigned_repr by rep_lia. reflexivity.
Qed.

Lemma s4_binop_sub (q : val) k : isptr q -> 0 <= k <= Ptrofs.max_unsigned ->
  eval_binop Osub (tptr tuchar) (tptr tuchar) (offset_val k q) q = Vlong (Int64.repr k).
Proof.
  intros Pq Hk. unfold eval_binop. rewrite <- (s4_sub_ptr q k Pq Hk). unfold force_val2, force_val.
  destruct (sem_binary_operation' _ _ _ _ _); reflexivity.
Qed.

(* capacity - (next_out - compressed) *)
Lemma s4_rest_val (q : val) m k : isptr q -> 0 <= k <= m -> m <= Int64.max_unsigned ->
  force_val (sem_binary_operation' Osub tulong tulong (Vlong (Int64.repr m))
    (eval_cast tlong tulong (eval_binop Osub (tptr tuchar) (tptr tuchar) (offset_val k q) q))) =
  Vlong (Int64.repr (m - k)).
Proof.
  intros Pq Hk Hm. rewrite s4_binop_sub by (auto; rep_lia). simpl.
  f_equal. apply Int64.eqm_samerepr. apply Int64.eqm_sub; apply Int64.eqm_sym; apply Int64.eqm_unsigned_repr.
Qed.

Lemma s4_sameblock (q : val) k : isptr q -> is_true (sameblock (offset_val k q) q).
Proof. intros Pq. destruct q; try contradiction. unfold sameblock; simpl. destruct (peq b b); [reflexivity | congruence]. Qed.

(** ** The assertions of the loop *)
Section Loop.
Context (gv : globals) (vh vg vc vd vr : val)
        (J : Z -> DS.gzh -> Z -> list Z -> dstate -> Z -> Z -> Z -> Prop)
        (g : gsetup) (hx : share * val * val * val) (Hr : mpred) (b : Z) (cbp : val).

(* the locals of the segment *)
Definition s4_locals : list localdef :=
  temp _out_size (vl b) :: temp _compressed cbp :: gp_locals g ++ gs_locals g ++ lv_locals gv vh vg vc vd vr.

(* the memory of the loop: the compressor in the state s with the caller's fields (next_in Z_NULL, avail_in 0,
   next_out = compressed + |O|, avail_out ao), head inside the compressor, the compressed object with O first *)
Definition s4_mem (O : list Z) (s : dstate) (tin tout adler ao : Z) (msgv : val) : list mpred :=
  [dstream 2 (Some s) vc vh gv; api_fields vc nullval 0 tin (offset_val (Zlength O) cbp) ao tout msgv adler;
   srest vc; hdr_at (Some s) vh hx; Hr; gside vg vd vr g; mem_mgr gv; R gv; ifz gv; s4_comp b O cbp].

(* at the head of the body: J of the bytes O produced so far, the state and the fields *)
Definition s4_LI : environ -> mpred :=
  EX O : list Z, EX s : dstate, EX tin : Z, EX tout : Z, EX adler : Z, EX ao : Z, EX msg : option Z, EX msgv : val,
  PROPx [gs_ok g; J (g_wb g) (gh_of g) b O s tin tout adler; msg_ok msg msgv; hclose vh g s hx Hr; isptr cbp]
  (LOCALx s4_locals (SEPx (s4_mem O s tin tout adler ao msgv))).

(* right before the call: avail_out = clip(b - |O|) *)
Definition s4_X1 (O : list Z) (s : dstate) (tin tout adler : Z) (msg : option Z) (msgv : val) : environ -> mpred :=
  PROPx [gs_ok g; J (g_wb g) (gh_of g) b O s tin tout adler; msg_ok msg msgv; hclose vh g s hx Hr; isptr cbp]
  (LOCALx s4_locals (SEPx (s4_mem O s tin tout adler (clipz (b - Zlength O)) msgv))).

(* after the call (and after the loop): its code; J when it is Z_OK, the gzip stream of no data with main's header
   when it is Z_STREAM_END *)
Definition s4_LC : environ -> mpred :=
  EX code : Z, EX O : list Z, EX s : dstate, EX tin : Z, EX tout : Z, EX adler : Z, EX ao : Z, EX msg : option Z,
  EX msgv : val,
  PROPx [gs_ok g; rs32 code; 0 <= Zlength O <= b; b <= max_u64; rbytes O; d_gzhead s = Some (gh_of g);
         code = Z_OK -> J (g_wb g) (gh_of g) b O s tin tout adler;
         code = Z_STREAM_END -> dfinal [] 2 (rwbe (g_wb g)) (Some (gh_of g)) [] O;
         msg_ok msg msgv; hclose vh g s hx Hr; isptr cbp]
  (LOCALx (temp _code (vi code) :: s4_locals) (SEPx (s4_mem O s tin tout adler ao msgv))).

End Loop.

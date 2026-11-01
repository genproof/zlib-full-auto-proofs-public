(* Law api_reset, main (ARMain.v): the kit shared by the segment lemmas of main's proof.
   - Delta_m (main's type context), POST_m (main's postcondition after start_function);
   - the segments of f_main's body: seg_obody (the body of the for-loop over phase, after its test
     `if (phase < 2) ; else break;`), seg_dbody (the body of the do-while), seg_tail (the do-while body from
     its second `if (phase == 1)`: the asserts, `read += ...`, the four free()s), seg_chk (the asserts),
     seg_rst (the then-branch of `if (phase == 0)` after the do-while: inflateReset(&used), inflateInit2_(&fresh));
   - the streams: `used` is an istreamA (SpecW.v) from its inflateInit2_ on; `fresh` is, in phase 0, the raw
     struct new_stream() and offer() leave (fresh_raw: next_in, avail_in, next_out, avail_out of a zfields,
     the rest undefined), and an istreamA from its inflateInit2_ on;
   - the assertions: oinv_at (the for-loop), dinv_at (the do-while), mid0_at / mid1_at (the do-while body
     after the inflate() calls and the test of Z_MEM_ERROR, phase 0 / phase 1);
   - the statements of the parts (body_stmt, tail0_stmt, tail1_stmt, chk_stmt, rst_stmt, obody_stmt) and the
     moves of byte arrays, malloc tokens and struct z_stream between the units' compspecs and the law's. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.api_reset.ARMainDefs.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.harness.api_reset.code.
Local Open Scope logic.

#[export] Existing Instances CC_inflate CC_adler32 CC_crc32 CC_zutil CC_inffast CC_inftrees CC_compress.

Definition Delta_m : tycontext := func_tycontext f_main (QPvarspecs p) Gmain nil.

(* main's postcondition after start_function (main_core_spec) *)
Definition POST_m : ret_assert :=
  frame_ret_assert (function_body_ret_assert tint (EX r : int, PROP () RETURN (Vint r) SEP (TT))%argsassert)
    (stackframe_of f_main).

(* ---------------------------------------------------------------------------------------------- *)
(* The segments of f_main's body                                                                 *)

(* a sub-statement by its path (0: first component, other: second) *)
Fixpoint sub_stmt (path: list nat) (s: statement) : statement :=
  match path, s with
  | nil, _ => s
  | O :: pth, Ssequence a _ => sub_stmt pth a
  | S _ :: pth, Ssequence _ b => sub_stmt pth b
  | O :: pth, Sifthenelse _ a _ => sub_stmt pth a
  | S _ :: pth, Sifthenelse _ _ b => sub_stmt pth b
  | O :: pth, Sloop a _ => sub_stmt pth a
  | S _ :: pth, Sloop _ b => sub_stmt pth b
  | _, _ => Sskip
  end.

Ltac get_seg pth :=
  let p := eval vm_compute in pth in
  let x := eval cbv beta iota zeta delta [sub_stmt f_main fn_body] in (sub_stmt p (fn_body f_main)) in
  exact x.

(* the for-loop over phase is the statement at path_oloop; its body is `if (phase < 2) ; else break;`
   followed by seg_obody *)
Definition path_oloop : list nat := [0; 1; 1; 1; 1; 0; 1]%nat.
Definition path_obody : list nat := path_oloop ++ [0; 1]%nat.
(* in seg_obody: input_len, input, its test, read = 0, the do-while, `if (phase == 0) {...}` *)
Definition path_dloop : list nat := path_obody ++ [1; 1; 1; 1; 0]%nat.
Definition path_dbody : list nat := path_dloop ++ [0]%nat.
(* the do-while body is a chain of 17 statements; seg_tail is its suffix from the 15th (index 14) *)
Definition path_tail : list nat := path_dbody ++ repeat 1%nat 14.
Definition path_chk : list nat := path_tail ++ [0; 0]%nat.
Definition path_rst : list nat := path_obody ++ [1; 1; 1; 1; 1; 0]%nat.

Definition seg_obody : statement := ltac:(get_seg path_obody).
Definition seg_dbody : statement := ltac:(get_seg path_dbody).
Definition seg_tail : statement := ltac:(get_seg path_tail).
Definition seg_chk : statement := ltac:(get_seg path_chk).
Definition seg_rst : statement := ltac:(get_seg path_rst).

(* ---------------------------------------------------------------------------------------------- *)
(* Compspecs moves (the specs are at the units' CS, main at the law's CS)                          *)

Definition t_z : type := Tstruct _z_stream_s noattr.

Definition strm_tuple : Type :=
  (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * val)))))))))))))%type.

Lemma strm_cs sh (v: strm_tuple) q:
  @data_at Zlib.units.Inflate.CS sh Rep.t_strm v q = @data_at CS sh t_z v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_inflate); [apply JMeq_refl | reflexivity]. Qed.
Lemma strm_cs_c sh (v: strm_tuple) q:
  @data_at Zlib.units.Compress.CS sh t_zs v q = @data_at CS sh t_z v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_compress); [apply JMeq_refl | reflexivity]. Qed.
Lemma bytes_inflate_cs sh n (v: list val) q:
  @data_at Zlib.units.Inflate.CS sh (tarray tuchar n) v q = @data_at CS sh (tarray tuchar n) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_inflate); [apply JMeq_refl | reflexivity]. Qed.
Lemma bytes_adler_cs sh n (v: list val) q:
  @data_at Zlib.units.Adler32.CS sh (tarray tuchar n) v q = @data_at CS sh (tarray tuchar n) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_adler32); [apply JMeq_refl | reflexivity]. Qed.
Lemma tok_inflate_cs sh n q:
  @malloc_token Zlib.units.Inflate.CS sh (tarray tuchar n) q = @malloc_token CS sh (tarray tuchar n) q.
Proof. apply equal_f; apply (@malloc_token_change_composite _ _ CC_inflate). reflexivity. Qed.
Lemma tok_adler_cs sh n q:
  @malloc_token Zlib.units.Adler32.CS sh (tarray tuchar n) q = @malloc_token CS sh (tarray tuchar n) q.
Proof. apply equal_f; apply (@malloc_token_change_composite _ _ CC_adler32). reflexivity. Qed.

(* the local z_stream before new_stream() *)
Lemma strm_undef sh q:
  @data_at_ CS sh t_z q =
  @data_at Zlib.units.Compress.CS sh t_zs
    (zs_val Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef) q.
Proof. unfold data_at_, zs_val. rewrite strm_cs_c. reflexivity. Qed.

(* the harness's "1.3.2" as inflateInit2_ takes it *)
Definition hv_list : list val := map (fun c => Vint (Int.repr c)) [49; 46; 51; 46; 50; 0].

Lemma hversion gv:
  @hversion_at CS ___stringlit_api_reset_1 gv =
  @data_at Zlib.units.Inflate.CS Ers (tarray tschar (Zlength hv_list)) hv_list (gv ___stringlit_api_reset_1).
Proof.
  unfold hversion_at, hv_list. change (Zlength _) with 6. symmetry.
  apply equal_f; apply (@data_at_change_composite _ _ CC_inflate); [apply JMeq_refl | reflexivity].
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Stream fresh in phase 0: the raw struct                                                        *)

Definition fr_tup (zb: zfields) : strm_tuple :=
  (zf_ni zb, (Vint (Int.repr (zf_ai zb)), (Vundef, (zf_no zb, (Vint (Int.repr (zf_ao zb)), (Vundef, (Vundef,
   (Vundef, (nullval, (nullval, (nullval, (Vundef, (Vundef, Vundef))))))))))))).

Definition fresh_raw (vb: val) (zb: zfields) : mpred := @data_at CS Tsh t_z (fr_tup zb) vb.

(* as offer() and new_stream() take and give it *)
Lemma fresh_raw_c vb zb:
  fresh_raw vb zb =
  @data_at Zlib.units.Compress.CS Tsh t_zs
    (zs_val (zf_ni zb) (Vint (Int.repr (zf_ai zb))) Vundef (zf_no zb) (Vint (Int.repr (zf_ao zb))) Vundef Vundef
       Vundef nullval nullval nullval Vundef Vundef Vundef) vb.
Proof. unfold fresh_raw, zs_val. rewrite strm_cs_c. reflexivity. Qed.

(* the fields of a raw struct as inflateInit2_ takes them *)
Definition fr_raw (zb: zfields) : rawf :=
  RF (zf_ni zb) (Vint (Int.repr (zf_ai zb))) Vundef (zf_no zb) (Vint (Int.repr (zf_ao zb))) Vundef Vundef Vundef
     Vundef.

Lemma fresh_raw_i gv vb zb:
  fresh_raw vb zb = raw_strm gv Tsh vb (fr_raw zb) Vundef Vundef nullval nullval nullval.
Proof. unfold fresh_raw, raw_strm. change Rep.t_strm with t_z. symmetry. apply (strm_cs Tsh (fr_tup zb) vb). Qed.

(* the fields after new_stream() (both streams) *)
Definition zf_new : zfields := ZF nullval 0 0 nullval 0 0 None 0 0 Vundef.

(* after a successful inflateInit2_ on fresh_raw zb: model adler adl (strm->adler = wrap & 1 for a wrapped
   stream; for a raw stream the member is undefined and the model value is free) *)
Definition zf_init (zb: zfields) (adl: Z) : zfields :=
  ZF (zf_ni zb) (zf_ai zb) 0 (zf_no zb) (zf_ao zb) 0 None 0 adl Vundef.

(* at a `return`: the struct given back to the stack frame *)
Lemma fresh_frame vb zb: fresh_raw vb zb |-- @data_at_ CS Tsh t_z vb.
Proof. unfold fresh_raw. apply data_at_data_at_. Qed.

Lemma raw_frame gv sh q r m s za zf o: raw_strm gv sh q r m s za zf o |-- @data_at_ CS sh t_z q.
Proof. unfold raw_strm. change Rep.t_strm with t_z. rewrite strm_cs. apply data_at_data_at_. Qed.

Lemma land1_range x: 0 <= Z.land x 1 <= 1.
Proof.
  change (Z.land x 1) with (Z.land x (Z.ones 1)). rewrite Z.land_ones by lia.
  pose proof (Z.mod_pos_bound x (2 ^ 1) ltac:(reflexivity)). simpl in *. lia.
Qed.

(* inflateInit2_ returned Z_OK on fresh_raw zb: the stream as an istreamA *)
Lemma fresh_init gv vb zb adl L:
  zf_ok zb -> 0 <= adl <= Int64.max_unsigned -> (raw_live (Some L) = false -> adl = Z.land (i_wrap (l_s L)) 1) ->
  istream_raw gv Tsh vb (raw_after_init (fr_raw zb) (l_s L)) L |-- istreamA gv Tsh vb (zf_init zb adl) Vundef (Some L).
Proof.
  intros Zo Ha Hr. unfold istream_raw, istreamA, zstrm_atA, raw_strm, raw_after_init, fr_raw, zf_init, adler_v.
  unfold raw_live in *. Intros.
  assert (Zi: zf_ok (zf_init zb adl)) by (unfold zf_ok, zf_init in *; simpl; rep_lia).
  destruct (i_wrap (l_s L) =? 0) eqn:E; simpl.
  - entailer!.
  - rewrite (Hr eq_refl) in Zi |- *. entailer!.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* A live stream at the law's compspecs                                                          *)

Definition ar_tup (gv: globals) (z: zfields) (adv sp: val) : strm_tuple :=
  (zf_ni z, (Vint (Int.repr (zf_ai z)), (Vlong (Int64.repr (zf_tin z)), (zf_no z, (Vint (Int.repr (zf_ao z)),
   (Vlong (Int64.repr (zf_tout z)), (msg_val gv (zf_msg z), (sp, (gv Zlib.inflate.code._zcalloc,
   (gv Zlib.inflate.code._zcfree, (nullval, (Vint (Int.repr (zf_dt z)), (adv, zf_res z))))))))))))).

Lemma istreamA_unfold gv shs vs z av L:
  istreamA gv shs vs z av (Some L) =
  (!! (zf_ok z /\ writable_share shs /\ live_ok L) &&
   (@data_at CS shs t_z (ar_tup gv z (adler_v (raw_live (Some L)) z av) (l_sp L)) vs * state_mem gv vs L)).
Proof.
  unfold istreamA, zstrm_atA. change Rep.t_strm with t_z. rewrite strm_cs.
  apply pred_ext; entailer!.
Qed.

Lemma istreamA_fold gv shs vs z av L:
  zf_ok z -> writable_share shs -> live_ok L ->
  @data_at CS shs t_z (ar_tup gv z (adler_v (raw_live (Some L)) z av) (l_sp L)) vs * state_mem gv vs L
  |-- istreamA gv shs vs z av (Some L).
Proof. intros. rewrite istreamA_unfold. entailer!. Qed.

Lemma istreamA_opt_ptr gv shs (vs: val) z av st: isptr vs -> istreamA_opt gv shs vs z av st = istreamA gv shs vs z av st.
Proof. intros Pv. unfold istreamA_opt. destruct (eq_dec vs nullval); [subst; contradiction | reflexivity]. Qed.

Lemma is_live_ptr (vs: val) st: isptr vs -> is_live vs st = st.
Proof. intros Pv. unfold is_live. destruct (eq_dec vs nullval); [subst; contradiction | reflexivity]. Qed.

Lemma head_none vs L: isptr vs -> i_head (l_s L) = false -> head_opt (is_live vs (Some L)) = emp.
Proof. intros Pv H. rewrite is_live_ptr by auto. unfold head_opt, head_mem. rewrite H. reflexivity. Qed.

(* at a `return`: the struct given back to the stack frame *)
Lemma a_frame gv vs z av L: istreamA gv Tsh vs z av (Some L) |-- @data_at_ CS Tsh t_z vs * TT.
Proof. rewrite istreamA_unfold. Intros. sep_apply (data_at_data_at_ Tsh t_z). cancel. Qed.

Lemma a_frame_opt gv vs z av st: isptr vs -> istreamA_opt gv Tsh vs z av st |-- @data_at_ CS Tsh t_z vs * TT.
Proof.
  intros Pv. rewrite istreamA_opt_ptr by auto. destruct st as [L|]; [apply a_frame | ].
  unfold istreamA, zstrm_atA. change Rep.t_strm with t_z. rewrite strm_cs. Intros.
  sep_apply (data_at_data_at_ Tsh t_z). cancel.
Qed.

(* the struct as offer() takes it *)
Lemma istreamA_zs gv vs z av L:
  istreamA gv Tsh vs z av (Some L) |--
  !! (zf_ok z /\ live_ok L) &&
  (@data_at Zlib.units.Compress.CS Tsh t_zs
     (zs_val (zf_ni z) (Vint (Int.repr (zf_ai z))) (Vlong (Int64.repr (zf_tin z))) (zf_no z)
        (Vint (Int.repr (zf_ao z))) (Vlong (Int64.repr (zf_tout z))) (msg_val gv (zf_msg z)) (l_sp L)
        (gv Zlib.inflate.code._zcalloc) (gv Zlib.inflate.code._zcfree) nullval (Vint (Int.repr (zf_dt z)))
        (adler_v (raw_live (Some L)) z av) (zf_res z)) vs * state_mem gv vs L).
Proof. rewrite istreamA_unfold. Intros. unfold zs_val. rewrite strm_cs_c. entailer!. Qed.

(* after offer(strm, ip, ain, op, aout): the stream inflate() takes (no gz_header) *)
Lemma offer_fold gv vs z av L ip ain op aout:
  isptr vs -> zf_ok z -> live_ok L -> i_head (l_s L) = false ->
  0 <= ain <= Int.max_unsigned -> 0 <= aout <= Int.max_unsigned ->
  @data_at Zlib.units.Compress.CS Tsh t_zs
     (zs_val ip (Vint (Int.repr ain)) (Vlong (Int64.repr (zf_tin z))) op
        (Vint (Int.repr aout)) (Vlong (Int64.repr (zf_tout z))) (msg_val gv (zf_msg z)) (l_sp L)
        (gv Zlib.inflate.code._zcalloc) (gv Zlib.inflate.code._zcfree) nullval (Vint (Int.repr (zf_dt z)))
        (adler_v (raw_live (Some L)) z av) (zf_res z)) vs * state_mem gv vs L
  |-- istreamA_opt gv Tsh vs (ir_call z ip ain op aout) av (Some L) * head_opt (is_live vs (Some L)).
Proof.
  intros Pv Zo Lo Hh Ha Hb.
  rewrite head_none, istreamA_opt_ptr by auto. rewrite sepcon_emp.
  eapply derives_trans; [ | apply (istreamA_fold gv Tsh vs (ir_call z ip ain op aout) av L)];
    [ | unfold zf_ok, ir_call in *; simpl; tauto | auto | auto].
  unfold zs_val. rewrite strm_cs_c. apply derives_refl.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The objects of an inflate() call                                                              *)

(* the input object (copy_of: the slice of the input) and the output object (malloc: undefined bytes) *)
Definition ar_ib (ip: val) (ain: Z) (d: list Z) : inbuf := InBuf Ews ip 0 ain (bytes_rep d).
Definition ar_ob (op: val) (aout: Z) : outbuf := OutBuf Ews op 0 aout (Zrepeat Vundef aout).

Lemma ar_in_ptr ip ain d: isptr ip -> in_ptr (ar_ib ip ain d) 0 = ip.
Proof. intros P. destruct ip; try contradiction. simpl. rewrite Ptrofs.add_zero. reflexivity. Qed.
Lemma ar_out_ptr op aout: isptr op -> out_ptr (ar_ob op aout) 0 = op.
Proof. intros P. destruct op; try contradiction. simpl. rewrite Ptrofs.add_zero. reflexivity. Qed.

Lemma ar_in_ok ip ain d: isptr ip -> Zlength d = ain -> ain <= Ptrofs.max_unsigned -> bytes_ok d ->
  in_ok (ar_ib ip ain d) d.
Proof.
  intros Pp Hl Ht Hb. unfold in_ok, ar_ib. pose proof (Zlength_nonneg d).
  assert (Zlength (bytes_rep d) = ain) by (unfold bytes_rep; rewrite Zlength_map; auto).
  repeat split; auto; try lia.
  rewrite Z.add_0_l, sublist_same by lia. reflexivity.
Qed.

Lemma ar_out_ok op aout: isptr op -> 0 <= aout <= Ptrofs.max_unsigned -> out_ok (ar_ob op aout) aout.
Proof.
  intros Pp Hr. unfold out_ok, ar_ob.
  assert (Zlength (Zrepeat Vundef aout) = aout) by (rewrite Zlength_Zrepeat; lia).
  split; [apply writable_Ews | ]. repeat split; auto; try lia.
Qed.

(* the output object after a call that wrote ow *)
Definition out_after (c: list val) (ow: list Z) (n: Z) : list val :=
  sublist 0 0 c ++ byte_vals ow ++ sublist (0 + Zlength ow) n c.

(* malloc's object of n bytes *)
Lemma malloc_bytes sh n q: @data_at_ CS sh (tarray tuchar n) q = @data_at CS sh (tarray tuchar n) (Zrepeat Vundef n) q.
Proof. reflexivity. Qed.

Lemma bufs_pre L ip ain d op aout: 0 <= aout ->
  @data_at CS Ews (tarray tuchar ain) (bytes_rep d) ip * @malloc_token CS Ews (tarray tuchar ain) ip *
  @data_at CS Ews (tarray tuchar aout) (Zrepeat Vundef aout) op * @malloc_token CS Ews (tarray tuchar aout) op
  |-- bufs_opt (Some L) (ar_ib ip ain d) (Some (ar_ob op aout)) [] true true.
Proof.
  intros Ha. unfold bufs_opt, ar_ib, ar_ob, in_rep, out_opt, out_rep, in_tok, out_tok.
  rewrite <- (bytes_inflate_cs Ews ain _ ip), <- (tok_inflate_cs Ews ain ip),
          <- (bytes_inflate_cs Ews aout _ op), <- (tok_inflate_cs Ews aout op).
  assert (Eo: sublist 0 0 (Zrepeat Vundef aout) ++ byte_vals [] ++ sublist (0 + Zlength (@nil Z)) aout
                (Zrepeat Vundef aout) = Zrepeat Vundef aout).
  { rewrite sublist_nil. simpl. rewrite sublist_same by (rewrite ?Zlength_Zrepeat; lia). reflexivity. }
  rewrite Eo. cancel.
Qed.

Lemma bufs_post L ip ain d op aout ow:
  bufs_opt (Some L) (ar_ib ip ain d) (Some (ar_ob op aout)) ow true true
  |-- @data_at CS Ews (tarray tuchar ain) (bytes_rep d) ip * @malloc_token CS Ews (tarray tuchar ain) ip *
      @data_at CS Ews (tarray tuchar aout) (out_after (Zrepeat Vundef aout) ow aout) op *
      @malloc_token CS Ews (tarray tuchar aout) op.
Proof.
  unfold bufs_opt, ar_ib, ar_ob, in_rep, out_opt, out_rep, in_tok, out_tok, out_after.
  rewrite (bytes_inflate_cs Ews ain _ ip), (tok_inflate_cs Ews ain ip), (tok_inflate_cs Ews aout op),
          (bytes_inflate_cs Ews aout _ op). cancel.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The message literals: strm->msg of either stream is NULL or a valid pointer                    *)

Lemma ar_mapsto_valid sh q: readable_share sh -> mapsto_ sh tschar q |-- valid_pointer q.
Proof.
  intros Hsh. unfold mapsto_, mapsto. destruct q; try apply FF_left.
  cbv beta iota zeta delta [access_mode type_is_volatile tschar]. rewrite if_true by auto. apply orp_left.
  - apply andp_left1. apply prop_left. intros X. inversion X.
  - apply andp_left2. apply exp_left. intros v2.
    replace (Vptr b i) with (Vptr b (Ptrofs.repr (Ptrofs.unsigned i + 0)))
      by (rewrite Z.add_0_r, Ptrofs.repr_unsigned; auto).
    pose proof (valid_pointer.address_mapsto_valid_pointer Mint8signed v2 sh b (Ptrofs.unsigned i) 0
             ltac:(pose proof (Ptrofs.unsigned_range i); simpl; lia) ltac:(simpl; lia)) as X.
    constructor. exact X.
Qed.

Lemma ar_msg_valid gv m: ir_msg_lits gv |-- valid_pointer (gv (msg_ident m)).
Proof.
  unfold ir_msg_lits. pose proof (ir_all_msgs_complete m) as Hm. induction ir_all_msgs as [ | a l IH].
  - inversion Hm.
  - simpl. destruct Hm as [<- | Hm].
    + apply sepcon_valid_pointer1. apply ar_mapsto_valid. auto with share.
    + apply sepcon_valid_pointer2. auto.
Qed.

Lemma ar_msg_ptr gv m: ir_msg_lits gv |-- !! isptr (gv (msg_ident m)).
Proof.
  unfold ir_msg_lits. pose proof (ir_all_msgs_complete m) as Hm. induction ir_all_msgs as [ | a l IH].
  - inversion Hm.
  - simpl. destruct Hm as [<- | Hm].
    + sep_apply (mapsto__local_facts Ers tschar (gv (msg_ident a))). entailer!.
    + sep_apply IH. entailer!.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The assertions                                                                                *)

Definition J0T : Type := Z -> list Z -> Z -> zfields -> live -> Prop.
Definition J1T : Type := Z -> list Z -> Z -> zfields -> live -> zfields -> live -> Prop.

(* the facts fixed in a phase: the theory's facts, windowBits w (accepted by inflateInit2_), the phase's input
   src (at inp), the two locals *)
Definition g_facts (J0: J0T) (J1: J1T) (w: Z) (inp: val) (src: list Z) (va vb: val) : Prop :=
  ar_facts J0 J1 /\ wbits_ok w = true /\ Int.min_signed <= w <= Int.max_signed /\
  Zlength src <= Int64.max_signed /\ bytes_ok src /\ isptr inp /\ isptr va /\ isptr vb.

(* stream fresh: raw in phase 0, live from phase 1 on *)
Definition fresh_mem (gv: globals) (ph: Z) (vb: val) (zb: zfields) (Lb: live) : mpred :=
  if ph =? 0 then fresh_raw vb zb else istreamA gv Tsh vb zb Vundef (Some Lb).

(* the for-loop over phase, at its head (phase = ph) and at its continue point (phase = ph - 1): phase 0,
   used just made by inflateInit2_ (J0 at position 0 of any input), fresh raw; phase 1, both after the reset
   (J1 at position 0 of any input); phase 2, nothing more is needed.  A live stream's wrapper is 0 (raw)
   exactly when windowBits is negative: strm->adler is compared only for windowBits >= 0. *)
Definition ostate (J0: J0T) (J1: J1T) (w ph: Z) (za: zfields) (La: live) (zb: zfields) (Lb: live) : Prop :=
  if ph =? 0 then
    (forall src, bytes_ok src -> J0 w src 0 za La) /\ swfW (l_s La) /\ raw_live (Some La) = (w <? 0) /\ zf_ok zb
  else if ph =? 1 then
    (forall src, bytes_ok src -> J1 w src 0 za La zb Lb) /\ swfW (l_s La) /\ swfW (l_s Lb) /\
    raw_live (Some La) = (w <? 0) /\ raw_live (Some Lb) = (w <? 0)
  else True.

Definition oinv_at (J0: J0T) (J1: J1T) (gv: globals) (va vb: val) (w ph phv: Z)
    (za: zfields) (La: live) (zb: zfields) (Lb: live) : environ -> mpred :=
  PROP (0 <= ph <= 2; ostate J0 J1 w ph za La zb Lb)
  LOCAL (temp _window_bits (Vint (Int.repr w)); temp _phase (Vint (Int.repr phv));
         lvar _used t_z va; lvar _fresh t_z vb; gvars gv)
  SEP (istreamA gv Tsh va za Vundef (Some La); fresh_mem gv ph vb zb Lb;
       mem_mgr gv; zfuncs gv; tables_rep Ers gv; crc_table_at Ers gv; version_lit gv;
       hversion_at ___stringlit_api_reset_1 gv; ir_msg_lits gv; TT).

(* the for-loop's head and continue assertions, and its exit *)
Definition oinv (J0: J0T) (J1: J1T) (gv: globals) (va vb: val) (w: Z) : environ -> mpred :=
  EX ph: Z, EX za: zfields, EX La: live, EX zb: zfields, EX Lb: live, oinv_at J0 J1 gv va vb w ph ph za La zb Lb.
Definition ocont (J0: J0T) (J1: J1T) (gv: globals) (va vb: val) (w: Z) : environ -> mpred :=
  EX ph: Z, EX za: zfields, EX La: live, EX zb: zfields, EX Lb: live,
  oinv_at J0 J1 gv va vb w (ph + 1) ph za La zb Lb.
Definition obrk (J0: J0T) (J1: J1T) (gv: globals) (va vb: val) (w: Z) : environ -> mpred :=
  EX za: zfields, EX La: live, EX zb: zfields, EX Lb: live, oinv_at J0 J1 gv va vb w 2 2 za La zb Lb.

(* the do-while in phase ph (0 or 1) on the input src at inp; pos = read, the bytes of src consumed *)
Definition dprop (J0: J0T) (J1: J1T) (w: Z) (src: list Z) (ph pos: Z) (za: zfields) (La: live) (zb: zfields)
    (Lb: live) : Prop :=
  swfW (l_s La) /\ raw_live (Some La) = (w <? 0) /\
  (if ph =? 0 then J0 w src pos za La /\ zf_ok zb
   else J1 w src pos za La zb Lb /\ swfW (l_s Lb) /\ raw_live (Some Lb) = (w <? 0)).

Definition dinv_at (J0: J0T) (J1: J1T) (gv: globals) (va vb: val) (w ph: Z) (inp: val) (src: list Z) (pos: Z)
    (za: zfields) (La: live) (zb: zfields) (Lb: live) : environ -> mpred :=
  PROP (dprop J0 J1 w src ph pos za La zb Lb; 0 <= pos <= Zlength src)
  LOCAL (temp _window_bits (Vint (Int.repr w)); temp _phase (Vint (Int.repr ph));
         temp _input_len (Vlong (Int64.repr (Zlength src))); temp _input inp;
         temp _read (Vlong (Int64.repr pos)); lvar _used t_z va; lvar _fresh t_z vb; gvars gv)
  SEP (istreamA gv Tsh va za Vundef (Some La); fresh_mem gv ph vb zb Lb;
       malloc_token Ews (tarray tuchar (Zlength src)) inp; data_at Ews (tarray tuchar (Zlength src)) (bytes_rep src) inp;
       mem_mgr gv; zfuncs gv; tables_rep Ers gv; crc_table_at Ers gv; version_lit gv;
       hversion_at ___stringlit_api_reset_1 gv; ir_msg_lits gv; TT).

Definition dinv (J0: J0T) (J1: J1T) (gv: globals) (va vb: val) (w ph: Z) (inp: val) (src: list Z)
    : environ -> mpred :=
  EX pos: Z, EX za: zfields, EX La: live, EX zb: zfields, EX Lb: live,
  dinv_at J0 J1 gv va vb w ph inp src pos za La zb Lb.

(* the post of the do-while body: dinv at the loop test (normal end) *)
Definition dpost (J0: J0T) (J1: J1T) (gv: globals) (va vb: val) (w ph: Z) (inp: val) (src: list Z) : ret_assert :=
  loop1_ret_assert (dinv J0 J1 gv va vb w ph inp src)
    (overridePost (dinv J0 J1 gv va vb w ph inp src) POST_m).

(* After the inflate() calls of one iteration and the test of Z_MEM_ERROR (before the asserts): the piece
   offered was src[pos .. pos + take) (in the objects iu (used's) and ifr (fresh's)), the output space room
   bytes (objects ou, ofr); used's call returned ra (code_fresh = ra too) and left (za, La). *)

(* phase 0: fresh was only offered the objects (zb: its fields after offer); cu, cf the output objects'
   contents *)
Definition mid0_facts (J0: J0T) (J1: J1T) (w: Z) (inp: val) (src: list Z) (va vb: val)
    (pos take room: Z) (iu ifr ou ofr: val) (ra: Z) (za: zfields) (La: live) (zb: zfields) : Prop :=
  g_facts J0 J1 w inp src va vb /\
  J0 w src (pos + (take - zf_ai za)) za La /\ swfW (l_s La) /\ raw_live (Some La) = (w <? 0) /\ zf_ok zb /\
  0 <= pos /\ 0 <= take <= Int.max_unsigned /\ pos + take <= Zlength src /\ 0 <= zf_ai za <= take /\
  0 <= room <= Int.max_unsigned /\ ra <> Z_MEM_ERROR /\ isptr iu /\ isptr ifr /\ isptr ou /\ isptr ofr.

Definition mid0_at (J0: J0T) (J1: J1T) (gv: globals) (va vb: val) (w: Z) (inp: val) (src: list Z)
    (pos take room: Z) (iu ifr ou ofr: val) (cu cf: list val) (ra: Z) (za: zfields) (La: live) (zb: zfields)
    : environ -> mpred :=
  PROP ()
  LOCAL (temp _code_used (Vint (Int.repr ra)); temp _code_fresh (Vint (Int.repr ra));
         temp _window_bits (Vint (Int.repr w)); temp _phase (Vint (Int.repr 0));
         temp _input_len (Vlong (Int64.repr (Zlength src))); temp _input inp;
         temp _read (Vlong (Int64.repr pos)); temp _take (Vlong (Int64.repr take));
         temp _room (Vlong (Int64.repr room));
         temp _in_used iu; temp _in_fresh ifr; temp _out_used ou; temp _out_fresh ofr;
         lvar _used t_z va; lvar _fresh t_z vb; gvars gv)
  SEP (istreamA gv Tsh va za Vundef (Some La); fresh_raw vb zb;
       data_at Ews (tarray tuchar take) (bytes_rep (sublist pos (pos + take) src)) iu;
       malloc_token Ews (tarray tuchar take) iu;
       data_at Ews (tarray tuchar take) (bytes_rep (sublist pos (pos + take) src)) ifr;
       malloc_token Ews (tarray tuchar take) ifr;
       data_at Ews (tarray tuchar room) cu ou; malloc_token Ews (tarray tuchar room) ou;
       data_at Ews (tarray tuchar room) cf ofr; malloc_token Ews (tarray tuchar room) ofr;
       malloc_token Ews (tarray tuchar (Zlength src)) inp; data_at Ews (tarray tuchar (Zlength src)) (bytes_rep src) inp;
       mem_mgr gv; zfuncs gv; tables_rep Ers gv; crc_table_at Ers gv; version_lit gv;
       hversion_at ___stringlit_api_reset_1 gv; ir_msg_lits gv; TT).

(* phase 1: fresh's call returned ra too and left (zb, Lb); both calls wrote ow (af_inflate1) *)
Definition mid1_facts (J0: J0T) (J1: J1T) (w: Z) (inp: val) (src: list Z) (va vb: val)
    (pos take room: Z) (iu ifr ou ofr: val) (ra: Z) (za: zfields) (La: live) (zb: zfields) (Lb: live)
    (ow: list Z) : Prop :=
  g_facts J0 J1 w inp src va vb /\
  J1 w src (pos + (take - zf_ai za)) za La zb Lb /\ swfW (l_s La) /\ swfW (l_s Lb) /\
  raw_live (Some La) = (w <? 0) /\ raw_live (Some Lb) = (w <? 0) /\
  0 <= pos /\ 0 <= take <= Int.max_unsigned /\ pos + take <= Zlength src /\ 0 <= zf_ai za <= take /\
  0 <= room <= Int.max_unsigned /\ 0 <= zf_ao za <= room /\ ra <> Z_MEM_ERROR /\
  zf_ai za = zf_ai zb /\ zf_ao za = zf_ao zb /\ zf_tin za = zf_tin zb /\ zf_tout za = zf_tout zb /\
  zf_dt za = zf_dt zb /\ zf_msg za = zf_msg zb /\ (0 <= w -> zf_adler za = zf_adler zb) /\
  Zlength ow = room - zf_ao za /\ isptr iu /\ isptr ifr /\ isptr ou /\ isptr ofr.

Definition mid1_at (J0: J0T) (J1: J1T) (gv: globals) (va vb: val) (w: Z) (inp: val) (src: list Z)
    (pos take room: Z) (iu ifr ou ofr: val) (ra: Z) (za: zfields) (La: live) (zb: zfields) (Lb: live)
    (ow: list Z) : environ -> mpred :=
  PROP ()
  LOCAL (temp _code_used (Vint (Int.repr ra)); temp _code_fresh (Vint (Int.repr ra));
         temp _window_bits (Vint (Int.repr w)); temp _phase (Vint (Int.repr 1));
         temp _input_len (Vlong (Int64.repr (Zlength src))); temp _input inp;
         temp _read (Vlong (Int64.repr pos)); temp _take (Vlong (Int64.repr take));
         temp _room (Vlong (Int64.repr room));
         temp _in_used iu; temp _in_fresh ifr; temp _out_used ou; temp _out_fresh ofr;
         lvar _used t_z va; lvar _fresh t_z vb; gvars gv)
  SEP (istreamA gv Tsh va za Vundef (Some La); istreamA gv Tsh vb zb Vundef (Some Lb);
       data_at Ews (tarray tuchar take) (bytes_rep (sublist pos (pos + take) src)) iu;
       malloc_token Ews (tarray tuchar take) iu;
       data_at Ews (tarray tuchar take) (bytes_rep (sublist pos (pos + take) src)) ifr;
       malloc_token Ews (tarray tuchar take) ifr;
       data_at Ews (tarray tuchar room) (out_after (Zrepeat Vundef room) ow room) ou;
       malloc_token Ews (tarray tuchar room) ou;
       data_at Ews (tarray tuchar room) (out_after (Zrepeat Vundef room) ow room) ofr;
       malloc_token Ews (tarray tuchar room) ofr;
       malloc_token Ews (tarray tuchar (Zlength src)) inp; data_at Ews (tarray tuchar (Zlength src)) (bytes_rep src) inp;
       mem_mgr gv; zfuncs gv; tables_rep Ers gv; crc_table_at Ers gv; version_lit gv;
       hversion_at ___stringlit_api_reset_1 gv; ir_msg_lits gv; TT).

(* ---------------------------------------------------------------------------------------------- *)
(* The statements of the parts                                                                    *)

(* the do-while body in phase ph (ARMainHead0.v: ph = 0, ARMainHead1.v: ph = 1) *)
Definition body_stmt (ph: Z) : Prop :=
  forall {Espec: OracleKind} J0 J1 gv va vb w inp src pos za La zb Lb,
  g_facts J0 J1 w inp src va vb ->
  semax Delta_m (dinv_at J0 J1 gv va vb w ph inp src pos za La zb Lb) seg_dbody
    (dpost J0 J1 gv va vb w ph inp src).

(* the end of the do-while body (ARMainTail.v) *)
Definition tail0_stmt : Prop :=
  forall {Espec: OracleKind} J0 J1 gv va vb w inp src pos take room iu ifr ou ofr cu cf ra za La zb,
  mid0_facts J0 J1 w inp src va vb pos take room iu ifr ou ofr ra za La zb ->
  semax Delta_m (mid0_at J0 J1 gv va vb w inp src pos take room iu ifr ou ofr cu cf ra za La zb) seg_tail
    (dpost J0 J1 gv va vb w 0 inp src).

Definition tail1_stmt : Prop :=
  forall {Espec: OracleKind} J0 J1 gv va vb w inp src pos take room iu ifr ou ofr ra za La zb Lb ow,
  mid1_facts J0 J1 w inp src va vb pos take room iu ifr ou ofr ra za La zb Lb ow ->
  semax Delta_m (mid1_at J0 J1 gv va vb w inp src pos take room iu ifr ou ofr ra za La zb Lb ow) seg_tail
    (dpost J0 J1 gv va vb w 1 inp src).

(* the asserts of phase 1 (ARMainChk.v): they all hold and change nothing *)
Definition chk_stmt : Prop :=
  forall {Espec: OracleKind} J0 J1 gv va vb w inp src pos take room iu ifr ou ofr ra za La zb Lb ow,
  mid1_facts J0 J1 w inp src va vb pos take room iu ifr ou ofr ra za La zb Lb ow ->
  semax Delta_m (mid1_at J0 J1 gv va vb w inp src pos take room iu ifr ou ofr ra za La zb Lb ow) seg_chk
    (normal_ret_assert (mid1_at J0 J1 gv va vb w inp src pos take room iu ifr ou ofr ra za La zb Lb ow)).

(* after the do-while of phase 0 (ARMainRst.v): inflateReset(&used) (asserted Z_OK), inflateInit2_(&fresh, w)
   (`return 0` unless Z_OK), to the for-loop's continue point in phase 0 *)
Definition rst_stmt : Prop :=
  forall {Espec: OracleKind} J0 J1 gv va vb w inp src pos za La zb Lb,
  g_facts J0 J1 w inp src va vb ->
  semax Delta_m (dinv_at J0 J1 gv va vb w 0 inp src pos za La zb Lb) seg_rst
    (overridePost (ocont J0 J1 gv va vb w) POST_m).

(* the body of the for-loop after its test, in phase 0 or 1 (ARMainOuter.v): the input, the do-while, the
   reset after phase 0 *)
Definition obody_stmt : Prop :=
  forall {Espec: OracleKind} J0 J1 gv va vb w ph za La zb Lb,
  ar_facts J0 J1 -> wbits_ok w = true -> Int.min_signed <= w <= Int.max_signed -> isptr va -> isptr vb ->
  0 <= ph <= 1 ->
  semax Delta_m (oinv_at J0 J1 gv va vb w ph ph za La zb Lb) seg_obody
    (loop1_ret_assert (ocont J0 J1 gv va vb w) (overridePost (obrk J0 J1 gv va vb w) POST_m)).

(* ---------------------------------------------------------------------------------------------- *)
(* Model facts on the wrapper                                                                     *)

(* inflateInit2_ makes a raw stream exactly for a negative windowBits *)
Lemma init_raw sp w: wbits_ok w = true -> raw_live (Some (init_live sp w)) = (w <? 0).
Proof.
  intros W. unfold wbits_ok in W. unfold raw_live, init_live.
  destruct (reset2_wb w) as [[wr wb] | ] eqn:E; [ | discriminate].
  (* the wrapper inflateInit2_ stores (fix F8: bit 3 with a window size from the header) *)
  assert (Wi: i_wrap (init_s wr wb) = reset2_wrap wr wb).
  { change (init_s wr wb) with (reset_full_s (set_i_wbits (set_i_wrap zero_s (reset2_wrap wr wb)) wb)).
    unfold reset_full_s, reset_hdr_s. destruct (_ =? 0); reflexivity. }
  cbn [l_s]. rewrite Wi. clear Wi W.
  unfold reset2_wb in E. destruct (Z.ltb_spec w 0).
  - destruct (w <? -15); [discriminate | ].
    destruct ((8 <=? - w) && (- w <=? 15))%bool eqn:B; [ | discriminate].
    inversion E; subst. apply andb_prop in B. destruct B as [B _]. apply Z.leb_le in B.
    unfold reset2_wrap. destruct (Z.eqb_spec (- w) 0); [lia | reflexivity].
  - assert (Wr: wr = Z.shiftr w 4 + 5) by (destruct (_ || _)%bool; inversion E; auto).
    assert (Hs: 0 <= Z.shiftr w 4) by (apply Z.shiftr_nonneg; lia).
    apply Z.eqb_neq. unfold reset2_wrap. destruct (wb =? 0); [| lia].
    intros Z0. apply Z.lor_eq_0_iff in Z0. lia.
Qed.

(* inflateReset keeps the wrapper *)
Lemma reset_raw z L: raw_live (Some (thd3 (reset_f z L))) = raw_live (Some L).
Proof.
  unfold reset_f, thd3, raw_live. cbn [snd l_s set_l_s].
  unfold reset_full_s, reset_hdr_s. destruct (Z.land (i_wrap (l_s L)) 8 =? 0); reflexivity.
Qed.


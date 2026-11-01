(* Law rt_session (harness/rt_session.c): main's statements 58-62, the input object: the compressed bytes, then any bytes (SMKit.v, [segB_stmt]). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.deflate.DSpec9.
Require Zlib.proof.deflate.Api_toend.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.proof.zutil.Libc.
Require Import Zlib.proof.harness.rt_stream.UDFacts.
Require Import Zlib.proof.harness.rt_session.SCS.
Require Import Zlib.proof.harness.rt_session.SIFacts.
Require Import Zlib.proof.harness.rt_session.SMainStmt.
Require Import Zlib.proof.harness.rt_session.SMKit.
Require Import Zlib.proof.harness.rt_session.SMBFacts.
Require Import Zlib.harness.rt_session.code.
#[local] Existing Instance SCS.CS.
Local Open Scope logic.

(* VST's after_forward_call simplifies remove_localdef_temp with `simpl rlt_ident_eq`, which runs away on main's
   identifiers (e.g. _i against _input); each identifier comparison is decided by vm_compute instead. *)
Ltac smb_rlt_fix u :=
  lazymatch u with
  | context C [rlt_ident_eq ?a ?b] =>
      let v := eval vm_compute in (rlt_ident_eq a b) in
      let u2 := context C [v] in smb_rlt_fix u2
  | _ => u
  end.

Ltac simplify_remove_localdef_temp ::=
  match goal with |- context [remove_localdef_temp ?i ?L] =>
    let u := constr:(remove_localdef_temp i L) in
    let u' := eval lazy delta [remove_localdef_temp] beta iota in u in
    let u' := smb_rlt_fix u' in
    let u' := eval lazy beta iota in u' in
    let u' := eval lazy zeta in u' in
    change u with u'
  end.

(** ** The compressor's next_out *)

(* main reads compressor.next_out (at the law's compspecs) out of the deflate specifications' fields: the
   compressor without that field *)
Definition smb_cs_rest (gv : globals) (vc ghp : val) (c : cst) : mpred :=
  dstream 2 (Some (cs_s c)) vc ghp gv *
  (!! (u32_ok (cs_ain c) /\ u64_ok (cs_tin c) /\ u32_ok (cs_aout c) /\ u64_ok (cs_tout c) /\ u64_ok (cs_adler c)) &&
   (@field_at DCS.CS Ews Zlib.proof.deflate.Rep.t_strm (DOT deflate.code._next_in) (cs_ni c) vc *
    @field_at DCS.CS Ews Zlib.proof.deflate.Rep.t_strm (DOT deflate.code._avail_in) (vi (cs_ain c)) vc *
    @field_at DCS.CS Ews Zlib.proof.deflate.Rep.t_strm (DOT deflate.code._total_in) (vl (cs_tin c)) vc *
    @field_at DCS.CS Ews Zlib.proof.deflate.Rep.t_strm (DOT deflate.code._avail_out) (vi (cs_aout c)) vc *
    @field_at DCS.CS Ews Zlib.proof.deflate.Rep.t_strm (DOT deflate.code._total_out) (vl (cs_tout c)) vc *
    @field_at DCS.CS Ews Zlib.proof.deflate.Rep.t_strm (DOT deflate.code._msg) (cs_msgv c) vc *
    @field_at DCS.CS Ews Zlib.proof.deflate.Rep.t_strm (DOT deflate.code._adler) (vl (cs_adler c)) vc)) *
  srest vc.

Lemma smb_next_out_cs (v q : val) :
  @field_at DCS.CS Ews Zlib.proof.deflate.Rep.t_strm (DOT deflate.code._next_out) v q =
  field_at Ews t_z (DOT _next_out) v q.
Proof. apply equal_f; apply (@field_at_change_composite _ _ CC_dcs); [apply JMeq_refl | reflexivity]. Qed.

Lemma smb_cstream_split gv vc ghp c :
  cstream gv vc ghp c = field_at Ews t_z (DOT _next_out) (cs_no c) vc * smb_cs_rest gv vc ghp c.
Proof.
  unfold cstream, smb_cs_rest, api_fields. rewrite smb_next_out_cs.
  apply pred_ext; Intros; entailer!.
Qed.

(* the compressor, whatever its state, gives back the local's memory (at a return) *)
Lemma smb_comp_back (gv : globals) (vc ghp : val) (c : cst) : cstream gv vc ghp c |-- data_at_ Tsh t_z vc * TT.
Proof.
  unfold cstream, srest.
  sep_apply (BoundKit.dstream_data_at_ (Some (cs_s c)) vc ghp gv (cs_ni c) (cs_ain c) (cs_tin c) (cs_no c)
               (cs_aout c) (cs_tout c) (cs_msgv c) (cs_adler c) Api_toend.dstream_to_end).
  rewrite (@data_at__change_composite DCS.CS CS CC_dcs Ews Zlib.proof.deflate.Rep.t_strm) by reflexivity.
  rewrite (BoundKit.data_at__Tsh_split t_z vc). cancel.
Qed.

(* compressed_len = (size_t) (compressor.next_out - compressed) *)
Lemma smb_ptr_sub (p : val) (n : Z) :
  isptr p -> 0 <= n <= max_size ->
  force_val (sem_binary_operation' Osub (tptr tuchar) (tptr tuchar) (offset_val n p) p) = vl n.
Proof.
  intros Pp Hn. destruct p; try contradiction.
  unfold sem_binary_operation', sem_sub; simpl. unfold sem_sub_pp. simpl.
  destruct (eq_block b b); [ | congruence]. simpl. unfold vl.
  rewrite Ptrofs.sub_add_l, Ptrofs.sub_idem, Ptrofs.add_zero_l. change (Ptrofs.repr 1) with Ptrofs.one.
  rewrite Ptrofs.divs_one by reflexivity.
  unfold Vptrofs; simpl. unfold Ptrofs.to_int64.
  rewrite Ptrofs.unsigned_repr by (unfold max_size in *; rep_lia). reflexivity.
Qed.

(** ** The input object *)

(* byte arrays and malloc tokens of alloc_any_bytes (at the compspecs of the laws_common.h helpers) at main's *)
Lemma smb_bytes_adler sh n (v : list val) q :
  @data_at Zlib.units.Adler32.CS sh (tarray tuchar n) v q = @data_at CS sh (tarray tuchar n) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_adler32); [apply JMeq_refl | reflexivity]. Qed.
Lemma smb_tok_adler sh n q :
  @malloc_token Zlib.units.Adler32.CS sh (tarray tuchar n) q = @malloc_token CS sh (tarray tuchar n) q.
Proof. apply equal_f; apply (@malloc_token_change_composite _ _ CC_adler32). reflexivity. Qed.

(* the input object after i iterations of the copy loop: the first i bytes of O, then the bytes bs
   alloc_any_bytes gave from i on *)
Definition smb_mix (i : Z) (O bs : list Z) : list Z := sublist 0 i O ++ sublist i (Zlength bs) bs.

Lemma smb_mix_0 O bs : smb_mix 0 O bs = bs.
Proof. unfold smb_mix. rewrite sublist_nil, sublist_same by lia. reflexivity. Qed.

Lemma smb_mix_length i O bs :
  0 <= i <= Zlength O -> Zlength O <= Zlength bs -> Zlength (smb_mix i O bs) = Zlength bs.
Proof. intros. unfold smb_mix. rewrite Zlength_app, !Zlength_sublist by lia. lia. Qed.

(* the store of iteration i: input[i] = compressed[i] *)
Lemma smb_mix_store i O bs : 0 <= i < Zlength O -> Zlength O <= Zlength bs -> rbytes O ->
  upd_Znth i (map vi (smb_mix i O bs)) (Vint (Int.zero_ext 8 (Int.repr (Znth i O)))) =
  map vi (smb_mix (i + 1) O bs).
Proof.
  intros Hi Hl HO.
  assert (B : 0 <= Znth i O < 256) by (exact (proj1 (Forall_Znth O _) HO i Hi)).
  assert (E : Int.zero_ext 8 (Int.repr (Znth i O)) = Int.repr (Znth i O)).
  { rewrite <- (Int.repr_unsigned (Int.zero_ext 8 _)). rewrite Int.zero_ext_mod by (cbn; lia).
    rewrite Int.unsigned_repr by rep_lia. change (two_p 8) with 256. rewrite Z.mod_small by lia. reflexivity. }
  rewrite E. change (Vint (Int.repr (Znth i O))) with (vi (Znth i O)).
  rewrite upd_Znth_map. f_equal. unfold smb_mix.
  rewrite (sublist_split 0 i (i + 1) O) by lia. rewrite (sublist_split i (i + 1) (Zlength bs) bs) by lia.
  rewrite !sublist_len_1 by lia. rewrite <- app_assoc.
  rewrite upd_Znth_app2 by (rewrite Zlength_sublist by lia; list_solve).
  rewrite Zlength_sublist by lia. replace (i - (i - 0)) with 0 by lia.
  simpl app. rewrite upd_Znth0. reflexivity.
Qed.

(* the byte i of the compressed object (i < |O|): O's *)
Lemma smb_O_at i O (R : list val) : 0 <= i < Zlength O -> Znth i (map vi O ++ R) = Vint (Int.repr (Znth i O)).
Proof.
  intros Hi. rewrite app_Znth1 by (rewrite Zlength_map; lia).
  rewrite Znth_map by lia. reflexivity.
Qed.

(* after the loop: the input object is O followed by the bytes of bs after |O| *)
Lemma smb_mix_src_ok O bs : Zlength O <= Zlength bs <= max_size -> rbytes O -> Libc.bytes_ok bs ->
  src_ok O (smb_mix (Zlength O) O bs).
Proof.
  intros Hl HO Hb. pose proof (Zlength_nonneg O). unfold src_ok. rewrite smb_mix_length by lia.
  split; [lia | split].
  - unfold smb_mix. rewrite sublist0_app1 by (rewrite Zlength_sublist; lia).
    rewrite (sublist_same 0 (Zlength O) O) by lia. rewrite sublist_same by lia. reflexivity.
  - unfold rbytes, smb_mix. apply Forall_app; split.
    + apply Forall_sublist. exact HO.
    + apply Forall_sublist. eapply Forall_impl; [ | exact Hb]. simpl. intros; rep_lia.
Qed.

Lemma sm_segB : segB_stmt.
Proof.
  intros Espec gv vh vg vc va vd u O c.
  unfold DE, segB, POST_s, c_locals, d_locals, lvs, lv_locals. abbreviate_semax.
  Intros.
  match goal with H : su_ok u |- _ => pose proof H as [Hdok (Pdc & Pxc & Pnc & Pcc & Pe & Pc & Po & Pgx & Pgn & Pgc)] end.
  assert (Hcap : 0 <= su_cap u <= max_size) by (unfold su_dok in Hdok; tauto).
  match goal with H : dfinal _ _ _ _ _ _ |- _ => pose proof (smb_sc_ok u O ltac:(assumption) H) as Hsc end.
  (* compressed_len = (size_t) (compressor.next_out - compressed) = |O| *)
  rewrite (smb_cstream_split gv vc (ghp vh u) c) at 1. Intros. cbn [app].
  match goal with H : cs_no c = _ |- _ => rewrite H end.
  forward.
  forward.
  { entailer!. destruct (su_cp u); try contradiction.
    apply prop_right; unfold sameblock; cbn; destruct (peq b b); [reflexivity | congruence]. }
  rewrite smb_ptr_sub by (auto; unfold max_size in *; rep_lia).
  match goal with H : cs_no c = _ |- _ => rewrite <- H end.
  gather_SEP (field_at Ews t_z (DOT _next_out) _ vc) (smb_cs_rest gv vc (ghp vh u) c).
  rewrite <- smb_cstream_split.
  assert (HOm : 0 <= Zlength O <= max_size) by (pose proof (Zlength_nonneg O); lia).
  (* after = upto(PTRDIFF_MAX - compressed_len) *)
  forward_call (max_size - Zlength O).
  { unfold max_size in *; rep_lia. }
  Intros after.
  (* input = alloc_any_bytes(compressed_len + after) *)
  forward_call (Zlength O + after, gv).
  { unfold max_size in *; rep_lia. }
  Intros vret. destruct vret as [ip bs]. cbn [fst snd] in *.
  destruct (eq_dec ip nullval) as [Pip|Pip].
  { (* NULL: return 0, the compressor's local given back *)
    subst ip. forward_if.
    { sep_apply (smb_comp_back gv vc (ghp vh u) c). forward. Exists (Int.repr 0). entailer!.
      unfold hobj, graw. sep_apply (data_at_data_at_ Tsh t_g (hvals u) vh).
      sep_apply (data_at_data_at_ Tsh t_g (gval u) vg). cancel. }
    { exfalso; auto. } }
  Intros. rewrite smb_bytes_adler, smb_tok_adler.
  forward_if.
  { contradiction. }
  replace (bytes_rep bs) with (map vi bs) by reflexivity.
  unfold cobj, cbytes. Intros.
  (* the copy loop: after i iterations input holds O's first i bytes, then bs from i on *)
  assert (HOl : Zlength O <= Zlength bs) by lia.
  freeze [0;1;3;4;5;6;7;9;10;11;12;13;14] FR.
  forward_for_simple_bound (Zlength O) (EX i : Z,
    PROP ()
    LOCAL (temp _input ip; temp _after (Vlong (Int64.repr after));
           temp _compressed_len (vl (Zlength O));
           temp _dict_copy (su_dcp u); temp _extra_copy (su_xcp u); temp _name_copy (su_ncp u);
           temp _comment_copy (su_ccp u); temp _expected (su_ep u); temp _compressed (su_cp u);
           temp _out (su_op u);
           temp _level (vi (su_level u)); temp _window_bits (vi (su_wbits u)); temp _mem_level (vi (su_mem u));
           temp _strategy (vi (su_strategy u)); temp _choice (vi (su_choice u));
           temp _with_dict (vi (Z.b2z (with_dict u))); temp _with_head (vi (Z.b2z (with_head u)));
           temp _dict_len (vl (Zlength (su_dict u))); temp _extra_len (vl (Zlength (su_xf u)));
           temp _name_len (vl (Zlength (su_nm u))); temp _comment_len (vl (Zlength (su_cm u)));
           temp _data_len (vl (Zlength (su_data u))); temp _out_size (vl (su_cap u));
           temp _text (vi (su_text u)); temp _time (vl (su_time u)); temp _os (vi (su_os u));
           temp _hcrc (vi (su_hcrc u)); temp _dict (su_dictp u); temp _data (su_dp u);
           lvar _decompressor t_z vd; lvar _at t_p va; lvar _compressor t_z vc;
           lvar _got t_g vg; lvar _head t_g vh; gvars gv)
    SEP (FRZL FR; data_at Ews (tarray tuchar (Zlength O + after)) (map vi (smb_mix i O bs)) ip;
         data_at Ews (tarray tuchar (su_cap u)) (map vi O ++ Zrepeat Vundef (su_cap u - Zlength O)) (su_cp u))).
  { unfold max_size in *; rep_lia. }
  { entailer!. rewrite smb_mix_0. auto. }
  { assert (Bo : 0 <= Znth i O < 256) by (exact (proj1 (Forall_Znth O _) H2 i ltac:(lia))).
    forward.
    { rewrite smb_O_at by lia. entailer!. simpl; rep_lia. }
    rewrite smb_O_at by lia.
    forward.
    rewrite smb_mix_store by (auto; lia).
    entailer!. }
  (* at the exit: src = O ++ the bytes of bs after |O| *)
  assert (Hsl : Zlength (smb_mix (Zlength O) O bs) = Zlength O + after) by (rewrite smb_mix_length; lia).
  assert (Hok : src_ok O (smb_mix (Zlength O) O bs)) by (apply smb_mix_src_ok; auto; unfold max_size in *; lia).
  thaw FR.
  Exists (smb_mix (Zlength O) O bs) ip.
  unfold DB, iobj, cobj, cbytes, c_locals, d_locals, lvs, lv_locals. rewrite Hsl.
  replace (Zlength O + after - Zlength O) with after by lia.
  cbn [app].
  entailer!.
Qed.

(* Law deflate_api, deflate_run's loop body: the draws, exact_copy, exact_space, the stream's fields, up to the call (RunKit.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.deflate.LawFacts Zlib.proof.deflate.HarnessLib Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.roundtrip.RTRCS Zlib.proof.roundtrip.RTRRunSpec
               Zlib.proof.roundtrip.RTRApiConv Zlib.proof.roundtrip.RTRRunKit.
Require Import Zlib.harness.x_deflate_roundtrip.code.
#[local] Existing Instance RTRCS.CS.
Local Open Scope logic.

Lemma lp_t56 aout c :
  0 <= aout <= Int.max_unsigned -> 0 <= c <= 4194304 -> Int.unsigned (Int.shl (Int.repr 1) (Int.repr 20)) >= aout ->
  vi (if ((aout <=? 1048576) && (aout <=? 4194304 - c))%bool then 1 else 0) =
  bool2val (Int64.cmpu Cle (Int64.repr aout) (Int64.repr (Int.unsigned (Int.shl (Int.repr 1) (Int.repr 22)) - c))).
Proof.
  intros Ha Hc Hb.
  change (Int.unsigned (Int.shl (Int.repr 1) (Int.repr 22))) with 4194304.
  change (Int.unsigned (Int.shl (Int.repr 1) (Int.repr 20))) with 1048576 in Hb.
  unfold Int64.cmpu, Int64.ltu.
  rewrite !Int64.unsigned_repr by (unfold Int64.max_unsigned; simpl; rep_lia).
  replace (aout <=? 1048576) with true by (symmetry; apply Z.leb_le; lia).
  destruct (zlt (4194304 - c) aout); destruct (aout <=? 4194304 - c) eqn:E; simpl;
    rewrite ?Z.leb_le, ?Z.leb_gt in E; try lia; reflexivity.
Qed.

(* case analysis on the comparisons of a boolean temp's value *)
Ltac lp_bool :=
  unfold Int.ltu, Int.lt in *;
  rewrite ?Int.unsigned_repr, ?Int.signed_repr by rep_lia;
  repeat match goal with
  | |- context [zlt ?a ?b] => destruct (zlt a b)
  | |- context [?a <=? ?b] =>
      let E := fresh "E" in destruct (a <=? b) eqn:E; [apply Z.leb_le in E | apply Z.leb_gt in E]
  end; simpl; first [lia | reflexivity].

Lemma lp_fold rs (init wrap wb : val) nf dset hset clen ended Rp :
  field_at Ews t_drun (DOT _level) (vi (rs_level rs)) Rp *
  field_at Ews t_drun (DOT _method) (vi (rs_method rs)) Rp *
  field_at Ews t_drun (DOT _wbits) (vi (rs_wbits rs)) Rp *
  field_at Ews t_drun (DOT _mem) (vi (rs_mem rs)) Rp *
  field_at Ews t_drun (DOT _strategy) (vi (rs_strategy rs)) Rp *
  field_at Ews t_drun (DOT _init) init Rp *
  field_at Ews t_drun (DOT _wrap) wrap Rp *
  field_at Ews t_drun (DOT _wb) wb Rp *
  field_at Ews t_drun (DOT _data) (rs_datap rs) Rp *
  field_at Ews t_drun (DOT _n) (vi (Zlength (rs_data rs))) Rp *
  field_at Ews t_drun (DOT _nf) (vi nf) Rp *
  field_at Ews t_drun (DOT _dict) (rs_dictp rs) Rp *
  field_at Ews t_drun (DOT _dlen) (vi (Zlength (rs_dict rs))) Rp *
  field_at Ews t_drun (DOT _dict_set) (vi dset) Rp *
  field_at Ews t_drun (DOT _head_set) (vi hset) Rp *
  field_at Ews t_drun (DOT _xf) (rs_xfp rs) Rp *
  field_at Ews t_drun (DOT _nf_) (rs_nfp rs) Rp *
  field_at Ews t_drun (DOT _cf) (rs_cfp rs) Rp *
  field_at Ews t_drun (DOT _xlen) (vi (Zlength (rs_xf rs))) Rp *
  field_at Ews t_drun (DOT _nl) (vi (Zlength (rs_nm rs))) Rp *
  field_at Ews t_drun (DOT _cl) (vi (Zlength (rs_cm rs))) Rp *
  field_at Ews t_drun (DOT _comp) (rs_compp rs) Rp *
  field_at Ews t_drun (DOT _clen) (vl clen) Rp *
  field_at Ews t_drun (DOT _ended) (vi ended) Rp *
  field_at Ews t_drun (DOT _api_ok) (vi 1) Rp * drun_pad Rp
  |-- drun_rest rs init wrap wb nf dset hset clen ended Rp.
Proof. unfold drun_rest. apply derives_refl. Qed.

(* the return 0 after a failed allocation *)
Lemma lp_ret0 rs init wrap wb nf dset hset clen ended Rp s ghp sp gv nin ain tin nout aout tout msgv adler :
  run_mem_ok ->
  ((hset = 1 /\ ghp = hp_of Rp /\ d_gzhead s = Some (hdr_of rs)) \/ (hset = 0 /\ d_gzhead s = None)) ->
  drun_rest rs init wrap wb nf dset hset clen ended Rp * hpart hset Rp * hdr_at (Some s) ghp (hx_of rs) *
  dstream 2 (Some s) sp ghp gv * api_fields sp nin ain tin nout aout tout msgv adler * strm_pad sp
  |-- data_at_ Ews t_drun Rp * data_at_ Ews t_strmL sp * TT.
Proof.
  intros [M1 [M2 _]] Hh.
  sep_apply (M2 rs init wrap wb nf dset hset clen ended Rp s ghp Hh).
  sep_apply (M1 (Some s) sp ghp gv nin ain tin nout aout tout msgv adler).
  cancel.
Qed.

(* after if (finishing) ... : lim, flush chosen, finishing and R->nf updated *)
Definition LP1 (Rp sp : val) (api : Z) (vosn : val) (gv : globals) (rs : rsetup) (ls : lstate)
    (aout plev pstrat psel lim flush : Z) : environ -> mpred :=
  PROP (ls_pos ls <= lim <= Zlength (rs_data rs); 0 <= flush <= 5;
        forall R, ls_fin ls = Some R -> flush = 4 /\ lim = ls_nf ls)
  LOCAL (temp _lim (vi lim); temp _flush (vi flush); temp _finishing (vi (if flush =? 4 then 1 else 0));
         temp _psel (Vint (Int.repr psel)); temp _pstrat (Vint (Int.repr pstrat)); temp _plev (Vint (Int.repr plev));
         temp _aout (Vint (Int.repr aout)); temp _pos (vi (ls_pos ls));
         temp _R Rp; temp _s sp; temp _api (vi api); lvar _osnap (tptr tuchar) vosn; gvars gv)
  SEP (field_at Ews t_drun (DOT _level) (vi (rs_level rs)) Rp;
       field_at Ews t_drun (DOT _method) (vi (rs_method rs)) Rp;
       field_at Ews t_drun (DOT _wbits) (vi (rs_wbits rs)) Rp;
       field_at Ews t_drun (DOT _mem) (vi (rs_mem rs)) Rp;
       field_at Ews t_drun (DOT _strategy) (vi (rs_strategy rs)) Rp;
       field_at Ews t_drun (DOT _init) (vi 0) Rp;
       field_at Ews t_drun (DOT _wrap) (vi (wrap_of (rs_wbits rs))) Rp;
       field_at Ews t_drun (DOT _wb) (vi (wb_of (rs_wbits rs))) Rp;
       field_at Ews t_drun (DOT _data) (rs_datap rs) Rp;
       field_at Ews t_drun (DOT _n) (vi (Zlength (rs_data rs))) Rp;
       field_at Ews t_drun (DOT _nf) (vi (if flush =? 4 then lim else ls_nf ls)) Rp;
       field_at Ews t_drun (DOT _dict) (rs_dictp rs) Rp;
       field_at Ews t_drun (DOT _dlen) (vi (Zlength (rs_dict rs))) Rp;
       field_at Ews t_drun (DOT _dict_set) (vi (ls_dset ls)) Rp;
       field_at Ews t_drun (DOT _head_set) (vi (ls_hset ls)) Rp;
       field_at Ews t_drun (DOT _xf) (rs_xfp rs) Rp;
       field_at Ews t_drun (DOT _nf_) (rs_nfp rs) Rp;
       field_at Ews t_drun (DOT _cf) (rs_cfp rs) Rp;
       field_at Ews t_drun (DOT _xlen) (vi (Zlength (rs_xf rs))) Rp;
       field_at Ews t_drun (DOT _nl) (vi (Zlength (rs_nm rs))) Rp;
       field_at Ews t_drun (DOT _cl) (vi (Zlength (rs_cm rs))) Rp;
       field_at Ews t_drun (DOT _comp) (rs_compp rs) Rp;
       field_at Ews t_drun (DOT _clen) (vl (Zlength (ls_O ls))) Rp;
       field_at Ews t_drun (DOT _ended) (vi 0) Rp;
       field_at Ews t_drun (DOT _api_ok) (vi 1) Rp; drun_pad Rp; strm_pad sp;
       api_fields sp (ls_nin ls) (ls_ain ls) (ls_tin ls) (ls_nout ls) (ls_aout ls) (ls_tout ls) (ls_msgv ls)
         (ls_adler ls);
       data_at_ Tsh (tptr tuchar) vosn; hpart (ls_hset ls) Rp; dstream 2 (Some (ls_s ls)) sp (ls_ghp ls) gv;
       hdr_at (Some (ls_s ls)) (ls_ghp ls) (hx_of rs);
       obj (rs_datap rs) (rs_data rs); obj (rs_dictp rs) (rs_dict rs);
       comp_at (ls_O ls) (rs_compp rs); mem_mgr gv; deflate_globals gv; TT; version_at gv vlit).

Lemma lp_ptr_cs sh p : @data_at_ DCS.CS sh (tptr tuchar) p = @data_at_ CS sh (tptr tuchar) p.
Proof.
  unfold data_at_. apply equal_f. apply (@data_at_change_composite _ _ CC_dcs); [ apply JMeq_refl | reflexivity ].
Qed.

Lemma lp_vp (cs1 cs2 : compspecs) n (v : list val) p Q :
  @malloc_token cs1 Ews (tarray tuchar n) p * @data_at cs2 Ews (tarray tuchar n) v p * Q |-- valid_pointer p.
Proof.
  destruct (zlt 0 n).
  - apply sepcon_valid_pointer1. apply sepcon_valid_pointer2.
    apply data_at_valid_ptr; auto. simpl. rep_lia.
  - apply sepcon_valid_pointer1. apply sepcon_valid_pointer1.
    apply malloc_token_valid_pointer. simpl. rep_lia.
Qed.

Ltac lp_tc_null :=
  apply denote_tc_test_eq_split; [ | apply valid_pointer_zero64; auto ];
  first [ eapply derives_trans; [ | eapply (lp_vp DCS.CS DCS.CS _ _ _ TT) ]; solve [cancel]
        | eapply derives_trans; [ | eapply (lp_vp CS CS _ _ _ TT) ]; solve [cancel] ].

Ltac lp_ret_tac HM Hh :=
  forward; Exists 0; unfold run_post; rewrite Z.eqb_refl; cbv iota; entailer!;
  match goal with |- context [drun_rest ?rs ?i ?w ?b ?nf ?ds ?hs ?cl ?en ?Rp] =>
  match goal with |- context [dstream 2 (Some ?s) ?sp ?ghp ?gv] =>
  match goal with |- context [api_fields ?sp ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8] =>
    sep_apply (lp_ret0 rs i w b nf ds hs cl en Rp s ghp sp gv a1 a2 a3 a4 a5 a6 a7 a8 HM Hh)
  end end end;
  cancel.

Lemma loop_pre_ok {Espec : OracleKind} I Iend Rp sp api vosn gv rs ls :
  run_mem_ok ->
  (forall ci, semax Delta_r (B1 I Iend Rp sp api vosn gv rs ls ci) lsuf21 (Rbody I Iend Rp sp api vosn gv rs)) ->
  semax Delta_r (J_at I Iend Rp sp api vosn gv rs ls) run_lbody (Rbody I Iend Rp sp api vosn gv rs).
Proof.
  intros HM HB.
  unfold J_at, run_lbody, J_ok, lsep, Rbody, POST_r. Intros.
  assert (HDn : Zlength (rs_data rs) <= 1048576) by (unfold rs_ok in H; tauto).
  assert (HDb : bytes (rs_data rs)) by (unfold rs_ok in H; tauto).
  assert (HDp : isptr (rs_datap rs)) by (unfold rs_ok in H; tauto).
  assert (HJ : J_ok I Iend Rp api rs ls) by (unfold J_ok; tauto).
  abbreviate_semax.
  forward.
  forward_call tt. Intros nlim.
  forward_call tt. Intros aout. forward_call tt. Intros fsel. forward_call tt. Intros plev.
  forward_call tt. Intros pstrat. forward_call tt. Intros psel.
  unfold drun_rest. Intros. unfold COMP_MAX in *.
  forward_if (temp _t'56 (vi (if ((aout <=? 1048576) && (aout <=? 4194304 - Zlength (ls_O ls)))%bool then 1 else 0))).
  { forward. unfold vl. forward.
    entailer!.
    apply lp_t56; rep_lia. }
  { forward.
    entailer!.
    change (Int.unsigned (Int.shl (Int.repr 1) (Int.repr 20))) with 1048576 in *.
    replace (aout <=? 1048576) with false by (symmetry; apply Z.leb_gt; lia). reflexivity. }
  forward_call (Int.repr (if ((aout <=? 1048576) && (aout <=? 4194304 - Zlength (ls_O ls)))%bool then 1 else 0)).
  Intros.
  match goal with Hz : Int.repr _ <> Int.zero |- _ => rename Hz into HA end.
  assert (HAo : aout <= 1048576 /\ aout <= 4194304 - Zlength (ls_O ls)).
  { destruct ((aout <=? 1048576) && (aout <=? 4194304 - Zlength (ls_O ls)))%bool eqn:E;
      [ rewrite andb_true_iff, !Z.leb_le in E; lia | contradiction ]. }
  clear HA.
  forward.
  forward_if (EX lim : Z, EX flush : Z, LP1 Rp sp api vosn gv rs ls aout plev pstrat psel lim flush).
  { (* finishing *)
    destruct (ls_fin ls) as [Rf|] eqn:EF; [ | simpl in *; contradiction ].
    destruct H7 as [[H7 _] | H7]; [ discriminate | ].
    forward. forward.
    Exists (ls_nf ls) 4. unfold LP1. entailer!. }
  { (* not finishing *)
    assert (EF : ls_fin ls = None) by (destruct (ls_fin ls); [ simpl in *; discriminate | reflexivity ]).
    rewrite EF in H7 |- *. destruct H7 as [[_ Hnf] | H7]; [ | discriminate ].
    forward_if (temp _t'57 (vi (if ((ls_pos ls <=? nlim) && (nlim <=? Zlength (rs_data rs)))%bool then 1 else 0))).
    { forward. forward.
      entailer!.
      try rewrite Int.unsigned_repr in * by rep_lia.
      lp_bool. }
    { forward.
      entailer!.
      try rewrite Int.unsigned_repr in * by rep_lia.
      lp_bool. }
    forward_call (Int.repr (if ((ls_pos ls <=? nlim) && (nlim <=? Zlength (rs_data rs)))%bool then 1 else 0)).
    Intros.
    match goal with Hz : Int.repr _ <> Int.zero |- _ => rename Hz into HA end.
    assert (HN : ls_pos ls <= nlim <= Zlength (rs_data rs)).
    { destruct ((ls_pos ls <=? nlim) && (nlim <=? Zlength (rs_data rs)))%bool eqn:E;
        [ rewrite andb_true_iff, !Z.leb_le in E; lia | contradiction ]. }
    clear HA.
    forward_if (temp _t'58 (vi (if ((0 <=? Int.signed (Int.repr fsel)) && (Int.signed (Int.repr fsel) <=? 5))%bool then 1 else 0))).
    { forward.
      entailer!.
      unfold Int.lt; change (Int.signed (Int.repr 5)) with 5; lp_bool. }
    { forward.
      entailer!.
      lp_bool. }
    forward_call (Int.repr (if ((0 <=? Int.signed (Int.repr fsel)) && (Int.signed (Int.repr fsel) <=? 5))%bool then 1 else 0)).
    Intros.
    match goal with Hz : Int.repr _ <> Int.zero |- _ => rename Hz into HA end.
    assert (HFl : 0 <= Int.signed (Int.repr fsel) <= 5).
    { destruct ((0 <=? Int.signed (Int.repr fsel)) && (Int.signed (Int.repr fsel) <=? 5))%bool eqn:E;
        [ rewrite andb_true_iff, !Z.leb_le in E; lia | contradiction ]. }
    clear HA.
    assert (HFs : Int.signed (Int.repr fsel) = fsel).
    { unfold Int.signed in *. rewrite Int.unsigned_repr in * by rep_lia.
      destruct (zlt fsel Int.half_modulus); rep_lia. }
    rewrite HFs in HFl.
    forward.
    forward_if.
    { forward. forward.
      Exists nlim fsel. unfold LP1.
      entailer!. }
    { forward.
      Exists nlim fsel. unfold LP1.
      match goal with Hn : fsel <> 4 |- _ => rewrite (proj2 (Z.eqb_neq fsel 4) Hn) end.
      entailer!. } }
  Intros lim flush. unfold LP1. Intros.
  forward.
  unfold obj. Intros.
  forward.
  sep_apply (lp_fold rs (vi 0) (vi (wrap_of (rs_wbits rs))) (vi (wb_of (rs_wbits rs)))
               (if flush =? 4 then lim else ls_nf ls) (ls_dset ls) (ls_hset ls) (Zlength (ls_O ls)) 0 Rp).
  forward_call (offset_val (ls_pos ls) (rs_datap rs), Ews, rs_datap rs, ls_pos ls, Zlength (rs_data rs),
                map vi (rs_data rs), lim - ls_pos ls, sublist (ls_pos ls) lim (rs_data rs), gv).
  { entailer!. simpl.
    destruct (rs_datap rs); try contradiction. unfold vi; simpl. f_equal. f_equal. f_equal.
    rewrite Ptrofs.mul_commut, Ptrofs.mul_one. unfold Ptrofs.of_intu, Ptrofs.of_int.
    rewrite Int.unsigned_repr by rep_lia. reflexivity. }
  { rewrite (bytes_cs DCS.CS CS). cancel. }
  { unfold cbuf_ok. split; [reflexivity | ]. split; [auto | ]. split; [lia | ]. split; [lia | ].
    split; [rewrite Zlength_sublist by lia; lia | ]. split.
    - unfold is_bytes. apply Forall_sublist. eapply Forall_impl; [ | exact HDb ]. simpl; intros; rep_lia.
    - replace (ls_pos ls + (lim - ls_pos ls)) with lim by lia. unfold bytes_rep. rewrite sublist_map. reflexivity. }
  Intros ib. forward.
  forward_call (aout, vosn, Tsh, gv).
  { rewrite lp_ptr_cs. cancel. }
  Intros vret. destruct vret as [[vob q] bs]. cbn [fst snd].
  Intros.
  destruct (eq_dec ib nullval) as [Hib | Hib].
  { (* ib = NULL: return 0 *)
    forward_if (temp _t'61 (vi 1)).
    { forward. entailer!. }
    { forward. entailer!. }
    forward_if.
    { lp_ret_tac HM H9. }
    { match goal with H : Int.repr 1 = Int.zero |- _ => discriminate H end. } }
  destruct (eq_dec ib nullval); [ contradiction | ]. Intros.
  destruct (eq_dec vob nullval) as [Hob | Hob].
  { (* ob = NULL: return 0 *)
    forward_if (temp _t'61 (vi 1)).
    { lp_tc_null. }
    { contradiction. }
    { forward. entailer!. }
    forward_if.
    { lp_ret_tac HM H9. }
    { match goal with H : Int.repr 1 = Int.zero |- _ => discriminate H end. } }
  Intros.
  forward_if (temp _t'61 (vi 0)).
  { lp_tc_null. }
  { contradiction. }
  { forward. entailer!. lp_tc_null.
    entailer!. destruct vob; try contradiction; reflexivity. }
  forward_if.
  { match goal with H : Int.repr 0 <> Int.zero |- _ => contradiction H; reflexivity end. }
  rewrite api_fields_L. unfold api_fieldsL. Intros.
  forward. forward. forward. forward.
  forward. forward.
  forward_if (temp _t'62 (vi (if flush =? 4 then 0 else if psel =? 0 then 1 else 0))).
  { forward.
    match goal with H : Int.repr (if flush =? 4 then 1 else 0) = Int.zero |- _ =>
      destruct (flush =? 4); [ discriminate H | ] end.
    entailer!.
    destruct (zeq psel 0) as [-> | Hp]; [ reflexivity | ].
    rewrite (proj2 (Z.eqb_neq _ _) Hp). reflexivity. }
  { forward.
    match goal with H : Int.repr (if flush =? 4 then 1 else 0) <> Int.zero |- _ =>
      destruct (flush =? 4); [ | contradiction H; reflexivity ] end.
    entailer!. }
  forward.
  eapply semax_pre; [ | apply (HB (mkCI lim aout flush (negb (flush =? 4) && (psel =? 0))%bool
                                   (Int.signed (Int.repr plev)) (Int.signed (Int.repr pstrat)) ib vob q bs)) ].
  unfold B1, B_loc, lsep, obj, ci_inb, ci_nf, ci_fin.
  cbn [ci_lim ci_aout ci_flush ci_params ci_plev ci_pstrat ci_ib ci_ob ci_q ci_bs].
  rewrite api_fields_L. unfold api_fieldsL.
  rewrite ?tok_tuchar_cs, ?(bytes_cs DCS.CS CS).
  rewrite Zlength_sublist by lia.
  change Z_FINISH with 4.
  entailer!.
  split; [ | split; [ split; [ | split ] | ] ].
  - unfold ci_ok. cbn [ci_lim ci_aout ci_flush ci_params ci_plev ci_pstrat ci_ib ci_ob ci_q ci_bs].
    cbn [fst snd] in *.
    split; [ exact HJ | ]. split; [ lia | ].
    split; [ match goal with H : forall R, ls_fin ls = Some R -> _ |- _ => exact H end | ].
    split; [ lia | ]. split; [ rep_lia | ]. split; [ unfold COMP_MAX; lia | ].
    split.
    { intros Hp. apply andb_true_iff in Hp as [Hp1 _]. apply negb_true_iff, Z.eqb_neq in Hp1.
      split; [ | exact Hp1 ].
      match goal with H : forall R, ls_fin ls = Some R -> _ |- _ => rename H into HF end.
      destruct (ls_fin ls) as [R0|] eqn:EF; [ exfalso | reflexivity ].
      first [ destruct (HF R0 EF) | destruct (HF R0 eq_refl) ]; contradiction. }
    split; [ pose proof (Int.signed_range (Int.repr plev)); unfold s32; rep_lia | ].
    split; [ pose proof (Int.signed_range (Int.repr pstrat)); unfold s32; rep_lia | ].
    split; [ reflexivity | ].
    split; [ match goal with H : is_bytes bs |- _ => unfold bytes; eapply Forall_impl; [ | exact H ];
               simpl; intros; rep_lia end | ].
    split; [ match goal with H : malloc_compatible _ ib |- _ => clear - H; destruct ib; simpl in *; tauto end | ].
    split; [ match goal with H : malloc_compatible _ vob |- _ => clear - H; destruct vob; simpl in *; tauto end | ].
    match goal with H : malloc_compatible _ q |- _ => clear - H; destruct q; simpl in *; tauto end.
  - destruct (flush =? 4); destruct (psel =? 0); reflexivity.
  - unfold vi. rewrite Int.repr_signed. reflexivity.
  - unfold vi. rewrite Int.repr_signed. reflexivity.
  - unfold u32_ok. rep_lia.
Qed.

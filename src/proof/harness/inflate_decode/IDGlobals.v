(* Law inflate_decode: the resources of the program's global variables that main needs (R), out of
   globvars2pred: inflate's read-only tables (Spec5.tables_rep), crc32's table, inflate.c's ZLIB_VERSION literal,
   the harness's "1.3.2" literal, the first byte of each of inflate's / inffast's message literals (as law
   inflate_codes, Globals.v there), and the harness's static tables: deflate_ref.h's ref_lbase/lext/dbase/dext
   (DRefSpec.dref_tabs id_tabs), cl_order, and main's gzip header gz. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Assembly.
Require Import Zlib.proof.inflate_api.Spec5.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.harness.inflate_decode.IDLawCS.
Require Import Zlib.proof.harness.inflate_common.DRefSpec.
Require Zlib.harness.x_inflate_decode.code.
Require Zlib.inflate.code Zlib.inffast.code Zlib.inftrees.code Zlib.crc32.code Zlib.zutil.code.
Require Zlib.units.Inflate Zlib.units.Inftrees.
Module HD := Zlib.harness.x_inflate_decode.code.

(* every message strm->msg may hold *)
Definition id_all_msgs : list msgid :=
  [M_hdr_check; M_method; M_wsize; M_hflags; M_hcrc; M_btype; M_stored; M_toomany; M_cl_set; M_repeat; M_eob;
   M_ll_set; M_d_set; M_ll_code; M_d_code; M_far; M_dcheck; M_lcheck; F_far; F_d_code; F_ll_code].

Definition id_msg_lits (gv: globals) : mpred :=
  fold_right sepcon emp (map (fun m => mapsto_ Ers tschar (gv (msg_ident m))) id_all_msgs).

(* the harness's "1.3.2" *)
Definition id_hversion_lit (gv: globals) : mpred :=
  data_at Ers (tarray tschar 6) (map (fun c => Vint (Int.repr c)) [49; 46; 51; 46; 50; 0])
    (gv HD.___stringlit_x_inflate_decode_1).

(* main's minimal gzip header *)
Definition gz_vals : list Z := [31; 139; 8; 0; 0; 0; 0; 0; 0; 3].

Definition R (gv: globals) : mpred :=
  (tables_rep Ers gv * crc_table_at Ers gv * version_lit gv * id_hversion_lit gv * id_msg_lits gv *
   dref_tabs gv Ers id_tabs * data_at Ers (tarray tuchar 19) (zvals clorder) (gv HD._cl_order) *
   data_at Ers (tarray tuchar 10) (zvals gz_vals) (gv HD._gz))%logic.

(* ---------------------------------------------------------------------------------------------- *)
(* helpers: globvar2pred of initialised read-only arrays                                          *)

(* integer arrays (Init_int8/16/32 data) *)
Definition asint (sz: intsize) (dl: list init_data) : option (list int) :=
  fold_right (fun d r =>
    match r with
    | None => None
    | Some l =>
      match sz, d with
      | I8, Init_int8 i | I16, Init_int16 i | I32, Init_int32 i => Some (i :: l)
      | _, _ => None
      end
    end) (Some []) dl.

Lemma asint_ok sz dl data : asint sz dl = Some data -> dl = map (inttype2init_data sz) data.
Proof.
  revert data; induction dl as [|d dl IH]; intros data H; simpl in H.
  - inv H; reflexivity.
  - destruct (asint sz dl) eqn:E; [|discriminate].
    destruct sz, d; try discriminate; inv H; simpl; f_equal; auto.
Qed.

Lemma idl2_star_int {cs: compspecs} Delta gv sh sz : notboolsize sz -> forall (data: list int) v,
  init_data_list2pred gv (map (inttype2init_data sz) data) sh v =
  id2pred_star Delta gv sh v (map (inttype2init_data sz) data).
Proof.
  intros NB; induction data; intros; simpl; auto.
  rewrite IHdata. destruct sz; try contradiction; reflexivity.
Qed.

Lemma gv_arr {cs: compspecs} gv sh sz sign (data: list int) p :
  notboolsize sz -> data <> [] -> sizeof (Tint sz sign noattr) * Zlength data < Ptrofs.modulus ->
  (forall b o, p = Vptr b o -> o = Ptrofs.zero) ->
  init_data_list2pred gv (map (inttype2init_data sz) data) sh p
  |-- data_at sh (tarray (Tint sz sign noattr) (Zlength data)) (map (Vint oo Cop.cast_int_int sz sign) data) p.
Proof.
  intros NB NE R HP.
  destruct p; try (destruct data as [|d data]; [contradiction|]; destruct sz; try contradiction;
                   simpl; unfold mapsto; simpl; rewrite FF_sepcon; apply FF_left).
  specialize (HP b i eq_refl); subst i.
  rewrite (idl2_star_int empty_tycontext _ _ _ NB).
  pose proof (id2pred_star_ZnthV_Tint empty_tycontext gv sh (Zlength data) (Vptr b Ptrofs.zero) data
               sz sign (map (inttype2init_data sz) data) NB) as H.
  rewrite Zlength_map in H. specialize (H eq_refl eq_refl any_environ).
  eapply derives_trans; [ | apply H]. unfold_lift. simpl.
  repeat apply andp_right; try apply derives_refl; apply prop_right.
  - auto.
  - destruct sz, sign; try contradiction; (eapply align_compatible_rec_by_value; [reflexivity | ]);
    rewrite Ptrofs.unsigned_zero; apply Z.divide_0_r.
  - rewrite Ptrofs.unsigned_zero. pose proof (Zlength_nonneg data).
    destruct sz; try contradiction; simpl in R |- *; lia.
Qed.

Fixpoint leqb {A} (eqb: A -> A -> bool) (l1 l2: list A) : bool :=
  match l1, l2 with
  | [], [] => true
  | a :: r1, b :: r2 => (eqb a b && leqb eqb r1 r2)%bool
  | _, _ => false
  end.

Definition isz (sz: intsize) : Z := match sz with I8 | IBool => 1 | I16 => 2 | I32 => 4 end.

Definition int_glob_ok (sz: intsize) (sign: signedness) (v: globvar type) (n: Z) (zs: list Z) : bool :=
  match asint sz (gvar_init v) with
  | Some data =>
      negb (gvar_volatile v) && gvar_readonly v && (0 <? Zlength data) &&
      (isz sz * Zlength data <? Ptrofs.modulus) && (n =? Zlength data) &&
      leqb Z.eqb (map (fun i => Int.unsigned (Cop.cast_int_int sz sign i)) data) zs
  | None => false
  end%bool.

Lemma leqb_Z_ok (l1 l2: list Z) : leqb Z.eqb l1 l2 = true -> l1 = l2.
Proof.
  revert l2; induction l1 as [|a l1 IH]; intros [|b l2] E; simpl in E; try discriminate; auto.
  apply andb_true_iff in E as [E1 E2]. apply Z.eqb_eq in E1. subst. f_equal; auto.
Qed.

Lemma int_glob {cs: compspecs} gv i v sz sign n zs :
  notboolsize sz -> int_glob_ok sz sign v n zs = true ->
  (forall b o, gv i = Vptr b o -> o = Ptrofs.zero) ->
  globvar2pred gv (i, v) |-- data_at Ers (tarray (Tint sz sign noattr) n) (map (fun z => Vint (Int.repr z)) zs) (gv i).
Proof.
  intros NB OK HP. unfold int_glob_ok in OK.
  destruct (asint sz (gvar_init v)) as [data|] eqn:E; [|discriminate].
  rewrite !andb_true_iff in OK. destruct OK as [[[[[V RO] L0] LM] N] EQ].
  apply negb_true_iff in V. apply Z.ltb_lt in L0. apply Z.ltb_lt in LM. apply Z.eqb_eq in N.
  apply leqb_Z_ok in EQ. subst n zs.
  unfold globvar2pred; simpl. rewrite V, RO. apply asint_ok in E. rewrite E.
  eapply derives_trans; [apply (gv_arr gv _ sz sign); auto;
    try (intro X; subst; discriminate); destruct sz, sign; try contradiction; simpl; simpl in LM; lia | ].
  apply derives_refl'. f_equal. rewrite map_map. apply map_ext. intros a.
    unfold Basics.compose. rewrite Int.repr_unsigned. reflexivity.
Qed.

Lemma data_at_tschar_mapsto_ {cs: compspecs} sh v p : data_at sh tschar v p |-- mapsto_ sh tschar p.
Proof.
  assert_PROP (field_compatible tschar [] p) by entailer!.
  rewrite <- (mapsto_data_at' sh tschar v v p) by auto. apply mapsto_mapsto_.
Qed.

Lemma first_byte {cs: compspecs} sh n (l: list val) p :
  1 <= n -> Zlength l = n -> data_at sh (tarray tschar n) l p |-- mapsto_ sh tschar p * TT.
Proof.
  intros H1 H2. unfold tarray. rewrite (split2_data_at_Tarray_tschar sh n 1 l p) by lia.
  rewrite sublist_one by lia. rewrite data_at_tschar_singleton_array_eq.
  sep_apply data_at_tschar_mapsto_. cancel.
Qed.

Lemma str_first gv i v n zs :
  int_glob_ok I8 Signed v n zs = true ->
  (forall b o, gv i = Vptr b o -> o = Ptrofs.zero) ->
  globvar2pred gv (i, v) |-- mapsto_ Ers tschar (gv i) * TT.
Proof.
  intros OK HP.
  assert (L: 1 <= n /\ Zlength zs = n).
  { unfold int_glob_ok in OK. destruct (asint I8 (gvar_init v)) as [data|]; [|discriminate].
    rewrite !andb_true_iff in OK. destruct OK as [[[[[_ _] L0] _] N] EQ].
    apply Z.ltb_lt in L0. apply Z.eqb_eq in N. apply leqb_Z_ok in EQ. subst. rewrite Zlength_map. lia. }
  sep_apply (@int_glob CS gv i v I8 Signed n zs I OK HP).
  apply first_byte; [lia | rewrite Zlength_map; lia].
Qed.

(* arrays of struct code (inftrees.c's lenfix, distfix: Init_int8 op, Init_int8 bits, Init_int16 val) *)
Section Codes.
#[local] Existing Instance Zlib.units.Inflate.CS.
Definition tcode := Tstruct Zlib.inflate.code.___gp_code noattr.

Lemma fc_field p f : field_compatible tcode [] p ->
  In f [Zlib.inflate.code._op; Zlib.inflate.code._bits; Zlib.inflate.code._val] -> field_compatible tcode (DOT f) p.
Proof. intros FC Hf. apply field_compatible_cons. split; auto. Qed.

Lemma code_elem sh p (a1 a2 a3: val) : field_compatible tcode [] p ->
  mapsto sh tuchar p a1 * mapsto sh tuchar (offset_val 1 p) a2 * mapsto sh tushort (offset_val 2 p) a3
  |-- data_at sh tcode (a1,(a2,a3)) p.
Proof.
  intros FC. unfold_data_at (data_at _ _ _ p).
  erewrite <- (mapsto_field_at sh tcode (DOT Zlib.inflate.code._op) a1 _ p);
    [ | reflexivity | reflexivity | apply fc_field; simpl; tauto | apply JMeq_refl].
  erewrite <- (mapsto_field_at sh tcode (DOT Zlib.inflate.code._bits) a2 _ p);
    [ | reflexivity | reflexivity | apply fc_field; simpl; tauto | apply JMeq_refl].
  erewrite <- (mapsto_field_at sh tcode (DOT Zlib.inflate.code._val) a3 _ p);
    [ | reflexivity | reflexivity | apply fc_field; simpl; tauto | apply JMeq_refl].
  rewrite !field_address_offset by (apply fc_field; simpl; tauto).
  simpl. rewrite isptr_offset_val_zero by (destruct FC; auto). cancel.
Qed.

Lemma align_code z : (2 | z) -> align_compatible_rec cenv_cs tcode z.
Proof.
  intros H2. eapply align_compatible_rec_Tstruct; [reflexivity|reflexivity|].
  intros i t z' Hf Ho. simpl in Hf, Ho.
  repeat if_tac in Hf; inv Hf; simpl in Ho; rewrite ?if_true in Ho by auto;
    rewrite ?if_false in Ho by (try (intro X; inv X); auto); inv Ho;
    eapply align_compatible_rec_by_value; try reflexivity; simpl; try apply Z.divide_1_l.
  apply Z.divide_add_r; auto. apply Z.divide_refl.
Qed.

Definition cinit (e: int * int * int) : list init_data :=
  [Init_int8 (fst (fst e)); Init_int8 (snd (fst e)); Init_int16 (snd e)].
Definition crep (e: int * int * int) : val * (val * val) :=
  (Vint (Int.zero_ext 8 (fst (fst e))), (Vint (Int.zero_ext 8 (snd (fst e))), Vint (Int.zero_ext 16 (snd e)))).

Lemma codes_arr gv sh : forall (l: list (int * int * int)) b ofs,
  Ptrofs.unsigned ofs + 4 * Zlength l < Ptrofs.modulus -> (2 | Ptrofs.unsigned ofs) ->
  init_data_list2pred gv (flat_map cinit l) sh (Vptr b ofs)
  |-- data_at sh (tarray tcode (Zlength l)) (map crep l) (Vptr b ofs).
Proof.
  induction l as [|x l IH]; intros b ofs H1 H2.
  - simpl. apply data_at_zero_array; simpl; auto.
  - pose proof (Zlength_nonneg l) as Hn. rewrite Zlength_cons in *.
    change (map crep (x :: l)) with ([crep x] ++ map crep l).
    rewrite (@split2_data_at_Tarray_app Zlib.units.Inflate.CS 1 (Z.succ (Zlength l)) sh tcode [crep x] (map crep l))
      by (rewrite ?Zlength_map; reflexivity || lia).
    rewrite (@data_at_singleton_array_eq Zlib.units.Inflate.CS sh tcode (crep x)) by reflexivity.
    rewrite field_address0_offset.
    2: { unfold field_compatible0. repeat split; auto; try lia.
         - simpl. rewrite Z.max_r by lia. lia.
         - hnf. apply align_compatible_rec_Tarray. intros i Hi.
           apply align_code. apply Z.divide_add_r; auto. simpl sizeof.
           apply Z.divide_mul_l. exists 2; reflexivity. }
    destruct x as [[a1 a2] a3]. cbn [flat_map app cinit fst snd init_data_list2pred init_data2pred init_data_size].
    rewrite !offset_offset_val. simpl nested_field_offset. change (1 + 1) with 2. change (2 + 2) with 4.
    rewrite <- !sepcon_assoc.
    apply sepcon_derives.
    + apply code_elem. repeat split; auto; [simpl; lia | hnf; apply align_code; auto].
    + replace (Z.succ (Zlength l) - 1) with (Zlength l) by lia.
      simpl offset_val. apply IH.
      * rewrite Ptrofs.add_unsigned, Ptrofs.unsigned_repr; rewrite ?Ptrofs.unsigned_repr; rep_lia.
      * rewrite Ptrofs.add_unsigned, Ptrofs.unsigned_repr; rewrite ?Ptrofs.unsigned_repr; try rep_lia.
        apply Z.divide_add_r; auto. exists 2; reflexivity.
Qed.

Fixpoint ascodes3 (dl: list init_data) : option (list (int * int * int)) :=
  match dl with
  | [] => Some []
  | Init_int8 a :: Init_int8 b :: Init_int16 c :: r =>
      match ascodes3 r with Some l => Some ((a, b, c) :: l) | None => None end
  | _ => None
  end.

Lemma ascodes3_ok : forall dl l, ascodes3 dl = Some l -> dl = flat_map cinit l.
Proof.
  fix IH 1. intros dl l H.
  destruct dl as [|d1 [|d2 [|d3 r]]]; simpl in H.
  - inv H; reflexivity.
  - destruct d1; discriminate.
  - destruct d1, d2; discriminate.
  - destruct d1; try discriminate. destruct d2; try discriminate. destruct d3; try discriminate.
    destruct (ascodes3 r) eqn:E; inv H. simpl. rewrite (IH r l0 E). reflexivity.
Qed.

Definition code_glob_ok (v: globvar type) (n: Z) (es: list (Z * Z * Z)) : bool :=
  match ascodes3 (gvar_init v) with
  | Some l =>
      negb (gvar_volatile v) && gvar_readonly v && (0 <? Zlength l) &&
      (4 * Zlength l <? Ptrofs.modulus) && (n =? Zlength l) &&
      leqb (fun x y => (fst (fst x) =? fst (fst y)) && (snd (fst x) =? snd (fst y)) && (snd x =? snd y))
        (map (fun e => (Int.unsigned (Int.zero_ext 8 (fst (fst e))), Int.unsigned (Int.zero_ext 8 (snd (fst e))),
                        Int.unsigned (Int.zero_ext 16 (snd e)))) l) es
  | None => false
  end%bool.

Definition zrep (e: Z * Z * Z) : val * (val * val) :=
  (Vint (Int.repr (fst (fst e))), (Vint (Int.repr (snd (fst e))), Vint (Int.repr (snd e)))).

Lemma code_glob gv i v n es :
  code_glob_ok v n es = true ->
  (forall b o, gv i = Vptr b o -> o = Ptrofs.zero) ->
  globvar2pred gv (i, v) |-- data_at Ers (tarray tcode n) (map zrep es) (gv i).
Proof.
  intros OK HP. unfold code_glob_ok in OK.
  destruct (ascodes3 (gvar_init v)) as [l|] eqn:E; [|discriminate].
  rewrite !andb_true_iff in OK. destruct OK as [[[[[V RO] L0] LM] N] EQ].
  apply negb_true_iff in V. apply Z.ltb_lt in L0. apply Z.ltb_lt in LM. apply Z.eqb_eq in N. subst n.
  assert (ES: map crep l = map zrep es).
  { revert es EQ. clear. induction l as [|[[a b] c] l IH]; intros [|e es] EQ; simpl in EQ; try discriminate; auto.
    destruct e as [[x y] z]. simpl in EQ. rewrite !andb_true_iff in EQ. destruct EQ as [[[E1 E2] E3] EQ].
    apply Z.eqb_eq in E1, E2, E3. simpl. f_equal; auto.
    unfold crep, zrep; simpl. subst. rewrite !Int.repr_unsigned. reflexivity. }
  unfold globvar2pred; simpl. rewrite V, RO. apply ascodes3_ok in E. rewrite E.
  destruct (gv i) eqn:G;
    try (destruct l as [|[[a b] c] l]; [rewrite Zlength_nil in L0; lia|];
         simpl; unfold mapsto; simpl; rewrite FF_sepcon; apply FF_left).
  specialize (HP b i0 eq_refl); subst i0.
  rewrite <- ES. apply codes_arr; rewrite ?Ptrofs.unsigned_zero; [lia | apply Z.divide_0_r].
Qed.
End Codes.

Definition str_ok (v: globvar type) : bool :=
  match asint I8 (gvar_init v) with
  | Some data => int_glob_ok I8 Signed v (Zlength data) (map (fun i => Int.unsigned (Cop.cast_int_int I8 Signed i)) data)
  | None => false
  end.

Lemma str_glob gv i v : str_ok v = true ->
  (forall b o, gv i = Vptr b o -> o = Ptrofs.zero) ->
  globvar2pred gv (i, v) |-- mapsto_ Ers tschar (gv i) * TT.
Proof.
  unfold str_ok. destruct (asint I8 (gvar_init v)); [|discriminate]. apply str_first.
Qed.


(* the program's globals *)
Lemma id_W_vars : QPprog_vars p =
  [(HD._gz, HD.v_gz);
   (Zlib.inflate.code._order, Zlib.inflate.code.v_order);
   (HD._cl_order, HD.v_cl_order);
   (Zlib.crc32.code._crc_table, Zlib.crc32.code.v_crc_table);
   (Zlib.inftrees.code._inflate_copyright, Zlib.inftrees.code.v_inflate_copyright);
   (Zlib.inflate.code.___stringlit_inflate_8, Zlib.inflate.code.v___stringlit_inflate_8);
   (Zlib.inflate.code.___stringlit_inflate_4, Zlib.inflate.code.v___stringlit_inflate_4);
   (Zlib.inflate.code.___stringlit_inflate_2, Zlib.inflate.code.v___stringlit_inflate_2);
   (Zlib.inflate.code.___stringlit_inflate_6, Zlib.inflate.code.v___stringlit_inflate_6);
   (Zlib.inflate.code.___stringlit_inflate_10, Zlib.inflate.code.v___stringlit_inflate_10);
   (Zlib.inflate.code.___stringlit_inflate_18, Zlib.inflate.code.v___stringlit_inflate_18);
   (Zlib.inflate.code.___stringlit_inflate_14, Zlib.inflate.code.v___stringlit_inflate_14);
   (Zlib.inflate.code.___stringlit_inflate_12, Zlib.inflate.code.v___stringlit_inflate_12);
   (Zlib.inflate.code.___stringlit_inflate_16, Zlib.inflate.code.v___stringlit_inflate_16);
   (Zlib.inflate.code.___stringlit_inflate_1, Zlib.inflate.code.v___stringlit_inflate_1);
   (Zlib.inflate.code.___stringlit_inflate_11, Zlib.inflate.code.v___stringlit_inflate_11);
   (Zlib.inflate.code.___stringlit_inflate_19, Zlib.inflate.code.v___stringlit_inflate_19);
   (Zlib.inflate.code.___stringlit_inflate_15, Zlib.inflate.code.v___stringlit_inflate_15);
   (Zlib.inflate.code.___stringlit_inflate_13, Zlib.inflate.code.v___stringlit_inflate_13);
   (Zlib.inflate.code.___stringlit_inflate_17, Zlib.inflate.code.v___stringlit_inflate_17);
   (Zlib.inflate.code.___stringlit_inflate_9, Zlib.inflate.code.v___stringlit_inflate_9);
   (Zlib.inflate.code.___stringlit_inflate_5, Zlib.inflate.code.v___stringlit_inflate_5);
   (Zlib.inflate.code.___stringlit_inflate_3, Zlib.inflate.code.v___stringlit_inflate_3);
   (Zlib.inflate.code.___stringlit_inflate_7, Zlib.inflate.code.v___stringlit_inflate_7);
   (Zlib.inffast.code.___stringlit_inffast_2, Zlib.inffast.code.v___stringlit_inffast_2);
   (Zlib.inffast.code.___stringlit_inffast_1, Zlib.inffast.code.v___stringlit_inffast_1);
   (Zlib.inffast.code.___stringlit_inffast_3, Zlib.inffast.code.v___stringlit_inffast_3);
   (HD.___stringlit_x_inflate_decode_1, HD.v___stringlit_x_inflate_decode_1);
   (Zlib.zutil.code.___stringlit_zutil_8, Zlib.zutil.code.v___stringlit_zutil_8);
   (Zlib.zutil.code.___stringlit_zutil_4, Zlib.zutil.code.v___stringlit_zutil_4);
   (Zlib.zutil.code.___stringlit_zutil_2, Zlib.zutil.code.v___stringlit_zutil_2);
   (Zlib.zutil.code.___stringlit_zutil_6, Zlib.zutil.code.v___stringlit_zutil_6);
   (Zlib.zutil.code.___stringlit_zutil_10, Zlib.zutil.code.v___stringlit_zutil_10);
   (Zlib.zutil.code.___stringlit_zutil_1, Zlib.zutil.code.v___stringlit_zutil_1);
   (Zlib.zutil.code.___stringlit_zutil_9, Zlib.zutil.code.v___stringlit_zutil_9);
   (Zlib.zutil.code.___stringlit_zutil_5, Zlib.zutil.code.v___stringlit_zutil_5);
   (Zlib.zutil.code.___stringlit_zutil_3, Zlib.zutil.code.v___stringlit_zutil_3);
   (Zlib.zutil.code.___stringlit_zutil_7, Zlib.zutil.code.v___stringlit_zutil_7);
   (Zlib.crc32.code._x2n_table, Zlib.crc32.code.v_x2n_table);
   (HD._x_inflate_decode__ref_lext, HD.v_x_inflate_decode__ref_lext);
   (HD._x_inflate_decode__ref_lbase, HD.v_x_inflate_decode__ref_lbase);
   (HD._x_inflate_decode__ref_dext, HD.v_x_inflate_decode__ref_dext);
   (HD._x_inflate_decode__ref_dbase, HD.v_x_inflate_decode__ref_dbase);
   (Zlib.inftrees.code._lext, Zlib.inftrees.code.v_lext);
   (Zlib.inftrees.code._lenfix, Zlib.inftrees.code.v_lenfix);
   (Zlib.inftrees.code._lbase, Zlib.inftrees.code.v_lbase);
   (Zlib.inftrees.code._distfix, Zlib.inftrees.code.v_distfix);
   (Zlib.inftrees.code._dext, Zlib.inftrees.code.v_dext);
   (Zlib.inftrees.code._dbase, Zlib.inftrees.code.v_dbase);
   (Zlib.zutil.code._z_errmsg, Zlib.zutil.code.v_z_errmsg)].
Proof. vm_compute; reflexivity. Qed.

Lemma lenfix_g gv : (forall b o, gv Zlib.inftrees.code._lenfix = Vptr b o -> o = Ptrofs.zero) ->
  globvar2pred gv (Zlib.inftrees.code._lenfix, Zlib.inftrees.code.v_lenfix)
  |-- @data_at Zlib.units.Inflate.CS Ers (tarray t_code 512) (map ent lenfix_list) (gv g_lenfix).
Proof.
  intros HP. replace (map ent lenfix_list) with (map zrep (map (fun e => (e_op e, e_bits e, e_val e)) lenfix_list))
    by (rewrite map_map; reflexivity).
  apply code_glob; [vm_compute; reflexivity | exact HP].
Qed.

Lemma distfix_g gv : (forall b o, gv Zlib.inftrees.code._distfix = Vptr b o -> o = Ptrofs.zero) ->
  globvar2pred gv (Zlib.inftrees.code._distfix, Zlib.inftrees.code.v_distfix)
  |-- @data_at Zlib.units.Inflate.CS Ers (tarray t_code 32) (map ent distfix_list) (gv g_distfix).
Proof.
  intros HP. replace (map ent distfix_list) with (map zrep (map (fun e => (e_op e, e_bits e, e_val e)) distfix_list))
    by (rewrite map_map; reflexivity).
  apply code_glob; [vm_compute; reflexivity | exact HP].
Qed.

Lemma order_g gv : (forall b o, gv Zlib.inflate.code._order = Vptr b o -> o = Ptrofs.zero) ->
  globvar2pred gv (Zlib.inflate.code._order, Zlib.inflate.code.v_order)
  |-- @data_at Zlib.units.Inflate.CS Ers (tarray tushort 19) (map (fun z => Vint (Int.repr z)) order)
        (gv Zlib.inflate.code._order).
Proof. intros HP. apply (@int_glob Zlib.units.Inflate.CS gv _ _ I16 Unsigned); [exact I | vm_compute; reflexivity | exact HP]. Qed.

Ltac itab_g := intros HP; apply (@int_glob Zlib.units.Inftrees.CS _ _ _ I16 Unsigned); [exact I | vm_compute; reflexivity | exact HP].

Lemma lbase_g gv : (forall b o, gv Zlib.inftrees.code._lbase = Vptr b o -> o = Ptrofs.zero) ->
  globvar2pred gv (Zlib.inftrees.code._lbase, Zlib.inftrees.code.v_lbase)
  |-- @data_at Zlib.units.Inftrees.CS Ers (tarray tushort 31) (Zlib.proof.inftrees.spec.zs_rep Zlib.proof.inftrees.model.lbase)
        (gv Zlib.inftrees.code._lbase).
Proof. itab_g. Qed.
Lemma lext_g gv : (forall b o, gv Zlib.inftrees.code._lext = Vptr b o -> o = Ptrofs.zero) ->
  globvar2pred gv (Zlib.inftrees.code._lext, Zlib.inftrees.code.v_lext)
  |-- @data_at Zlib.units.Inftrees.CS Ers (tarray tushort 31) (Zlib.proof.inftrees.spec.zs_rep Zlib.proof.inftrees.model.lext)
        (gv Zlib.inftrees.code._lext).
Proof. itab_g. Qed.
Lemma dbase_g gv : (forall b o, gv Zlib.inftrees.code._dbase = Vptr b o -> o = Ptrofs.zero) ->
  globvar2pred gv (Zlib.inftrees.code._dbase, Zlib.inftrees.code.v_dbase)
  |-- @data_at Zlib.units.Inftrees.CS Ers (tarray tushort 32) (Zlib.proof.inftrees.spec.zs_rep Zlib.proof.inftrees.model.dbase)
        (gv Zlib.inftrees.code._dbase).
Proof. itab_g. Qed.
Lemma dext_g gv : (forall b o, gv Zlib.inftrees.code._dext = Vptr b o -> o = Ptrofs.zero) ->
  globvar2pred gv (Zlib.inftrees.code._dext, Zlib.inftrees.code.v_dext)
  |-- @data_at Zlib.units.Inftrees.CS Ers (tarray tushort 32) (Zlib.proof.inftrees.spec.zs_rep Zlib.proof.inftrees.model.dext)
        (gv Zlib.inftrees.code._dext).
Proof. itab_g. Qed.

Lemma version_g gv : (forall b o, gv Zlib.inflate.code.___stringlit_inflate_1 = Vptr b o -> o = Ptrofs.zero) ->
  globvar2pred gv (Zlib.inflate.code.___stringlit_inflate_1, Zlib.inflate.code.v___stringlit_inflate_1) |-- version_lit gv.
Proof. intros HP. unfold version_lit. eapply (int_glob _ _ _ I8 Signed); [exact I | vm_compute; reflexivity | exact HP]. Qed.

(* crc32's table (as crc32/Globals.v's crc_table_of_globvar, by int_glob) *)
Lemma crc_g gv : (forall b o, gv Zlib.crc32.code._crc_table = Vptr b o -> o = Ptrofs.zero) ->
  globvar2pred gv (Zlib.crc32.code._crc_table, Zlib.crc32.code.v_crc_table) |-- crc_table_at Ers gv.
Proof.
  intros HP. unfold crc_table_at, Zlib.proof.crc32.Model.crc_table_rep.
  apply (int_glob _ _ _ I32 Unsigned); [exact I | vm_compute; reflexivity | exact HP].
Qed.

Lemma id_hversion_g gv : (forall b o, gv HD.___stringlit_x_inflate_decode_1 = Vptr b o -> o = Ptrofs.zero) ->
  globvar2pred gv (HD.___stringlit_x_inflate_decode_1, HD.v___stringlit_x_inflate_decode_1) |-- id_hversion_lit gv.
Proof. intros HP. unfold id_hversion_lit. eapply (int_glob _ _ _ I8 Signed); [exact I | vm_compute; reflexivity | exact HP]. Qed.

Ltac hglob sz := intros HP; apply (int_glob _ _ _ sz Unsigned); [exact I | vm_compute; reflexivity | exact HP].

(* dref_tabs is stated at the harness unit's compspecs: int_glob is generic in them *)
Lemma dref_g gv : (forall i b o, gv i = Vptr b o -> o = Ptrofs.zero) ->
  globvar2pred gv (HD._x_inflate_decode__ref_lbase, HD.v_x_inflate_decode__ref_lbase) *
  globvar2pred gv (HD._x_inflate_decode__ref_lext, HD.v_x_inflate_decode__ref_lext) *
  globvar2pred gv (HD._x_inflate_decode__ref_dbase, HD.v_x_inflate_decode__ref_dbase) *
  globvar2pred gv (HD._x_inflate_decode__ref_dext, HD.v_x_inflate_decode__ref_dext)
  |-- dref_tabs gv Ers id_tabs.
Proof.
  intros HP. unfold dref_tabs, id_tabs.
  repeat apply sepcon_derives;
    (apply (int_glob _ _ _ _ Unsigned); [exact I | vm_compute; reflexivity | exact (HP _)]).
Qed.
Lemma cl_order_g gv : (forall b o, gv HD._cl_order = Vptr b o -> o = Ptrofs.zero) ->
  globvar2pred gv (HD._cl_order, HD.v_cl_order)
  |-- data_at Ers (tarray tuchar 19) (zvals clorder) (gv HD._cl_order).
Proof. hglob I8. Qed.
Lemma gz_g gv : (forall b o, gv HD._gz = Vptr b o -> o = Ptrofs.zero) ->
  globvar2pred gv (HD._gz, HD.v_gz)
  |-- data_at Ers (tarray tuchar 10) (zvals gz_vals) (gv HD._gz).
Proof. hglob I8. Qed.


Lemma id_globals_ok gv : (forall i b o, gv i = Vptr b o -> o = Ptrofs.zero) ->
  globvars2pred gv (QPprog_vars p) |-- R gv * TT.
Proof.
  intros HP. rewrite id_W_vars. unfold globvars2pred. simpl map; simpl fold_right.
  sep_apply (crc_g gv (HP _)).
  sep_apply (lenfix_g gv (HP _)).
  sep_apply (distfix_g gv (HP _)).
  sep_apply (order_g gv (HP _)).
  sep_apply (lbase_g gv (HP _)).
  sep_apply (lext_g gv (HP _)).
  sep_apply (dbase_g gv (HP _)).
  sep_apply (dext_g gv (HP _)).
  sep_apply (version_g gv (HP _)).
  sep_apply (id_hversion_g gv (HP _)).
  sep_apply (dref_g gv HP).
  sep_apply (cl_order_g gv (HP _)).
  sep_apply (gz_g gv (HP _)).
  sep_apply (str_glob gv Zlib.inflate.code.___stringlit_inflate_8 Zlib.inflate.code.v___stringlit_inflate_8 ltac:(vm_compute; reflexivity) (HP _)).
  sep_apply (str_glob gv Zlib.inflate.code.___stringlit_inflate_4 Zlib.inflate.code.v___stringlit_inflate_4 ltac:(vm_compute; reflexivity) (HP _)).
  sep_apply (str_glob gv Zlib.inflate.code.___stringlit_inflate_2 Zlib.inflate.code.v___stringlit_inflate_2 ltac:(vm_compute; reflexivity) (HP _)).
  sep_apply (str_glob gv Zlib.inflate.code.___stringlit_inflate_6 Zlib.inflate.code.v___stringlit_inflate_6 ltac:(vm_compute; reflexivity) (HP _)).
  sep_apply (str_glob gv Zlib.inflate.code.___stringlit_inflate_10 Zlib.inflate.code.v___stringlit_inflate_10 ltac:(vm_compute; reflexivity) (HP _)).
  sep_apply (str_glob gv Zlib.inflate.code.___stringlit_inflate_18 Zlib.inflate.code.v___stringlit_inflate_18 ltac:(vm_compute; reflexivity) (HP _)).
  sep_apply (str_glob gv Zlib.inflate.code.___stringlit_inflate_14 Zlib.inflate.code.v___stringlit_inflate_14 ltac:(vm_compute; reflexivity) (HP _)).
  sep_apply (str_glob gv Zlib.inflate.code.___stringlit_inflate_12 Zlib.inflate.code.v___stringlit_inflate_12 ltac:(vm_compute; reflexivity) (HP _)).
  sep_apply (str_glob gv Zlib.inflate.code.___stringlit_inflate_16 Zlib.inflate.code.v___stringlit_inflate_16 ltac:(vm_compute; reflexivity) (HP _)).
  sep_apply (str_glob gv Zlib.inflate.code.___stringlit_inflate_11 Zlib.inflate.code.v___stringlit_inflate_11 ltac:(vm_compute; reflexivity) (HP _)).
  sep_apply (str_glob gv Zlib.inflate.code.___stringlit_inflate_19 Zlib.inflate.code.v___stringlit_inflate_19 ltac:(vm_compute; reflexivity) (HP _)).
  sep_apply (str_glob gv Zlib.inflate.code.___stringlit_inflate_15 Zlib.inflate.code.v___stringlit_inflate_15 ltac:(vm_compute; reflexivity) (HP _)).
  sep_apply (str_glob gv Zlib.inflate.code.___stringlit_inflate_13 Zlib.inflate.code.v___stringlit_inflate_13 ltac:(vm_compute; reflexivity) (HP _)).
  sep_apply (str_glob gv Zlib.inflate.code.___stringlit_inflate_17 Zlib.inflate.code.v___stringlit_inflate_17 ltac:(vm_compute; reflexivity) (HP _)).
  sep_apply (str_glob gv Zlib.inflate.code.___stringlit_inflate_9 Zlib.inflate.code.v___stringlit_inflate_9 ltac:(vm_compute; reflexivity) (HP _)).
  sep_apply (str_glob gv Zlib.inflate.code.___stringlit_inflate_5 Zlib.inflate.code.v___stringlit_inflate_5 ltac:(vm_compute; reflexivity) (HP _)).
  sep_apply (str_glob gv Zlib.inflate.code.___stringlit_inflate_3 Zlib.inflate.code.v___stringlit_inflate_3 ltac:(vm_compute; reflexivity) (HP _)).
  sep_apply (str_glob gv Zlib.inflate.code.___stringlit_inflate_7 Zlib.inflate.code.v___stringlit_inflate_7 ltac:(vm_compute; reflexivity) (HP _)).
  sep_apply (str_glob gv Zlib.inffast.code.___stringlit_inffast_2 Zlib.inffast.code.v___stringlit_inffast_2 ltac:(vm_compute; reflexivity) (HP _)).
  sep_apply (str_glob gv Zlib.inffast.code.___stringlit_inffast_1 Zlib.inffast.code.v___stringlit_inffast_1 ltac:(vm_compute; reflexivity) (HP _)).
  sep_apply (str_glob gv Zlib.inffast.code.___stringlit_inffast_3 Zlib.inffast.code.v___stringlit_inffast_3 ltac:(vm_compute; reflexivity) (HP _)).
  unfold R, tables_rep, Zlib.proof.inftrees.spec.itables, id_msg_lits, id_all_msgs.
  cbv [map fold_right msg_ident].
  cancel.
Qed.

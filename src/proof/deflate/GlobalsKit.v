(** * Helpers for GlobalsInit: globvar2pred of the read-only globals of deflate's law programs.
    Integer arrays (int_glob: after src/proof/harness/inflate_codes/Globals.v), and a generic
    array lemma ([arr_init]) instantiated for arrays of ct_data (static trees), of config_s
    (configuration_table, with function pointers) and of pointers (z_errmsg); static_tree_desc_s. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Zlib.proof.deflate.DCS Zlib.proof.deflate.Rep.
Require Import Zlib.proof.deflate.DSpec.

#[local] Existing Instance DCS.CS.

Lemma init_data_list2pred_app gv sh : forall (l1 l2: list init_data) b o,
  init_data_list2pred gv (l1 ++ l2) sh (Vptr b o) =
  (init_data_list2pred gv l1 sh (Vptr b o) * init_data_list2pred gv l2 sh (offset_val (init_data_list_size l1) (Vptr b o)))%logic.
Proof.
  induction l1 as [|d l1 IH]; intros l2 b o; simpl.
  - rewrite emp_sepcon, Ptrofs.add_zero; auto.
  - rewrite IH, sepcon_assoc. simpl. rewrite Ptrofs.add_assoc, ptrofs_add_repr. reflexivity.
Qed.

(** ** A generic array of initialised structs *)
Section Arr.
Context {A: Type} (T: type) (ini: A -> list init_data) (rep: A -> reptype T) (P: A -> Prop)
  (gv: globals) (sh: share) (al: Z).
Hypothesis Hsize: forall x, init_data_list_size (ini x) = sizeof T.
Hypothesis Hcomplete: complete_legal_cosu_type T = true.
Hypothesis Hal_size: (al | sizeof T).
Hypothesis Hal: forall z, (al | z) -> align_compatible_rec cenv_cs T z.
Hypothesis Helem: forall x b o, P x -> field_compatible T [] (Vptr b o) ->
  init_data_list2pred gv (ini x) sh (Vptr b o) |-- data_at sh T (rep x) (Vptr b o).

Lemma arr_init : forall (l: list A) b o, Forall P l ->
  Ptrofs.unsigned o + sizeof T * Zlength l < Ptrofs.modulus -> (al | Ptrofs.unsigned o) ->
  init_data_list2pred gv (flat_map ini l) sh (Vptr b o)
  |-- data_at sh (tarray T (Zlength l)) (map rep l) (Vptr b o).
Proof.
  pose proof (sizeof_pos T) as HS.
  induction l as [|x l IH]; intros b o HP H1 H2.
  - simpl. apply data_at_zero_array; simpl; auto.
  - inversion HP as [|? ? Px Pl]; subst.
    pose proof (Zlength_nonneg l) as Hn. rewrite Zlength_cons in *.
    change (map rep (x :: l)) with ([rep x] ++ map rep l).
    rewrite (split2_data_at_Tarray_app 1 (Z.succ (Zlength l)) sh T [rep x] (map rep l))
      by (rewrite ?Zlength_map; reflexivity || lia).
    rewrite (data_at_singleton_array_eq sh T (rep x)) by reflexivity.
    rewrite field_address0_offset.
    2: { unfold field_compatible0. repeat split; auto; try lia.
         - simpl. rewrite Z.max_r by lia. exact H1.
         - hnf. apply align_compatible_rec_Tarray. intros i Hi.
           apply Hal. apply Z.divide_add_r; auto. apply Z.divide_mul_l; auto. }
    simpl flat_map. rewrite init_data_list2pred_app.
    apply sepcon_derives.
    + apply Helem; auto. repeat split; auto; [simpl; pose proof (Zlength_nonneg l); nia | hnf; apply Hal; auto].
    + replace (Z.succ (Zlength l) - 1) with (Zlength l) by lia.
      rewrite Hsize. simpl nested_field_offset. simpl offset_val.
      replace (0 + sizeof T * 1) with (sizeof T) by lia.
      apply IH; auto.
      * rewrite Ptrofs.add_unsigned, Ptrofs.unsigned_repr; rewrite ?Ptrofs.unsigned_repr; rep_lia.
      * rewrite Ptrofs.add_unsigned, Ptrofs.unsigned_repr; rewrite ?Ptrofs.unsigned_repr; try rep_lia.
        apply Z.divide_add_r; auto.
Qed.
End Arr.

(** ** Pointers out of Init_addrof: the symbol's address, whether it is a pointer or undefined. *)
Definition addr_ok (gv: globals) (s: ident) : Prop :=
  match gv s with Vptr _ _ | Vundef => True | _ => False end.

Lemma addr_ok_isptr gv s : isptr (gv s) -> addr_ok gv s.
Proof. unfold addr_ok. destruct (gv s); simpl; tauto. Qed.

Lemma addrof_mapsto gv s sh a : addr_ok gv s ->
  init_data2pred gv (Init_addrof s Ptrofs.zero) sh a |-- mapsto sh (tptr tvoid) a (gv s).
Proof.
  unfold addr_ok; intros H; simpl. destruct (gv s); try contradiction.
  - apply derives_refl.
  - rewrite Ptrofs.add_zero. apply derives_refl.
Qed.

Ltac ptr_change := unfold mapsto; simpl; reflexivity.

(** ** Arrays of pointers (z_errmsg) *)
Definition p_init (s: ident) : list init_data := [Init_addrof s Ptrofs.zero].

Lemma p_elem gv sh s b o : addr_ok gv s -> field_compatible (tptr tschar) [] (Vptr b o) ->
  init_data_list2pred gv (p_init s) sh (Vptr b o) |-- data_at sh (tptr tschar) (gv s) (Vptr b o).
Proof.
  intros H FC. unfold p_init, init_data_list2pred. rewrite sepcon_emp.
  sep_apply (addrof_mapsto gv s sh (Vptr b o) H).
  replace (mapsto sh (tptr tvoid) (Vptr b o) (gv s)) with (mapsto sh (tptr tschar) (Vptr b o) (gv s)) by ptr_change.
  rewrite (mapsto_data_at' sh (tptr tschar) (gv s) (gv s) (Vptr b o)) by auto. apply derives_refl.
Qed.

Lemma ptrs_init gv sh (l: list ident) b o : Forall (addr_ok gv) l ->
  Ptrofs.unsigned o + 8 * Zlength l < Ptrofs.modulus -> (8 | Ptrofs.unsigned o) ->
  init_data_list2pred gv (flat_map p_init l) sh (Vptr b o)
  |-- data_at sh (tarray (tptr tschar) (Zlength l)) (map gv l) (Vptr b o).
Proof.
  intros. apply (arr_init (tptr tschar) p_init gv (addr_ok gv) gv sh 8).
  - intros x; reflexivity.
  - reflexivity.
  - apply Z.divide_refl.
  - intros z Hz. eapply align_compatible_rec_by_value; [reflexivity|]. exact Hz.
  - intros. apply p_elem; auto.
  - auto.
  - auto.
  - auto.
Qed.

(** ** Arrays of ct_data (two unions of unsigned shorts) *)
Definition t_ct' := Tstruct Zlib.trees.code._ct_data_s noattr.
Definition ct_init (x: int * int) : list init_data := [Init_int16 (fst x); Init_int16 (snd x)].
Definition ct_rep (x: int * int) : reptype t_ct' :=
  (inl (Vint (Int.zero_ext 16 (fst x))), inl (Vint (Int.zero_ext 16 (snd x)))).

Lemma ct_elem sh p (a1 a2: int) : field_compatible t_ct' [] p ->
  mapsto sh tushort p (Vint (Int.zero_ext 16 a1)) * mapsto sh tushort (offset_val 2 p) (Vint (Int.zero_ext 16 a2))
  |-- data_at sh t_ct' (inl (Vint (Int.zero_ext 16 a1)), inl (Vint (Int.zero_ext 16 a2))) p.
Proof.
  intros FC. unfold_data_at (data_at _ _ _ p).
  assert (F: forall gfs, In gfs [[UnionField Zlib.trees.code._freq; StructField Zlib.trees.code._fc];
                                [UnionField Zlib.trees.code._dad; StructField Zlib.trees.code._dl]] ->
             field_compatible t_ct' gfs p).
  { intros gfs Hg. simpl in Hg. destruct Hg as [<-|[<-|[]]];
      (apply field_compatible_cons; simpl; split; [unfold in_members; simpl; auto|]);
      (apply field_compatible_cons; simpl; split; [unfold in_members; simpl; auto| exact FC]). }
  unfold_field_at 1%nat. unfold_field_at 2%nat.
  erewrite <- (mapsto_field_at sh t_ct' [UnionField Zlib.trees.code._freq; StructField Zlib.trees.code._fc] _ _ p);
    [ | reflexivity | reflexivity | apply F; simpl; tauto | apply JMeq_refl].
  erewrite <- (mapsto_field_at sh t_ct' [UnionField Zlib.trees.code._dad; StructField Zlib.trees.code._dl] _ _ p);
    [ | reflexivity | reflexivity | apply F; simpl; tauto | apply JMeq_refl].
  rewrite !field_address_offset by (apply F; simpl; tauto).
  simpl. rewrite isptr_offset_val_zero by (destruct FC; auto). cancel.
Qed.

Lemma align_ct z : (2 | z) -> align_compatible_rec cenv_cs t_ct' z.
Proof.
  intros H2. eapply align_compatible_rec_Tstruct; [reflexivity|reflexivity|].
  intros i t z' Hf Ho. cbv [co_members Ctypes.field_type] in Hf.
  repeat if_tac in Hf; inv Hf; cbv [Ctypes.field_offset co_members] in Ho; simpl in Ho; inv Ho;
    (eapply align_compatible_rec_Tunion; [reflexivity|reflexivity|]);
    intros i t Hf; cbv [co_members Ctypes.field_type] in Hf; repeat if_tac in Hf; inv Hf;
    (eapply align_compatible_rec_by_value; [reflexivity|]); simpl; try apply Z.divide_add_r; auto;
    apply Z.divide_refl || apply Z.divide_0_r.
Qed.

Lemma cts_init gv sh (l: list (int * int)) b o :
  Ptrofs.unsigned o + 4 * Zlength l < Ptrofs.modulus -> (2 | Ptrofs.unsigned o) ->
  init_data_list2pred gv (flat_map ct_init l) sh (Vptr b o)
  |-- @data_at DCS.CS sh (tarray t_ct' (Zlength l)) (map ct_rep l) (Vptr b o).
Proof.
  intros. apply (arr_init t_ct' ct_init ct_rep (fun _ => True) gv sh 2).
  - intros x; reflexivity.
  - reflexivity.
  - exists 2; reflexivity.
  - apply align_ct.
  - intros [a1 a2] b' o' _ FC. unfold ct_init, ct_rep. cbn [init_data_list2pred init_data2pred init_data_size fst snd].
    rewrite sepcon_emp.
    apply (ct_elem sh (Vptr b' o') a1 a2 FC).
  - apply Forall_forall; auto.
  - exact H.
  - exact H0.
Qed.

(** ** Arrays of config_s (four unsigned shorts and a function pointer) *)
Definition cfg_init (x: int * int * int * int * ident) : list init_data :=
  let '(g, l, n, c, f) := x in
  [Init_int16 g; Init_int16 l; Init_int16 n; Init_int16 c; Init_addrof f Ptrofs.zero].
Definition cfg_rep (gv: globals) (x: int * int * int * int * ident) : reptype t_config :=
  let '(g, l, n, c, f) := x in
  (Vint (Int.zero_ext 16 g), (Vint (Int.zero_ext 16 l), (Vint (Int.zero_ext 16 n), (Vint (Int.zero_ext 16 c), gv f)))).
Definition cfg_ok (gv: globals) (x: int * int * int * int * ident) : Prop :=
  let '(g, l, n, c, f) := x in addr_ok gv f.

Lemma cfg_elem gv sh x p : cfg_ok gv x -> field_compatible t_config [] p ->
  init_data_list2pred gv (cfg_init x) sh p |-- @data_at DCS.CS sh t_config (cfg_rep gv x) p.
Proof.
  destruct x as [[[[g l] n] c] f]. intros H FC.
  cbn [cfg_init cfg_rep cfg_ok init_data_list2pred init_data_size] in *.
  sep_apply (addrof_mapsto gv f sh (offset_val 2 (offset_val 2 (offset_val 2 (offset_val 2 p)))) H).
  rewrite !offset_offset_val. simpl. unfold_data_at (data_at _ _ _ p).
  assert (F: forall i, In i [Zlib.deflate.code._good_length; Zlib.deflate.code._max_lazy; Zlib.deflate.code._nice_length;
                            Zlib.deflate.code._max_chain; Zlib.deflate.code._func] ->
             field_compatible t_config (DOT i) p).
  { intros i Hi. apply field_compatible_cons. simpl. split; [|exact FC]. unfold in_members.
    simpl in Hi |- *. destruct Hi as [<-|[<-|[<-|[<-|[<-|[]]]]]]; simpl; tauto. }
  erewrite <- (mapsto_field_at sh t_config (DOT Zlib.deflate.code._good_length) _ _ p);
    [ | reflexivity | reflexivity | apply F; simpl; tauto | apply JMeq_refl].
  erewrite <- (mapsto_field_at sh t_config (DOT Zlib.deflate.code._max_lazy) _ _ p);
    [ | reflexivity | reflexivity | apply F; simpl; tauto | apply JMeq_refl].
  erewrite <- (mapsto_field_at sh t_config (DOT Zlib.deflate.code._nice_length) _ _ p);
    [ | reflexivity | reflexivity | apply F; simpl; tauto | apply JMeq_refl].
  erewrite <- (mapsto_field_at sh t_config (DOT Zlib.deflate.code._max_chain) _ _ p);
    [ | reflexivity | reflexivity | apply F; simpl; tauto | apply JMeq_refl].
  erewrite <- (mapsto_field_at sh t_config (DOT Zlib.deflate.code._func) _ _ p);
    [ | reflexivity | reflexivity | apply F; simpl; tauto | apply JMeq_refl].
  rewrite !field_address_offset by (apply F; simpl; tauto).
  simpl. rewrite isptr_offset_val_zero by (destruct FC; auto). cancel.
  apply derives_refl'. ptr_change.
Qed.

Lemma align_cfg z : (8 | z) -> align_compatible_rec cenv_cs t_config z.
Proof.
  intros H8. eapply align_compatible_rec_Tstruct; [reflexivity|reflexivity|].
  intros i t z' Hf Ho. cbv [co_members Ctypes.field_type] in Hf.
  repeat if_tac in Hf; inv Hf; cbv [Ctypes.field_offset co_members] in Ho; simpl in Ho; inv Ho;
    (eapply align_compatible_rec_by_value; [reflexivity|]); simpl; destruct H8 as [k ->];
    first [exists (4 * k); lia | exists (4 * k + 1); lia | exists (4 * k + 2); lia | exists (4 * k + 3); lia
          | exists (k + 1); lia].
Qed.

Lemma cfgs_init gv sh (l: list (int * int * int * int * ident)) b o : Forall (cfg_ok gv) l ->
  Ptrofs.unsigned o + 16 * Zlength l < Ptrofs.modulus -> (8 | Ptrofs.unsigned o) ->
  init_data_list2pred gv (flat_map cfg_init l) sh (Vptr b o)
  |-- @data_at DCS.CS sh (tarray t_config (Zlength l)) (map (cfg_rep gv) l) (Vptr b o).
Proof.
  intros. apply (arr_init t_config cfg_init (cfg_rep gv) (cfg_ok gv) gv sh 8).
  - intros [[[[g l'] n] c] f]; reflexivity.
  - reflexivity.
  - exists 2; reflexivity.
  - apply align_cfg.
  - intros x b' o' Hx FC. apply cfg_elem; auto.
  - auto.
  - exact H0.
  - exact H1.
Qed.

(** ** static_tree_desc_s *)
Definition t_sd' := Tstruct Zlib.trees.code._static_tree_desc_s noattr.

Lemma sd_elem sh p (v0 v1: val) (x y z: int) : readable_share sh -> field_compatible t_sd' [] p ->
  mapsto sh (tptr t_ct') p v0 * mapsto sh (tptr tint) (offset_val 8 p) v1 *
  mapsto sh tint (offset_val 16 p) (Vint x) * mapsto sh tint (offset_val 20 p) (Vint y) *
  mapsto sh tint (offset_val 24 p) (Vint z) * mapsto_zeros 4 sh (offset_val 28 p)
  |-- @data_at DCS.CS sh t_sd' (v0, (v1, (Vint x, (Vint y, Vint z)))) p.
Proof.
  intros RS FC. unfold_data_at (data_at _ _ _ p).
  assert (F: forall i, In i [Zlib.trees.code._static_tree; Zlib.trees.code._extra_bits; Zlib.trees.code._extra_base;
                            Zlib.trees.code._elems; Zlib.trees.code._max_length] ->
             field_compatible t_sd' (DOT i) p).
  { intros i Hi. apply field_compatible_cons. simpl. split; [|exact FC]. unfold in_members.
    simpl in Hi |- *. destruct Hi as [<-|[<-|[<-|[<-|[<-|[]]]]]]; simpl; tauto. }
  erewrite <- (mapsto_field_at sh t_sd' (DOT Zlib.trees.code._static_tree) _ _ p);
    [ | reflexivity | reflexivity | apply F; simpl; tauto | apply JMeq_refl].
  erewrite <- (mapsto_field_at sh t_sd' (DOT Zlib.trees.code._extra_bits) _ _ p);
    [ | reflexivity | reflexivity | apply F; simpl; tauto | apply JMeq_refl].
  erewrite <- (mapsto_field_at sh t_sd' (DOT Zlib.trees.code._extra_base) _ _ p);
    [ | reflexivity | reflexivity | apply F; simpl; tauto | apply JMeq_refl].
  erewrite <- (mapsto_field_at sh t_sd' (DOT Zlib.trees.code._elems) _ _ p);
    [ | reflexivity | reflexivity | apply F; simpl; tauto | apply JMeq_refl].
  erewrite <- (mapsto_field_at sh t_sd' (DOT Zlib.trees.code._max_length) _ _ p);
    [ | reflexivity | reflexivity | apply F; simpl; tauto | apply JMeq_refl].
  rewrite !field_address_offset by (apply F; simpl; tauto).
  simpl. rewrite isptr_offset_val_zero by (destruct FC; auto). cancel.
  unfold spacer; simpl. unfold at_offset. apply mapsto_zeros_memory_block; auto.
Qed.

(** ** Integer arrays (Init_int8/16/32 data): after src/proof/harness/inflate_codes/Globals.v *)
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

(** A string literal (or any global whose data starts with a byte) is at a pointer. *)
Definition starts_int8 (v: globvar type) : bool :=
  match gvar_init v with Init_int8 _ :: _ => negb (gvar_volatile v) | _ => false end.

Lemma glob_isptr gv i v : starts_int8 v = true -> globvar2pred gv (i, v) |-- !! isptr (gv i) && TT.
Proof.
  unfold starts_int8, globvar2pred; simpl. destruct (gvar_init v) as [|d r]; try discriminate.
  destruct d; try discriminate. intros V. apply negb_true_iff in V. rewrite V. simpl.
  apply andp_right; [|apply TT_right].
  sep_apply (mapsto_local_facts (readonly2share (gvar_readonly v)) (Tint I8 Unsigned noattr) (gv i)
               (Vint (Int.zero_ext 8 i0))).
  normalize.
Qed.

Lemma ptr_split (P Q: mpred) (v: val) :
  (P |-- !! isptr v) -> (forall b o, v = Vptr b o -> P |-- Q) -> P |-- Q.
Proof.
  intros H1 H2. apply derives_trans with (!! isptr v && P); [apply andp_right; auto|].
  destruct v; simpl; normalize. eapply H2; reflexivity.
Qed.

Lemma idl_isptr gv d r sh v : (match d with Init_space _ | Init_addrof _ _ => False | _ => True end) ->
  init_data_list2pred gv (d :: r) sh v |-- !! isptr v.
Proof.
  intros Hd. simpl. destruct d; try contradiction;
    (eapply derives_trans; [apply sepcon_derives; [apply mapsto_local_facts | apply TT_right] |]);
    rewrite <- (andp_TT (!! _)) at 1; rewrite sepcon_andp_prop'; apply andp_left1; apply prop_derives; tauto.
Qed.

(** ** The static trees *)
Fixpoint ascts (dl: list init_data) : option (list (int * int)) :=
  match dl with
  | [] => Some []
  | Init_int16 a :: Init_int16 b :: r => match ascts r with Some l => Some ((a, b) :: l) | None => None end
  | _ => None
  end.

Definition range16b (l: list Z) : bool := forallb (fun x => (0 <=? x) && (x <? 65536))%bool l.

Lemma range16b_ok l : range16b l = true -> forall i, 0 <= i < Zlength l -> 0 <= Znth i l < 65536.
Proof.
  intros H i Hi. unfold range16b in H. rewrite forallb_forall in H.
  specialize (H (Znth i l) (Znth_In i l Hi)). apply andb_true_iff in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.

Lemma tree_ok_of t n : Zlength (fc t) = n -> Zlength (dl t) = n ->
  range16b (fc t) = true -> range16b (dl t) = true -> tree_ok t n.
Proof.
  intros H1 H2 H3 H4. split3; auto. intros i Hi.
  split; [apply range16b_ok; auto; lia | apply range16b_ok; auto; lia].
Qed.

Lemma tree_glob gv i v n t data :
  gvar_volatile v = false -> gvar_readonly v = true -> gvar_init v = flat_map ct_init data ->
  data <> [] -> 4 * Zlength data < Ptrofs.modulus -> Zlength data = n ->
  map ct_rep data = ct_canon t -> tree_ok t n ->
  (forall b o, gv i = Vptr b o -> o = Ptrofs.zero) ->
  globvar2pred gv (i, v) |-- !! isptr (gv i) && tree_arr Ers n t (gv i).
Proof.
  intros V RO E NE SZ N R OK HP.
  unfold globvar2pred; simpl. rewrite V, RO, E. simpl readonly2share.
  apply (ptr_split _ _ (gv i)).
  { destruct data as [|x r]; [contradiction|]. apply idl_isptr. exact I. }
  intros b o G. rewrite G in *. specialize (HP b o eq_refl); subst o.
  apply andp_right; [apply prop_right; exact I|].
  unfold tree_arr. apply andp_right; [apply prop_right; exact OK|].
  eapply derives_trans; [apply cts_init; rewrite ?Ptrofs.unsigned_zero; [lia | apply Z.divide_0_r] |].
  rewrite N, R. apply derives_refl.
Qed.

Lemma ltree_g gv : (forall b o, gv Zlib.trees.code._static_ltree = Vptr b o -> o = Ptrofs.zero) ->
  globvar2pred gv (Zlib.trees.code._static_ltree, Zlib.trees.code.v_static_ltree)
  |-- !! isptr (gv Zlib.trees.code._static_ltree) &&
      tree_arr Ers (L_CODES + 2) static_ltree_t (gv Zlib.trees.code._static_ltree).
Proof.
  intros HP.
  let d := eval vm_compute in (ascts (gvar_init Zlib.trees.code.v_static_ltree)) in
  match d with Some ?data =>
    apply (tree_glob gv _ _ _ _ data); [reflexivity | reflexivity | vm_compute; reflexivity | discriminate
      | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
      | apply tree_ok_of; vm_compute; reflexivity | exact HP]
  end.
Qed.

Lemma dtree_g gv : (forall b o, gv Zlib.trees.code._static_dtree = Vptr b o -> o = Ptrofs.zero) ->
  globvar2pred gv (Zlib.trees.code._static_dtree, Zlib.trees.code.v_static_dtree)
  |-- !! isptr (gv Zlib.trees.code._static_dtree) &&
      tree_arr Ers D_CODES static_dtree_t (gv Zlib.trees.code._static_dtree).
Proof.
  intros HP.
  let d := eval vm_compute in (ascts (gvar_init Zlib.trees.code.v_static_dtree)) in
  match d with Some ?data =>
    apply (tree_glob gv _ _ _ _ data); [reflexivity | reflexivity | vm_compute; reflexivity | discriminate
      | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
      | apply tree_ok_of; vm_compute; reflexivity | exact HP]
  end.
Qed.

(** ** configuration_table *)
Fixpoint ascfg (dl: list init_data) : option (list (int * int * int * int * ident)) :=
  match dl with
  | [] => Some []
  | Init_int16 g :: Init_int16 l :: Init_int16 n :: Init_int16 c :: Init_addrof f o :: r =>
      if Ptrofs.eq_dec o Ptrofs.zero then
        match ascfg r with Some x => Some ((g, l, n, c, f) :: x) | None => None end
      else None
  | _ => None
  end.

Lemma cfg_glob gv i v n data vals :
  gvar_volatile v = false -> gvar_readonly v = true -> gvar_init v = flat_map cfg_init data ->
  data <> [] -> 16 * Zlength data < Ptrofs.modulus -> Zlength data = n ->
  map (cfg_rep gv) data = vals -> Forall (cfg_ok gv) data ->
  (forall b o, gv i = Vptr b o -> o = Ptrofs.zero) ->
  globvar2pred gv (i, v) |-- @data_at DCS.CS Ers (tarray t_config n) vals (gv i).
Proof.
  intros V RO E NE SZ N R OK HP.
  unfold globvar2pred; simpl. rewrite V, RO, E. simpl readonly2share.
  apply (ptr_split _ _ (gv i)).
  { destruct data as [|[[[[g l] n'] c] f] r]; [contradiction|]. apply idl_isptr. exact I. }
  intros b o G. rewrite G in *. specialize (HP b o eq_refl); subst o.
  eapply derives_trans; [apply cfgs_init; rewrite ?Ptrofs.unsigned_zero; [exact OK | lia | apply Z.divide_0_r] |].
  rewrite N, R. apply derives_refl.
Qed.

Lemma config_g gv :
  addr_ok gv Zlib.deflate.code._deflate_stored -> addr_ok gv Zlib.deflate.code._deflate_fast ->
  addr_ok gv Zlib.deflate.code._deflate_slow ->
  (forall b o, gv Zlib.deflate.code._configuration_table = Vptr b o -> o = Ptrofs.zero) ->
  globvar2pred gv (Zlib.deflate.code._configuration_table, Zlib.deflate.code.v_configuration_table)
  |-- @data_at DCS.CS Ers (tarray t_config 10) (config_vals gv) (gv Zlib.deflate.code._configuration_table).
Proof.
  intros H0 H1 H2 HP.
  let d := eval vm_compute in (ascfg (gvar_init Zlib.deflate.code.v_configuration_table)) in
  match d with Some ?data =>
    apply (cfg_glob gv _ _ _ data); [reflexivity | reflexivity | vm_compute; reflexivity | discriminate
      | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
      | repeat constructor; assumption | exact HP]
  end.
Qed.

(** ** z_errmsg (pointers to zutil.c's message literals) *)
Fixpoint asptrs (dl: list init_data) : option (list ident) :=
  match dl with
  | [] => Some []
  | Init_addrof s o :: r =>
      if Ptrofs.eq_dec o Ptrofs.zero then match asptrs r with Some x => Some (s :: x) | None => None end
      else None
  | _ => None
  end.

Lemma ptrs_glob gv i v (ss: list ident) :
  gvar_volatile v = false -> gvar_readonly v = true -> gvar_init v = flat_map p_init ss ->
  ss <> [] -> 8 * Zlength ss < Ptrofs.modulus -> Forall (fun s => isptr (gv s)) ss ->
  (forall b o, gv i = Vptr b o -> o = Ptrofs.zero) ->
  globvar2pred gv (i, v) |-- @data_at DCS.CS Ers (tarray (tptr tschar) (Zlength ss)) (map gv ss) (gv i).
Proof.
  intros V RO E NE SZ OK HP.
  unfold globvar2pred; simpl. rewrite V, RO, E. simpl readonly2share.
  apply (ptr_split _ _ (gv i)).
  { destruct ss as [|s r]; [contradiction|]. cbn [flat_map p_init app init_data_list2pred].
    sep_apply (addrof_mapsto gv s Ers (gv i)). { inv OK. apply addr_ok_isptr; auto. }
    eapply derives_trans; [apply sepcon_derives; [apply mapsto_local_facts | apply TT_right] |].
    rewrite <- (andp_TT (!! _)) at 1; rewrite sepcon_andp_prop'; apply andp_left1; apply prop_derives; tauto. }
  intros b o G. rewrite G in *. specialize (HP b o eq_refl); subst o.
  apply ptrs_init; rewrite ?Ptrofs.unsigned_zero; [ | lia | apply Z.divide_0_r].
  eapply Forall_impl; [|exact OK]. intros s. apply addr_ok_isptr.
Qed.

Lemma Forall_isptr_ptr_or_null (gv: globals) (ss: list ident) : Forall (fun s => isptr (gv s)) ss -> Forall is_pointer_or_null (map gv ss).
Proof. intros H. apply Forall_map. eapply Forall_impl; [|exact H]. intros s Hs. destruct (gv s); simpl in *; try contradiction; auto. Qed.

Definition errmsg_lits : list ident :=
  [Zlib.zutil.code.___stringlit_zutil_9; Zlib.zutil.code.___stringlit_zutil_8; Zlib.zutil.code.___stringlit_zutil_1;
   Zlib.zutil.code.___stringlit_zutil_7; Zlib.zutil.code.___stringlit_zutil_6; Zlib.zutil.code.___stringlit_zutil_5;
   Zlib.zutil.code.___stringlit_zutil_4; Zlib.zutil.code.___stringlit_zutil_3; Zlib.zutil.code.___stringlit_zutil_2;
   Zlib.zutil.code.___stringlit_zutil_1].

Lemma errmsg_g gv : Forall (fun s => isptr (gv s)) errmsg_lits ->
  (forall b o, gv Zlib.zutil.code._z_errmsg = Vptr b o -> o = Ptrofs.zero) ->
  globvar2pred gv (Zlib.zutil.code._z_errmsg, Zlib.zutil.code.v_z_errmsg) |-- errmsg_at gv.
Proof.
  intros OK HP. unfold errmsg_at. Exists (map gv errmsg_lits).
  apply andp_right; [apply prop_right; split; [reflexivity | apply Forall_isptr_ptr_or_null; exact OK] |].
  apply (ptrs_glob gv _ _ errmsg_lits); try reflexivity; auto; discriminate.
Qed.

(** ** static_tree_desc_s globals *)
Ltac div_off := match goal with |- (?a | ?k * 8 + ?c) =>
  let q := eval compute in (8 / a) in let r := eval compute in (c / a) in exists (k * q + r); lia end.

Lemma align_sd z : (8 | z) -> align_compatible_rec cenv_cs t_sd' z.
Proof.
  intros H8. eapply align_compatible_rec_Tstruct; [reflexivity|reflexivity|].
  intros i t z' Hf Ho. cbv [co_members Ctypes.field_type] in Hf.
  repeat if_tac in Hf; inv Hf; cbv [Ctypes.field_offset co_members] in Ho; simpl in Ho; inv Ho;
    (eapply align_compatible_rec_by_value; [reflexivity|]); simpl; destruct H8 as [k ->]; div_off.
Qed.

Lemma sd_glob gv i v d0 v0 s1 x y z :
  gvar_volatile v = false -> gvar_readonly v = true ->
  gvar_init v = [d0; Init_addrof s1 Ptrofs.zero; Init_int32 x; Init_int32 y; Init_int32 z; Init_space 4] ->
  init_data_size d0 = 8 ->
  (forall a, init_data2pred gv d0 Ers a |-- mapsto Ers (tptr t_ct') a v0) -> addr_ok gv s1 ->
  (forall b o, gv i = Vptr b o -> o = Ptrofs.zero) ->
  globvar2pred gv (i, v) |-- @data_at DCS.CS Ers t_sd' (v0, (gv s1, (Vint x, (Vint y, Vint z)))) (gv i).
Proof.
  intros V RO E S0 D0 A1 HP.
  unfold globvar2pred; simpl. rewrite V, RO, E. simpl readonly2share. cbn [init_data_list2pred init_data_size].
  rewrite S0. change (if Archi.ptr64 then 8 else 4) with 8.
  sep_apply (D0 (gv i)).
  apply (ptr_split _ _ (gv i)).
  { eapply derives_trans; [apply sepcon_derives; [apply mapsto_local_facts | apply TT_right] |].
    rewrite <- (andp_TT (!! _)) at 1; rewrite sepcon_andp_prop'; apply andp_left1; apply prop_derives; tauto. }
  intros b o G. rewrite G in *. specialize (HP b o eq_refl); subst o.
  rewrite !offset_offset_val. simpl Z.add.
  sep_apply (addrof_mapsto gv s1 Ers (offset_val 8 (Vptr b Ptrofs.zero)) A1).
  replace (mapsto Ers (tptr tvoid) (offset_val 8 (Vptr b Ptrofs.zero)) (gv s1))
    with (mapsto Ers (tptr tint) (offset_val 8 (Vptr b Ptrofs.zero)) (gv s1)) by ptr_change.
  cbn [init_data2pred]. rewrite !mapsto_tuint_tint.
  eapply derives_trans; [|apply sd_elem; [apply readable_Ers | ]].
  - cancel.
  - repeat split; auto. hnf. apply align_sd. rewrite Ptrofs.unsigned_zero. apply Z.divide_0_r.
Qed.

Lemma addrof_ct gv s : addr_ok gv s ->
  forall a, init_data2pred gv (Init_addrof s Ptrofs.zero) Ers a |-- mapsto Ers (tptr t_ct') a (gv s).
Proof.
  intros H a. sep_apply (addrof_mapsto gv s Ers a H). apply derives_refl'. ptr_change.
Qed.

Lemma null_ct gv : forall a, init_data2pred gv (Init_int64 (Int64.repr 0)) Ers a |-- mapsto Ers (tptr t_ct') a nullval.
Proof.
  intros a. simpl. unfold tptr. rewrite mapsto_tuint_tptr_nullval. apply derives_refl.
Qed.

Lemma l_desc_g gv : addr_ok gv Zlib.trees.code._static_ltree -> addr_ok gv Zlib.trees.code._extra_lbits ->
  (forall b o, gv Zlib.trees.code._static_l_desc = Vptr b o -> o = Ptrofs.zero) ->
  globvar2pred gv (Zlib.trees.code._static_l_desc, Zlib.trees.code.v_static_l_desc)
  |-- @data_at DCS.CS Ers t_sd (gv Zlib.trees.code._static_ltree, (gv Zlib.trees.code._extra_lbits, (vi 257, (vi 286, vi 15))))
        (gv Zlib.trees.code._static_l_desc).
Proof.
  intros A0 A1 HP. eapply sd_glob; [reflexivity | reflexivity | reflexivity | reflexivity | apply addrof_ct; auto | auto | auto].
Qed.

Lemma d_desc_g gv : addr_ok gv Zlib.trees.code._static_dtree -> addr_ok gv Zlib.trees.code._extra_dbits ->
  (forall b o, gv Zlib.trees.code._static_d_desc = Vptr b o -> o = Ptrofs.zero) ->
  globvar2pred gv (Zlib.trees.code._static_d_desc, Zlib.trees.code.v_static_d_desc)
  |-- @data_at DCS.CS Ers t_sd (gv Zlib.trees.code._static_dtree, (gv Zlib.trees.code._extra_dbits, (vi 0, (vi 30, vi 15))))
        (gv Zlib.trees.code._static_d_desc).
Proof.
  intros A0 A1 HP. eapply sd_glob; [reflexivity | reflexivity | reflexivity | reflexivity | apply addrof_ct; auto | auto | auto].
Qed.

Lemma bl_desc_g gv : addr_ok gv Zlib.trees.code._extra_blbits ->
  (forall b o, gv Zlib.trees.code._static_bl_desc = Vptr b o -> o = Ptrofs.zero) ->
  globvar2pred gv (Zlib.trees.code._static_bl_desc, Zlib.trees.code.v_static_bl_desc)
  |-- @data_at DCS.CS Ers t_sd (nullval, (gv Zlib.trees.code._extra_blbits, (vi 0, (vi 19, vi 7))))
        (gv Zlib.trees.code._static_bl_desc).
Proof.
  intros A1 HP. eapply sd_glob; [reflexivity | reflexivity | reflexivity | reflexivity | apply null_ct | auto | auto].
Qed.

(** ** trees.c's integer tables, my_version and the harness's ZLIB_VERSION literal *)
Lemma int_glob_p gv i v sz sign n zs :
  notboolsize sz -> int_glob_ok sz sign v n zs = true ->
  (forall b o, gv i = Vptr b o -> o = Ptrofs.zero) ->
  globvar2pred gv (i, v)
  |-- !! isptr (gv i) && @data_at DCS.CS Ers (tarray (Tint sz sign noattr) n) (map (fun z => Vint (Int.repr z)) zs) (gv i).
Proof.
  intros NB OK HP. sep_apply (@int_glob DCS.CS gv i v sz sign n zs NB OK HP).
  apply andp_right; [|apply derives_refl]. entailer!.
Qed.

Ltac tab_g sz sign := intros HP; apply (int_glob_p _ _ _ sz sign); [exact I | vm_compute; reflexivity | exact HP].

Lemma dist_code_g gv : (forall b o, gv Zlib.trees.code.__dist_code = Vptr b o -> o = Ptrofs.zero) ->
  globvar2pred gv (Zlib.trees.code.__dist_code, Zlib.trees.code.v__dist_code)
  |-- !! isptr (gv Zlib.trees.code.__dist_code) &&
      @data_at DCS.CS Ers (tarray tuchar 512) (map vi dist_code_tab) (gv Zlib.trees.code.__dist_code).
Proof. tab_g I8 Unsigned. Qed.

Lemma length_code_g gv : (forall b o, gv Zlib.trees.code.__length_code = Vptr b o -> o = Ptrofs.zero) ->
  globvar2pred gv (Zlib.trees.code.__length_code, Zlib.trees.code.v__length_code)
  |-- !! isptr (gv Zlib.trees.code.__length_code) &&
      @data_at DCS.CS Ers (tarray tuchar 256) (map vi length_code_tab) (gv Zlib.trees.code.__length_code).
Proof. tab_g I8 Unsigned. Qed.

Lemma base_length_g gv : (forall b o, gv Zlib.trees.code._base_length = Vptr b o -> o = Ptrofs.zero) ->
  globvar2pred gv (Zlib.trees.code._base_length, Zlib.trees.code.v_base_length)
  |-- !! isptr (gv Zlib.trees.code._base_length) &&
      @data_at DCS.CS Ers (tarray tint 29) (map vi base_length_tab) (gv Zlib.trees.code._base_length).
Proof. tab_g I32 Signed. Qed.

Lemma base_dist_g gv : (forall b o, gv Zlib.trees.code._base_dist = Vptr b o -> o = Ptrofs.zero) ->
  globvar2pred gv (Zlib.trees.code._base_dist, Zlib.trees.code.v_base_dist)
  |-- !! isptr (gv Zlib.trees.code._base_dist) &&
      @data_at DCS.CS Ers (tarray tint 30) (map vi base_dist_tab) (gv Zlib.trees.code._base_dist).
Proof. tab_g I32 Signed. Qed.

Lemma extra_lbits_g gv : (forall b o, gv Zlib.trees.code._extra_lbits = Vptr b o -> o = Ptrofs.zero) ->
  globvar2pred gv (Zlib.trees.code._extra_lbits, Zlib.trees.code.v_extra_lbits)
  |-- !! isptr (gv Zlib.trees.code._extra_lbits) &&
      @data_at DCS.CS Ers (tarray tint 29) (map vi extra_lbits) (gv Zlib.trees.code._extra_lbits).
Proof. tab_g I32 Signed. Qed.

Lemma extra_dbits_g gv : (forall b o, gv Zlib.trees.code._extra_dbits = Vptr b o -> o = Ptrofs.zero) ->
  globvar2pred gv (Zlib.trees.code._extra_dbits, Zlib.trees.code.v_extra_dbits)
  |-- !! isptr (gv Zlib.trees.code._extra_dbits) &&
      @data_at DCS.CS Ers (tarray tint 30) (map vi extra_dbits) (gv Zlib.trees.code._extra_dbits).
Proof. tab_g I32 Signed. Qed.

Lemma extra_blbits_g gv : (forall b o, gv Zlib.trees.code._extra_blbits = Vptr b o -> o = Ptrofs.zero) ->
  globvar2pred gv (Zlib.trees.code._extra_blbits, Zlib.trees.code.v_extra_blbits)
  |-- !! isptr (gv Zlib.trees.code._extra_blbits) &&
      @data_at DCS.CS Ers (tarray tint 19) (map vi extra_blbits) (gv Zlib.trees.code._extra_blbits).
Proof. tab_g I32 Signed. Qed.

Lemma bl_order_g gv : (forall b o, gv Zlib.trees.code._bl_order = Vptr b o -> o = Ptrofs.zero) ->
  globvar2pred gv (Zlib.trees.code._bl_order, Zlib.trees.code.v_bl_order)
  |-- !! isptr (gv Zlib.trees.code._bl_order) &&
      @data_at DCS.CS Ers (tarray tuchar 19) (map vi bl_order) (gv Zlib.trees.code._bl_order).
Proof. tab_g I8 Unsigned. Qed.

Lemma my_version_g gv : (forall b o, gv Zlib.deflate.code._my_version = Vptr b o -> o = Ptrofs.zero) ->
  globvar2pred gv (Zlib.deflate.code._my_version, Zlib.deflate.code.v_my_version)
  |-- !! isptr (gv Zlib.deflate.code._my_version) &&
      @data_at DCS.CS Ers (tarray tschar 6) (map vi [49; 46; 51; 46; 50; 0]) (gv Zlib.deflate.code._my_version).
Proof. tab_g I8 Signed. Qed.

Lemma version_lit_g gv i v : int_glob_ok I8 Signed v 6 [49; 46; 51; 46; 50; 0] = true ->
  (forall b o, gv i = Vptr b o -> o = Ptrofs.zero) ->
  globvar2pred gv (i, v)
  |-- !! isptr (gv i) && @data_at DCS.CS Ers (tarray tschar 6) (map vi [49; 46; 51; 46; 50; 0]) (gv i).
Proof. intros OK HP. apply (int_glob_p _ _ _ I8 Signed); [exact I | exact OK | exact HP]. Qed.

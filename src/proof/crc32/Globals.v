(* crc32.c's constant tables out of main's precondition: globvar2pred of crc_table and x2n_table (their
   Init_int32 data, as clightgen emits them) gives crc_table_at Ers gv and x2n_table_at Ers gv (the
   specifications' resources), for globals at offset zero (initialize.genviron2globals).

   For any law whose program links crc32.c: Globals.crc_tables_of_globvar (and the generic gv_arr32 for
   other uint tables).  After the reference proof of zlib-inftrees (henough_asm.v, gv_arr16). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Zlib.proof.crc32.SpecCombine.
Require Import Zlib.crc32.code.
#[local] Existing Instance Zlib.units.Crc32.CS.

Fixpoint as32 (dl: list init_data) : option (list int) :=
  match dl with
  | [] => Some []
  | Init_int32 i :: r => match as32 r with Some l => Some (i :: l) | None => None end
  | _ => None
  end.

Lemma as32_ok : forall dl data, as32 dl = Some data -> dl = map Init_int32 data.
Proof.
  induction dl as [|d dl IH]; intros data H; simpl in H.
  - inv H; reflexivity.
  - destruct d; try discriminate. destruct (as32 dl) eqn:E; inv H. simpl; f_equal; auto.
Qed.

Lemma idl2_star32 {cs: compspecs} Delta gv sh : forall (data: list int) v,
  init_data_list2pred gv (map Init_int32 data) sh v = id2pred_star Delta gv sh v (map Init_int32 data).
Proof. induction data; intros; simpl; auto. rewrite IHdata; reflexivity. Qed.

Lemma gv_arr32 {cs: compspecs} gv sh (data: list int) p :
  data <> [] -> 4 * Zlength data < Ptrofs.modulus ->
  (forall b o, p = Vptr b o -> o = Ptrofs.zero) ->
  init_data_list2pred gv (map Init_int32 data) sh p
  |-- data_at sh (tarray tuint (Zlength data)) (map (Vint oo Cop.cast_int_int I32 Unsigned) data) p.
Proof.
  intros NE R HP.
  destruct p; try (destruct data as [|d data]; [contradiction|]; simpl; unfold mapsto; simpl;
                   rewrite FF_sepcon; apply FF_left).
  specialize (HP b i eq_refl); subst i.
  rewrite (idl2_star32 empty_tycontext).
  pose proof (id2pred_star_ZnthV_Tint empty_tycontext gv sh (Zlength data) (Vptr b Ptrofs.zero) data
               I32 Unsigned (map Init_int32 data) I) as H.
  rewrite Zlength_map in H. specialize (H eq_refl eq_refl any_environ).
  eapply derives_trans; [ | apply H]. unfold_lift. simpl.
  repeat apply andp_right; try apply derives_refl; apply prop_right.
  - auto.
  - apply align_compatible_rec_by_value with (ch := Mint32); [reflexivity | ].
    rewrite Ptrofs.unsigned_zero. apply Z.divide_0_r.
  - rewrite Ptrofs.unsigned_zero. pose proof (Zlength_nonneg data). simpl sizeof. lia.
Qed.

(* Two lists of ints are equal when their unsigned values are (checked by computation). *)
Lemma ints_eq_unsigned (l1 l2: list int): map Int.unsigned l1 = map Int.unsigned l2 -> l1 = l2.
Proof.
  revert l2. induction l1 as [|a l1 IH]; intros [|b l2] E; simpl in E; try discriminate; auto.
  inv E. f_equal; auto.
  rewrite <- (Int.repr_unsigned a), <- (Int.repr_unsigned b). congruence.
Qed.

Lemma crc_table_ints (data: list int):
  map Int.unsigned data = map (fun x => Int.unsigned (Int.repr x)) crc_table_vals ->
  map (Vint oo Cop.cast_int_int I32 Unsigned) data = crc_table_rep.
Proof.
  intros E. unfold crc_table_rep.
  replace data with (map Int.repr crc_table_vals).
  - rewrite map_map. reflexivity.
  - apply ints_eq_unsigned. rewrite map_map. auto.
Qed.

Lemma x2n_table_ints (data: list int):
  map Int.unsigned data = map (fun x => Int.unsigned (Int.repr x)) x2n_table_vals ->
  map (Vint oo Cop.cast_int_int I32 Unsigned) data = x2n_table_rep.
Proof.
  intros E. unfold x2n_table_rep.
  replace data with (map Int.repr x2n_table_vals).
  - rewrite map_map. reflexivity.
  - apply ints_eq_unsigned. rewrite map_map. auto.
Qed.

Lemma crc_table_of_globvar gv:
  (forall b o, gv _crc_table = Vptr b o -> o = Ptrofs.zero) ->
  globvar2pred gv (_crc_table, v_crc_table) |-- crc_table_at Ers gv.
Proof.
  intros HP. unfold crc_table_at.
  let d := eval vm_compute in (as32 (gvar_init v_crc_table)) in
  match d with Some ?data =>
    change (globvar2pred gv (_crc_table, v_crc_table)) with (init_data_list2pred gv (map Init_int32 data) Ers (gv _crc_table));
    eapply derives_trans; [ apply gv_arr32; [ discriminate | vm_compute; reflexivity | exact HP ] | ];
    apply derives_refl'; rewrite crc_table_ints; [reflexivity | vm_compute; reflexivity]
  end.
Qed.

Lemma x2n_table_of_globvar gv:
  (forall b o, gv _x2n_table = Vptr b o -> o = Ptrofs.zero) ->
  globvar2pred gv (_x2n_table, v_x2n_table) |-- x2n_table_at Ers gv.
Proof.
  intros HP. unfold x2n_table_at.
  let d := eval vm_compute in (as32 (gvar_init v_x2n_table)) in
  match d with Some ?data =>
    change (globvar2pred gv (_x2n_table, v_x2n_table)) with (init_data_list2pred gv (map Init_int32 data) Ers (gv _x2n_table));
    eapply derives_trans; [ apply gv_arr32; [ discriminate | vm_compute; reflexivity | exact HP ] | ];
    apply derives_refl'; rewrite x2n_table_ints; [reflexivity | vm_compute; reflexivity]
  end.
Qed.

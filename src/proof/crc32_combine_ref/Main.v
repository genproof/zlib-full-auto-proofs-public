(* The main of harness/crc32_combine_ref.c, proved against main_core_spec (memory manager, crc32.c's
   tables). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Zlib.contracts.x_crc32_combine_ref.
Require Import Zlib.harness.x_crc32_combine_ref.code.
Require Import Zlib.proof.crc32.SpecCombine Zlib.proof.crc32.Combine Zlib.proof.crc32.HarnessRef.
Require Import Zlib.proof.crc32.Facts.
Require Import Zlib.proof.adler32.MainLib Zlib.proof.crc32.Globals.
Require Import Zlib.proof.adler32.Ptr.

Definition p := Zlib.contracts.x_crc32_combine_ref.whole_prog.
Definition comps := ltac:(let x := eval vm_compute in (prog_composites p) in exact x).
Definition cprog : Clight.program := Clightdefs.mkprogram comps nil nil 1%positive Logic.I.
#[export] Instance CS : compspecs. make_compspecs cprog. Defined.
#[export] Instance CC1 : change_composite_env Zlib.units.Crc32.CS CS. make_cs_preserve Zlib.units.Crc32.CS CS. Defined.

Ltac tok_cs :=
  match goal with |- context [@malloc_token Zlib.units.Crc32.CS ?sh ?t] =>
    rewrite (@malloc_token_change_composite Zlib.units.Crc32.CS CS CC1 sh t) by reflexivity end;
  cancel.

Ltac tok_norm :=
  repeat match goal with |- context [@malloc_token Zlib.units.Crc32.CS ?sh ?t] =>
    rewrite (@malloc_token_change_composite Zlib.units.Crc32.CS CS CC1 sh t) by reflexivity end.

Ltac side := try (solve [cancel | tok_cs | entailer!; arg_cmp]).

Definition R (gv: globals) : mpred := (crc_table_at Ers gv * x2n_table_at Ers gv)%logic.

Definition Gmain : funspecs := [crc32_z_spec; crc32_combine_spec; crc32_combine_gen_spec; crc32_combine_op_spec;
  ref_crc32_spec; ref_crc_byte_spec; (_quickproof_malloc, malloc_spec'); (_quickproof_free, free_spec');
  nondet_u32_spec; nondet_bytes_spec; gp_assert_spec; gp_assume_spec].

Lemma zeros_reg_range n r: 0 <= r < 2 ^ 32 -> 0 <= zeros_reg n r < 2 ^ 32.
Proof. intros. rewrite zeros_reg_iter. apply is32_iter. exact H. Qed.

Lemma zeros_reg_succ i r: 0 <= i -> zeros_reg (Z.to_nat (i + 1)) r = ref_crc_byte (zeros_reg (Z.to_nat i) r) 0.
Proof. intros. rewrite Z2Nat.inj_add by lia. rewrite Nat.add_comm. reflexivity. Qed.

Lemma and_low32 x: 0 <= x <= Int64.max_unsigned ->
  Int64.and (Int64.repr x) (Int64.repr 4294967295) = Int64.repr (x mod 2 ^ 32).
Proof.
  intros. unfold Int64.and. rewrite !Int64.unsigned_repr by rep_lia.
  change 4294967295 with (Z.ones 32). rewrite Z.land_ones by lia. reflexivity.
Qed.

Lemma xor_repr a b: 0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned ->
  Int64.xor (Int64.repr a) (Int64.repr b) = Int64.repr (Z.lxor a b).
Proof. intros. unfold Int64.xor. rewrite !Int64.unsigned_repr by rep_lia. reflexivity. Qed.

Lemma body_main: semax_body (QPvarspecs p) Gmain f_main (_main, main_core_spec R).
Proof.
  start_function.
  unfold R. Intros.
  (* pick(c0), pick(x), pick(y): unsigned longs *)
  assert_PROP (field_compatible tulong [] v_c0) as FCc by entailer!.
  sep_apply (data_at_ulong_bytes Tsh v_c0).
  assert_PROP (isptr v_c0) as Pc by entailer!.
  assert (Nc: v_c0 <> nullval) by (destruct v_c0; try contradiction; discriminate).
  forward_call (v_c0, 8, Tsh).
  { rewrite if_false by auto. cancel. }
  Intros bs. rewrite if_false by auto.
  match goal with H1: Zlength bs = 8, H2: Forall _ bs |- _ => sep_apply (pick_tulong Tsh bs v_c0 H1 H2 FCc) end.
  Intros vc0. clear dependent bs.
  assert (Ec: Vlong vc0 = Vlong (Int64.repr (Int64.unsigned vc0))) by (rewrite Int64.repr_unsigned; auto).
  rewrite Ec. clear Ec.
  assert (Hc0: 0 <= Int64.unsigned vc0 <= Int64.max_unsigned) by rep_lia.
  remember (Int64.unsigned vc0) as c0 eqn:Ec. clear Ec.
  assert_PROP (field_compatible tulong [] v_x) as FCx by entailer!.
  sep_apply (data_at_ulong_bytes Tsh v_x).
  assert_PROP (isptr v_x) as Px by entailer!.
  assert (Nx: v_x <> nullval) by (destruct v_x; try contradiction; discriminate).
  forward_call (v_x, 8, Tsh).
  { rewrite if_false by auto. cancel. }
  Intros bs. rewrite if_false by auto.
  match goal with H1: Zlength bs = 8, H2: Forall _ bs |- _ => sep_apply (pick_tulong Tsh bs v_x H1 H2 FCx) end.
  Intros vx. clear dependent bs.
  assert (Ex: Vlong vx = Vlong (Int64.repr (Int64.unsigned vx))) by (rewrite Int64.repr_unsigned; auto).
  rewrite Ex. clear Ex.
  assert (Hx: 0 <= Int64.unsigned vx <= Int64.max_unsigned) by rep_lia.
  remember (Int64.unsigned vx) as x eqn:Ex. clear Ex.
  assert_PROP (field_compatible tulong [] v_y) as FCy by entailer!.
  sep_apply (data_at_ulong_bytes Tsh v_y).
  assert_PROP (isptr v_y) as Py by entailer!.
  assert (Ny: v_y <> nullval) by (destruct v_y; try contradiction; discriminate).
  forward_call (v_y, 8, Tsh).
  { rewrite if_false by auto. cancel. }
  Intros bs. rewrite if_false by auto.
  match goal with H1: Zlength bs = 8, H2: Forall _ bs |- _ => sep_apply (pick_tulong Tsh bs v_y H1 H2 FCy) end.
  Intros vy. clear dependent bs.
  assert (Ey: Vlong vy = Vlong (Int64.repr (Int64.unsigned vy))) by (rewrite Int64.repr_unsigned; auto).
  rewrite Ey. clear Ey.
  assert (Hy: 0 <= Int64.unsigned vy <= Int64.max_unsigned) by rep_lia.
  remember (Int64.unsigned vy) as y eqn:Ey. clear Ey.
  (* pick(z): a long *)
  assert_PROP (field_compatible tlong [] v_z) as FCz by entailer!.
  sep_apply (data_at_long_bytes Tsh v_z).
  assert_PROP (isptr v_z) as Pz by entailer!.
  assert (Nz: v_z <> nullval) by (destruct v_z; try contradiction; discriminate).
  forward_call (v_z, 8, Tsh).
  { rewrite if_false by auto. cancel. }
  Intros bs. rewrite if_false by auto.
  match goal with H1: Zlength bs = 8, H2: Forall _ bs |- _ => sep_apply (pick_tlong Tsh bs v_z H1 H2 FCz) end.
  Intros vz. clear dependent bs.
  assert (Ez: Vlong vz = Vlong (Int64.repr (Int64.signed vz))) by (rewrite Int64.repr_signed; auto).
  rewrite Ez. clear Ez.
  assert (Hz: Int64.min_signed <= Int64.signed vz <= Int64.max_signed) by rep_lia.
  remember (Int64.signed vz) as z eqn:Ez. clear Ez.
  (* na, nb *)
  forward_call tt. Intros na.
  forward_call tt. Intros nb.
  ifpost _t'3 (Int.repr (if andb (na <=? 2 ^ 20) (nb <=? 2 ^ 20) then 1 else 0)).
  { forward. entailer!. change (Int.shl (Int.repr 1) (Int.repr 20)) with (Int.repr (2^20)) in *.
    rewrite Int.unsigned_repr in * by rep_lia. destruct (Z.leb_spec na (2^20)); [|lia]. simpl andb.
    unfold bool2val. arg_cmp. }
  { forward. entailer!. change (Int.shl (Int.repr 1) (Int.repr 20)) with (Int.repr (2^20)) in *.
    rewrite Int.unsigned_repr in * by rep_lia. destruct (Z.leb_spec na (2^20)); [lia|]. reflexivity. }
  forward_call (Int.repr (if andb (na <=? 2 ^ 20) (nb <=? 2 ^ 20) then 1 else 0)).
  assumed. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1, E2.
  (* ab = malloc(na + nb) *)
  forward_call (tarray tuchar (na + nb), gv).
  { simpl. rewrite Z.max_r by lia. rep_lia. }
  Intros ab.
  destruct (eq_dec ab nullval) as [PB|PB].
  { subst ab. forward_if False. { ret0. } { first [contradiction | discriminate]. } }
  Intros.
  ifsame. { contradiction. } { forward. entailer!. }
  (* nondet_bytes(ab, na + nb) *)
  forward_call (ab, na + nb, Ews).
  { rewrite if_false by auto. cancel. }
  Intros data. rewrite if_false by auto.
  match goal with H: Zlength data = _ |- _ => rename H into Hdn end.
  match goal with H: Forall _ data |- _ => rename H into Hdb end.
  assert (Hby: is_bytes data) by exact Hdb.
  assert_PROP (isptr ab) as Pab by entailer!.
  fold (bytes_rep data).
  (* ca = crc32_z(c0, ab, na) *)
  assert (CBa: cbuf_ok false ab Ews ab 0 (na + nb) na (bytes_rep data) (sublist 0 na data)).
  { pose proof (cbuf_ok_prefix Ews ab data na ltac:(auto) Pab Hby ltac:(lia) ltac:(lia)) as C.
    rewrite Hdn in C. exact C. }
  forward.
  forward_call (c0, ab, na, false, Ews, ab, 0, na + nb, bytes_rep data, sublist 0 na data, true, Ews, gv, Ers).
  all: side.
  forward.
  tok_norm.
  (* cb = crc32_z(0, ab + na, nb) *)
  assert (CBb: cbuf_ok false (offset_val na ab) Ews ab na (na + nb) nb (bytes_rep data) (sublist na (na + nb) data)).
  { pose proof (cbuf_ok_slice Ews ab data na nb ltac:(auto) Pab Hby ltac:(lia) ltac:(lia) ltac:(lia)) as C.
    rewrite Hdn in C. exact C. }
  forward_call (0, offset_val na ab, nb, false, Ews, ab, na, na + nb, bytes_rep data, sublist na (na + nb) data,
                true, Ews, gv, Ers).
  all: side.
  forward.
  tok_norm.
  (* want = ref_crc32(c0, ab, na + nb) *)
  assert (CBw: cbuf_ok false ab Ews ab 0 (na + nb) (na + nb) (bytes_rep data) data).
  { pose proof (cbuf_ok_whole Ews ab data ltac:(auto) Hby Pab) as C. rewrite Hdn in C. exact C. }
  forward_call (c0, ab, Ews, ab, 0, na + nb, bytes_rep data, na + nb, data).
  forward.
  pose proof (ref_crc32_range c0 (sublist 0 na data) (is_bytes_sublist _ _ _ Hby)) as Ra. unfold is32 in Ra.
  pose proof (ref_crc32_range 0 (sublist na (na + nb) data) (is_bytes_sublist _ _ _ Hby)) as Rb. unfold is32 in Rb.
  assert (Happ: crc32_combine_val (ref_crc32 c0 (sublist 0 na data)) (ref_crc32 0 (sublist na (na + nb) data)) nb
                = ref_crc32 c0 data).
  { pose proof (crc32_combine_val_app c0 (sublist 0 na data) (sublist na (na + nb) data)
      (is_bytes_sublist _ _ _ Hby) (is_bytes_sublist _ _ _ Hby)) as C.
    rewrite Zlength_sublist in C by lia. replace (na + nb - na) with nb in C by lia.
    rewrite C by lia. rewrite <- sublist_split by lia. rewrite sublist_same by lia. reflexivity. }
  (* crc32_combine(ca, cb, nb) == want *)
  forward_call (ref_crc32 c0 (sublist 0 na data), ref_crc32 0 (sublist na (na + nb) data), nb, gv, Ers).
  all: side.
  rewrite Happ.
  forward_call (Int.repr 1).
  all: side.
  (* crc32_combine_op(ca, cb, crc32_combine_gen(nb)) == want *)
  forward_call (nb, gv, Ers).
  all: side.
  assert (Rg: is32 (crc32_combine_gen_val nb)).
  { unfold crc32_combine_gen_val. destruct (Z.ltb_spec nb 0); [unfold is32; lia | apply x2n_val_is32; rep_lia]. }
  unfold is32 in Rg.
  forward_call (ref_crc32 c0 (sublist 0 na data), ref_crc32 0 (sublist na (na + nb) data), crc32_combine_gen_val nb).
  all: side.
  change (crc32_combine_op_val (ref_crc32 c0 (sublist 0 na data)) (ref_crc32 0 (sublist na (na + nb) data))
            (crc32_combine_gen_val nb))
    with (crc32_combine_val (ref_crc32 c0 (sublist 0 na data)) (ref_crc32 0 (sublist na (na + nb) data)) nb).
  rewrite Happ.
  forward_call (Int.repr 1).
  all: side.
  (* the arbitrary x, y, z *)
  forward.
  forward_if (PROP () LOCAL (temp _ab ab; lvar _z tlong v_z; lvar _y tulong v_y; lvar _x tulong v_x; lvar _c0 tulong v_c0; gvars gv)
    SEP (x2n_table_at Ers gv; data_at Ews (tarray tuchar (na + nb)) (bytes_rep data) ab;
         crc_table_at Ers gv; malloc_token Ews (tarray tuchar (na + nb)) ab; mem_mgr gv;
         data_at Tsh tlong (Vlong (Int64.repr z)) v_z; data_at Tsh tulong (Vlong (Int64.repr y)) v_y;
         data_at Tsh tulong (Vlong (Int64.repr x)) v_x; data_at Tsh tulong (Vlong (Int64.repr c0)) v_c0)).
  { (* z < 0 *)
    rewrite !Int64.signed_repr in * by rep_lia.
    forward. forward. forward.
    forward_call (x, y, z, gv, Ers).
    rewrite crc32_combine_val_neg by lia.
    forward_call (Int.repr 1).
    all: side.
    forward.
    forward_call (z, gv, Ers).
    replace (crc32_combine_gen_val z) with 0 by (unfold crc32_combine_gen_val; destruct (Z.ltb_spec z 0); lia).
    forward_call (Int.repr 1).
    all: side.
    forward. forward.
    forward_call (x, y, 0).
    all: try rep_lia.
    replace (crc32_combine_op_val x y 0) with 0 by reflexivity.
    forward_call (Int.repr 1).
    all: side.
    }
  rewrite !Int64.signed_repr in * by rep_lia.
  forward.
  forward_if (PROP () LOCAL (temp _ab ab; lvar _z tlong v_z; lvar _y tulong v_y; lvar _x tulong v_x; lvar _c0 tulong v_c0; gvars gv)
    SEP (x2n_table_at Ers gv; data_at Ews (tarray tuchar (na + nb)) (bytes_rep data) ab;
         crc_table_at Ers gv; malloc_token Ews (tarray tuchar (na + nb)) ab; mem_mgr gv;
         data_at Tsh tlong (Vlong (Int64.repr z)) v_z; data_at Tsh tulong (Vlong (Int64.repr y)) v_y;
         data_at Tsh tulong (Vlong (Int64.repr x)) v_x; data_at Tsh tulong (Vlong (Int64.repr c0)) v_c0)).
  { (* 0 <= z <= 2^20: reg over z zero bytes *)
    forward. forward.
    forward.
    forward_loop (EX i: Z, PROP (0 <= i <= z)
      LOCAL (temp _i (Vlong (Int64.repr i)); temp _reg (Vlong (Int64.repr (zeros_reg (Z.to_nat i) (x mod 2 ^ 32))));
             temp _ab ab; lvar _z tlong v_z; lvar _y tulong v_y; lvar _x tulong v_x; lvar _c0 tulong v_c0; gvars gv)
      SEP (x2n_table_at Ers gv; data_at Ews (tarray tuchar (na + nb)) (bytes_rep data) ab;
         crc_table_at Ers gv; malloc_token Ews (tarray tuchar (na + nb)) ab; mem_mgr gv;
         data_at Tsh tlong (Vlong (Int64.repr z)) v_z; data_at Tsh tulong (Vlong (Int64.repr y)) v_y;
         data_at Tsh tulong (Vlong (Int64.repr x)) v_x; data_at Tsh tulong (Vlong (Int64.repr c0)) v_c0))
    continue: (EX i: Z, PROP (0 <= i < z)
      LOCAL (temp _i (Vlong (Int64.repr i)); temp _reg (Vlong (Int64.repr (zeros_reg (Z.to_nat (i + 1)) (x mod 2 ^ 32))));
             temp _ab ab; lvar _z tlong v_z; lvar _y tulong v_y; lvar _x tulong v_x; lvar _c0 tulong v_c0; gvars gv)
      SEP (x2n_table_at Ers gv; data_at Ews (tarray tuchar (na + nb)) (bytes_rep data) ab;
         crc_table_at Ers gv; malloc_token Ews (tarray tuchar (na + nb)) ab; mem_mgr gv;
         data_at Tsh tlong (Vlong (Int64.repr z)) v_z; data_at Tsh tulong (Vlong (Int64.repr y)) v_y;
         data_at Tsh tulong (Vlong (Int64.repr x)) v_x; data_at Tsh tulong (Vlong (Int64.repr c0)) v_c0))
    break: (PROP ()
      LOCAL (temp _reg (Vlong (Int64.repr (zeros_reg (Z.to_nat z) (x mod 2 ^ 32)))); temp _ab ab; lvar _z tlong v_z; lvar _y tulong v_y; lvar _x tulong v_x; lvar _c0 tulong v_c0; gvars gv)
      SEP (x2n_table_at Ers gv; data_at Ews (tarray tuchar (na + nb)) (bytes_rep data) ab;
         crc_table_at Ers gv; malloc_token Ews (tarray tuchar (na + nb)) ab; mem_mgr gv;
         data_at Tsh tlong (Vlong (Int64.repr z)) v_z; data_at Tsh tulong (Vlong (Int64.repr y)) v_y;
         data_at Tsh tulong (Vlong (Int64.repr x)) v_x; data_at Tsh tulong (Vlong (Int64.repr c0)) v_c0)).
    { Exists 0. entailer!. simpl. change (Int.unsigned (Int.repr (-1))) with (Z.ones 32).
      rewrite Z.land_ones by lia. reflexivity. }
    { Intros i. forward.
      forward_if.
      { assert (Hiz: i < z).
        { match goal with H: Int64.lt _ _ = true |- _ => unfold Int64.lt in H;
            rewrite !Int64.signed_repr in H by rep_lia; destruct (zlt i z); [lia | discriminate] end. }
        pose proof (zeros_reg_range (Z.to_nat i) (x mod 2 ^ 32) ltac:(apply Z.mod_pos_bound; lia)) as Rr.
        forward_call (zeros_reg (Z.to_nat i) (x mod 2 ^ 32), 0).
        forward.
        Exists i. rewrite zeros_reg_succ by lia. entailer!. }
      { assert (Hiz: i = z).
        { match goal with H: Int64.lt _ _ = false |- _ => unfold Int64.lt in H;
            rewrite !Int64.signed_repr in H by rep_lia; destruct (zlt i z); [discriminate | lia] end. }
        subst i. forward. entailer!. } }
    { Intros i. forward. Exists (i + 1). entailer!. }
    (* r = crc32_combine(x, y, z) *)
    pose proof (zeros_reg_range (Z.to_nat z) (x mod 2 ^ 32) ltac:(apply Z.mod_pos_bound; lia)) as Rz.
    assert (Rym: 0 <= y mod 2 ^ 32 < 2 ^ 32) by (apply Z.mod_pos_bound; lia).
    forward. forward. forward.
    forward_call (x, y, z, gv, Ers).
    pose proof (crc32_combine_val_range x y z ltac:(rep_lia)) as Rc. unfold is32 in Rc.
    rewrite crc32_combine_val_zeros in Rc |- * by rep_lia.
    forward.
    forward.
    forward_call (Int.repr 1).
    { entailer!. simpl. change (Int.unsigned (Int.repr (-1))) with 4294967295.
      change 4294967295 with (Z.ones 32). rewrite Z.land_ones by lia. change (Z.pow_pos 2 32) with (2 ^ 32).
      rewrite xor_repr by rep_lia. rewrite Int64.eq_true. reflexivity. }
    all: side.
    forward_call (Int.repr 1).
    { entailer!. simpl. change (Z.pow_pos 2 32) with (2 ^ 32). unfold Int64.ltu.
      change (Int.unsigned (Int.repr (-1))) with 4294967295. rewrite !Int64.unsigned_repr by rep_lia.
      destruct (zlt 4294967295 _); [lia | reflexivity]. }
    entailer!. }
  { forward. entailer!. }
  (* free(ab); return 0 *)
  forward_call (tarray tuchar (na + nb), ab, gv).
  { rewrite if_false by auto. sep_apply (data_at_data_at_ Ews (tarray tuchar (na + nb)) (bytes_rep data) ab).
    cancel. }
  ret0.
Qed.

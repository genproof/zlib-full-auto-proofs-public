(* deflateInit2_ with a caller-supplied allocator, the rest of the function when the four buffer allocations
   succeeded (see InitZKit.v): s->prev is cleared, the symbol buffer, level, strategy and method are set and
   deflateReset completes the state: the stream of [dstream_za] with the five allocations as events. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DModel3 Zlib.proof.deflate.DCS.
Require Import Zlib.deflate.code.
Require Import Zlib.proof.za.deflate.Stmt.
Require Import Zlib.proof.deflate.ApiKit.
Require Import Zlib.proof.deflate.ZeroBytes Zlib.proof.deflate.InitKit Zlib.proof.deflate.InitKit2.
Require Import Zlib.proof.deflate.InitFacts Zlib.proof.deflate.InitTac.
Require Import Zlib.proof.deflate.InitParts.
Require Import Zlib.proof.za.deflate.InitZParts.
Require Import Zlib.proof.za.deflate.InitZKit.

Arguments zrest : simpl never.
Arguments zpad : simpl never.
Arguments zlate : simpl never.

Section ZA.
Context {ZA : zallocator}.

Lemma iz_ok_part {Espec : OracleKind} (strmp : val) (level wbits mem strategy : Z) (vp : val)
    (vsh : share) (vers : list Z) (ssize : Z) (ni tin tout msgv adler dt st0 : val) (gv : globals) (tr : list zev)
    (sp pw pp ph pb : val) :
  s32_ok level -> s32_ok 8 -> s32_ok wbits -> s32_ok mem -> s32_ok strategy -> s32_ok ssize ->
  readable_share vsh -> 1 <= Zlength vers -> -128 <= Znth 0 vers < 128 ->
  (forall a1 a2 a3 a4 a5 : bool, exists r : option dstate * strm * Z,
     c_deflateInit2_ true true false level 8 wbits mem strategy a1 a2 a3 a4 a5 zrst0 = Some r) ->
  za_alloc <> nullval -> za_free <> nullval -> is_pointer_or_null za_opaque ->
  za_now tr + (5968 + 65536 + 65536 + 131072 + 131072) <= za_cap ->
  (Znth 0 vers =? 49) = true -> (ssize =? 112) = true -> strmp <> nullval -> isptr za_alloc -> isptr za_free ->
  -15 <= wbits -> i_bad level 8 wbits mem strategy = false ->
  1 <= mem <= 9 -> 9 <= i_wb9 wbits <= 15 -> 0 <= i_lv level <= 9 -> 0 <= strategy <= 4 -> 0 <= i_wr wbits <= 2 ->
  512 <= Z.shiftl 1 (i_wb9 wbits) <= 32768 -> 256 <= Z.shiftl 1 (mem + 7) <= 65536 ->
  128 <= Z.shiftl 1 (mem + 6) <= 32768 ->
  sp <> nullval -> field_compatible t_ds [] sp ->
  1 <= Z.shiftl 1 (i_wb9 wbits) <= 65536 -> 1 <= Z.shiftl 1 (mem + 7) <= 65536 ->
  1 <= Z.shiftl 1 (mem + 6) <= 65536 ->
  ((if EqDec_val pw nullval then true else false) || (if EqDec_val pp nullval then true else false) ||
   (if EqDec_val ph nullval then true else false) || (if EqDec_val pb nullval then true else false))%bool = false ->
  semax Delta_iz (iz_pre strmp level wbits mem strategy vp vsh vers ni tin tout adler dt gv tr sp pw pp ph pb)
    IZ_rest (iz_fpost strmp level wbits mem strategy vp vsh vers ssize ni tin tout msgv adler st0 gv tr).
Proof.
  intros H H0 H1 H2 H3 H4 SH H5 Hv0 H6 Hza Hzf Hop Hcap Hv1 Hs1 H7 Pza Pzf Hwm Hbad Hmem Hwb9 Hlv Hstr Hwr BW BH BL
    Hsp FCs HW HHS HLB Hb21.
  cbv [IZ_fail IZ_rest IZ iz_ssub f_deflateInit2_ fn_body repeat app].
  unfold iz_pre, iz_fpost, Delta_iz. abbreviate_semax.
  assert (pw <> nullval /\ pp <> nullval /\ ph <> nullval /\ pb <> nullval) as (Ew & Ep & Eh & Eb)
    by (clear - Hb21; destruct (EqDec_val pw nullval), (EqDec_val pp nullval), (EqDec_val ph nullval),
          (EqDec_val pb nullval); simpl in Hb21; try discriminate; auto).
  rewrite !if_false by auto.
  rewrite (zalloc_ev_nn pw), (zalloc_ev_nn pp), (zalloc_ev_nn ph), (zalloc_ev_nn pb) by auto.
  Intros.
  forward. forward.
  assert_PROP (field_compatible (tarray tushort (Z.shiftl 1 (i_wb9 wbits))) [] pp) as FCp by entailer!.
  sep_apply (data_at__bytes Ews (tarray tushort (Z.shiftl 1 (i_wb9 wbits))) pp FCp).
  replace (sizeof (tarray tushort (Z.shiftl 1 (i_wb9 wbits)))) with (2 * Z.shiftl 1 (i_wb9 wbits))
    by (simpl; rewrite Z.max_r by lia; lia).
  forward_call (Ews, pp, 2 * Z.shiftl 1 (i_wb9 wbits), 0).
  { entailer!. destruct pp; try contradiction;
    try (match goal with H: field_compatible _ _ (Vlong _) |- _ => destruct H; contradiction end).
    simpl. rewrite Int64.Z_mod_modulus_eq, Z.mod_small by rep_lia. rewrite Int.unsigned_repr by rep_lia.
    f_equal. f_equal. f_equal. rewrite Z.mul_comm. reflexivity. }
  change (0 mod 256) with 0.
  sep_apply (prev_zero (Z.shiftl 1 (i_wb9 wbits)) pp ltac:(lia) FCp).
  forward. forward. forward. forward. forward. forward. forward. forward.
  replace (Int.divu (Int.repr (mem + 7 + 3 - 1)) (Int.repr 3)) with (Int.repr ((mem + 7 + 3 - 1) / 3))
    by (unfold Int.divu; rewrite !Int.unsigned_repr by rep_lia; reflexivity).
  replace (Int64.mul (Int64.repr (Int.unsigned (Int.repr (Z.shiftl 1 (mem + 6))))) (Int64.repr (Int.signed (Int.repr 4))))
    with (Int64.repr (Z.shiftl 1 (mem + 6) * 4))
    by (rewrite Int.unsigned_repr, Int.signed_repr by rep_lia; rewrite mul64_repr; reflexivity).
  assert_PROP (isptr pb) as Ppb by entailer!.
  replace (force_val (sem_add_ptr_int tuchar Unsigned pb (Vint (Int.repr (Z.shiftl 1 (mem + 6))))))
    with (offset_val (Z.shiftl 1 (mem + 6)) pb).
  2: { destruct pb; try contradiction. unfold sem_add_ptr_int. simpl. f_equal.
       rewrite Ptrofs.mul_commut, Ptrofs.mul_one. unfold Ptrofs.of_intu, Ptrofs.of_int.
       rewrite Int.unsigned_repr by rep_lia. reflexivity. }
  rewrite sub_repr, mul_repr.
  change (Int.zero_ext 8 (Int.zero_ext 8 (Int.repr 8))) with (Int.repr 8).
  pose proof (init_ok_stream_za level wbits mem strategy strmp sp pw pp ph pb dt gv Hwm Hbad H H3 H2 FCs) as IOK.
  cbv zeta in IOK. sep_apply IOK. clear IOK.
  destruct (H6 true true true true true) as [r0 Hr0].
  rewrite init_ok in Hr0 by auto.
  set (z0 := zrst0) in *.
  change (set_z_msg z0 None) with z0 in Hr0.
  destruct (c_deflateReset (i_state level 8 wbits mem strategy) z0) as [[[s1 z1] ret]|] eqn:ER;
    [ | discriminate].
  assert (Eret: ret = Z_OK) by (apply (reset_code _ _ _ ER); reflexivity). subst ret.
  forward_call (0, Some (i_state level 8 wbits mem strategy), strmp, nullval, ni, tin, tout, nullval, adler,
    (Some s1, z1, Z_OK), gv).
  { unfold reset_fields. cancel. }
  { unfold on_state, c_on_state. rewrite ER. reflexivity. }
  Intros msgv'.
  forward.
  Exists true true true true true (Some s1, z1, Z_OK).
  cbn [fst snd].
  match goal with |- context [za_res gv ?TR] => Exists TR end. Exists msgv'.
  change (Z_OK =? Z_VERSION_ERROR) with false. change (Z_OK =? Z_OK) with true. cbv iota.
  entailer!.
  split.
  - rewrite Hv1, Hs1, init_ok by auto. change (set_z_msg z0 None) with z0. rewrite ER. reflexivity.
  - destruct (reset_sizes _ _ _ _ _ ER) as (E1 & E2 & E3).
    unfold dinit_events. rewrite E1, E2, E3.
    change (d_w_size (i_state level 8 wbits mem strategy)) with (Z.shiftl 1 (i_wb9 wbits)).
    change (d_hash_size (i_state level 8 wbits mem strategy)) with (Z.shiftl 1 (mem + 7)).
    change (tr_lit_bufsize (d_tr (i_state level 8 wbits mem strategy))) with (Z.shiftl 1 (mem + 6)).
    rewrite <- !app_assoc. simpl app. rewrite !(Z.mul_comm (Z.shiftl _ _)). reflexivity.
Qed.

End ZA.

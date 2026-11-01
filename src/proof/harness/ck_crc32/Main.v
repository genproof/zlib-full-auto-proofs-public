(* The main of harness/ck_crc32.c, proved against main_core_spec (memory manager, crc32.c's table):
   the harness's bit-by-bit CRC-32 (the register preset to start ^ 0xffffffff, per byte an xor and eight
   shift/xor steps) is the register of ref_crc32 after each byte, so the final comparison with crc32_z holds. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Zlib.contracts.ck_crc32.
Require Import Zlib.harness.ck_crc32.code.
Require Import Zlib.proof.crc32.Spec Zlib.proof.crc32.Facts Zlib.proof.crc32.IntFacts Zlib.proof.crc32.HarnessRef.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.harness.laws_common.Spec.

Definition p := Zlib.contracts.ck_crc32.whole_prog.
Definition comps := ltac:(let x := eval vm_compute in (prog_composites p) in exact x).
Definition cprog : Clight.program := Clightdefs.mkprogram comps nil nil 1%positive Logic.I.
#[export] Instance CS : compspecs. make_compspecs cprog. Defined.
#[export] Instance CC1 : change_composite_env Zlib.units.Crc32.CS CS. make_cs_preserve Zlib.units.Crc32.CS CS. Defined.
#[export] Instance CC2 : change_composite_env Zlib.units.Adler32.CS CS. make_cs_preserve Zlib.units.Adler32.CS CS. Defined.

Ltac tok_cs :=
  repeat match goal with |- context [@malloc_token Zlib.units.Crc32.CS ?sh ?t] =>
    rewrite (@malloc_token_change_composite Zlib.units.Crc32.CS CS CC1 sh t) by reflexivity end;
  repeat match goal with |- context [@malloc_token Zlib.units.Adler32.CS ?sh ?t] =>
    rewrite (@malloc_token_change_composite Zlib.units.Adler32.CS CS CC2 sh t) by reflexivity end;
  cancel.

Definition R (gv: globals) : mpred := crc_table_at Ers gv.

Definition Gmain : funspecs := [upto_spec; any_bytes_spec; crc32_z_spec;
  nondet_u32_spec; gp_assert_spec].

Lemma body_main: semax_body (QPvarspecs p) Gmain f_main (_main, main_core_spec R).
Proof.
  start_function.
  unfold R. Intros.
  forward_call (9223372036854775807). Intros len.
  forward_call (len, gv).
  Intros vret. destruct vret as [buf data]. simpl fst in *; simpl snd in *.
  destruct (eq_dec buf nullval) as [PB|PB].
  { subst buf. forward_if False. { ret0. } { first [contradiction | discriminate]. } }
  forward_if True.
  { assert_PROP (isptr buf) by entailer!. destruct buf; try contradiction; discriminate. }
  { forward. entailer!. }
  Intros.
  (* start = nondet_u32(); crc = start ^ 0xffffffff *)
  apply -> seq_assoc. apply -> seq_assoc.
  forward_call tt. Intros start.
  forward. forward.
  rewrite Int.unsigned_repr by rep_lia.
  rewrite crc_post_int by rep_lia.
  set (c0 := Z.lxor start crc_mask).
  assert (Hc0: 0 <= c0 < 2 ^ 32) by (apply lxor_lt_pow2; [lia | rep_lia | apply crc_mask_range]).
  assert_PROP (field_compatible (tarray tuchar len) [] buf) as FC by entailer!.
  (* the register after i bytes *)
  forward_for_simple_bound len (EX i: Z,
    PROP () LOCAL (temp _crc (Vlong (Int64.repr (crc_reg c0 data i))); temp _start (Vlong (Int64.repr start));
                   temp _buf buf; temp _len (Vlong (Int64.repr len)); gvars gv)
    SEP (mem_mgr gv; malloc_token Ews (tarray tuchar len) buf;
         data_at Ews (tarray tuchar len) (bytes_rep data) buf; crc_table_at Ers gv)).
  { entailer!. }
  { assert (Hb: 0 <= Znth i data <= Byte.max_unsigned) by (apply is_bytes_Znth; auto; lia).
    assert (Hc: 0 <= crc_reg c0 data i < 2 ^ 32) by (apply crc_reg_range; auto).
    assert (Eb: @Znth val Vundef i (bytes_rep data) = Vint (Int.repr (Znth i data)))
      by (unfold bytes_rep; rewrite Znth_map by lia; reflexivity).
    forward.
    { entailer!. unfold bytes_rep. rewrite Znth_map by lia. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
    rewrite Eb.
    forward.
    (* eight shift/xor steps: ref_crc_byte *)
    set (x := Z.lxor (crc_reg c0 data i) (Znth i data)).
    assert (Hx: 0 <= x < 2 ^ 32) by (apply lxor_lt_pow2; rep_lia).
    forward_for_simple_bound 8 (EX k: Z,
      PROP () LOCAL (temp _crc (Vlong (Int64.repr (Nat.iter (Z.to_nat k) crc_step x)));
                     temp _i (Vlong (Int64.repr i)); temp _start (Vlong (Int64.repr start));
                     temp _buf buf; temp _len (Vlong (Int64.repr len)); gvars gv)
      SEP (mem_mgr gv; malloc_token Ews (tarray tuchar len) buf;
           data_at Ews (tarray tuchar len) (bytes_rep data) buf; crc_table_at Ers gv)).
    - entailer!. unfold Int64.xor. rewrite ?Int.unsigned_repr by rep_lia.
      rewrite !Int64.unsigned_repr by rep_lia. reflexivity.
    - assert (Hk: 0 <= Nat.iter (Z.to_nat i0) crc_step x < 2 ^ 32) by (apply iter_crc_step_range; auto).
      forward_if.
      + match goal with H: Int64.and _ _ <> _ |- _ => rewrite odd_and64 in H by auto end.
        destruct (Z.odd (Nat.iter (Z.to_nat i0) crc_step x)) eqn:O; [ | contradiction].
        forward. entailer!.
        rewrite Int64.xor_commut.
        rewrite crc_step_odd64 by auto. rewrite Z2Nat.inj_add by lia. rewrite Nat.add_1_r. reflexivity.
      + match goal with H: Int64.and _ _ = _ |- _ => rewrite odd_and64 in H by auto end.
        destruct (Z.odd (Nat.iter (Z.to_nat i0) crc_step x)) eqn:O.
        { exfalso. apply Int64.one_not_zero. auto. }
        forward. entailer!.
        rewrite crc_step_even64 by auto. rewrite Z2Nat.inj_add by lia. rewrite Nat.add_1_r. reflexivity.
    - entailer!. rewrite <- crc_reg_succ by lia. reflexivity. }
  (* crc32_z(start, buf, len) == crc ^ 0xffffffff *)
  assert_PROP (isptr buf) as Pbuf by entailer!.
  subst len.
  assert (CB: cbuf_ok false buf Ews buf 0 (Zlength data) (Zlength data) (bytes_rep data) data)
    by (apply cbuf_ok_whole; auto).
  forward_call (start, buf, Zlength data, false, Ews, buf, 0, Zlength data, bytes_rep data, data, true, Ews, gv, Ers).
  { tok_cs. }
  assert (Hr: 0 <= crc_reg c0 data (Zlength data) < 2 ^ 32) by (apply crc_reg_range; auto).
  assert (Ef: Int64.xor (Int64.repr (crc_reg c0 data (Zlength data))) (Int64.repr (Int.unsigned (Int.repr (-1)))) =
              Int64.repr (ref_crc32 start data)).
  { rewrite crc_post_int by auto. rewrite crc_reg_full. unfold ref_crc32.
    rewrite (Z.mod_small start) by rep_lia. reflexivity. }
  forward_call (Int.repr 1).
  { entailer!. simpl. rewrite Ef. rewrite Int64.eq_true. reflexivity. }
  { ret0. }
Qed.

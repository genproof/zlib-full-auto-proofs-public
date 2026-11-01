(* The main of harness/ck_adler32_combine.c, proved against main_core_spec (memory manager only: adler32.c has
   no globals): adler32_combine of the checksums of the two parts (the first from start, the second from 1) is
   the checksum of the whole from start, for any length up to PTRDIFF_MAX and any split. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Zlib.contracts.ck_adler32_combine.
Require Import Zlib.harness.ck_adler32_combine.code.
Require Import Zlib.proof.adler32.Model Zlib.proof.adler32.Spec Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.HarnessRef Zlib.proof.adler32.MainLib Zlib.proof.adler32.Ptr.
Require Import Zlib.proof.adler32_combine_ref.Algebra.
Require Import Zlib.proof.harness.laws_common.Spec.

Definition p := Zlib.contracts.ck_adler32_combine.whole_prog.
Definition comps := ltac:(let x := eval vm_compute in (prog_composites p) in exact x).
Definition cprog : Clight.program := Clightdefs.mkprogram comps nil nil 1%positive Logic.I.
#[export] Instance CS : compspecs. make_compspecs cprog. Defined.
#[export] Instance CC2 : change_composite_env Zlib.units.Adler32.CS CS. make_cs_preserve Zlib.units.Adler32.CS CS. Defined.

Ltac tok_cs :=
  match goal with |- context [@malloc_token Zlib.units.Adler32.CS ?sh ?t] =>
    rewrite (@malloc_token_change_composite Zlib.units.Adler32.CS CS CC2 sh t) by reflexivity end;
  cancel.

Ltac tok_norm :=
  repeat match goal with |- context [@malloc_token Zlib.units.Adler32.CS ?sh ?t] =>
    rewrite (@malloc_token_change_composite Zlib.units.Adler32.CS CS CC2 sh t) by reflexivity end.

Ltac side := try (solve [cancel | tok_cs | entailer!]).

Definition R (gv: globals) : mpred := emp.

Definition Gmain : funspecs := [upto_spec; any_bytes_spec; adler32_z_spec; adler32_combine_spec; gp_assert_spec].

(* start = high << 16 | low with both halves at most 65520: a valid Adler-32 value. *)
Lemma start_valid high low: 0 <= high <= 65520 -> 0 <= low <= 65520 ->
  Int64.or (Int64.shl (Int64.repr high) (Int64.repr (Int.unsigned (Int.repr 16)))) (Int64.repr low) =
    Int64.repr (high * 65536 + low) /\ adler_valid (high * 65536 + low).
Proof.
  intros Hh Hl. split; [apply or_pack_int; lia | ].
  unfold adler_valid, ADLER_BASE. rewrite adler_lo_pack, adler_hi_pack by lia. lia.
Qed.

Lemma body_main: semax_body (QPvarspecs p) Gmain f_main (_main, main_core_spec R).
Proof.
  start_function.
  unfold R. Intros.
  forward_call (Int64.max_signed).
  Intros len.
  forward_call len.
  Intros split.
  forward_call (len, gv).
  Intros vret. destruct vret as [buf data]. simpl fst in *. simpl snd in *.
  match goal with H: Zlength data = _ |- _ => rename H into Hdn end.
  match goal with H: is_bytes data |- _ => rename H into Hby end.
  destruct (eq_dec buf nullval) as [PB|PB].
  { subst buf. forward_if False. { ret0. } { first [contradiction | discriminate]. } }
  Intros.
  forward_if (PROP () LOCAL (temp _buf buf; temp _split (Vlong (Int64.repr split));
                             temp _len (Vlong (Int64.repr len)); gvars gv)
    SEP (mem_mgr gv; malloc_token Ews (tarray tuchar len) buf;
         data_at Ews (tarray tuchar len) (bytes_rep data) buf)).
  { contradiction. }
  { forward. entailer!. }
  forward_call 65520. Intros high.
  forward_call 65520. Intros low.
  forward.
  destruct (start_valid high low) as [Est Vst]; [lia | lia | ].
  rewrite Est. clear Est. set (start := high * 65536 + low) in *.
  assert (Rst: 0 <= start <= Int64.max_unsigned) by (destruct Vst; rep_lia).
  assert_PROP (isptr buf) as Pbuf by entailer!.
  set (A := sublist 0 split data). set (B := sublist split len data).
  assert (CBA: cbuf_ok false buf Ews buf 0 len split (bytes_rep data) A)
    by (rewrite <- Hdn; apply cbuf_ok_prefix; auto; lia).
  assert (CBB: cbuf_ok false (offset_val split buf) Ews buf split len (len - split) (bytes_rep data) B).
  { assert (C := cbuf_ok_slice Ews buf data split (len - split) ltac:(auto) Pbuf Hby ltac:(lia) ltac:(lia) ltac:(lia)).
    replace (split + (len - split)) with len in C by lia. rewrite Hdn in C. exact C. }
  assert (CBW: cbuf_ok false buf Ews buf 0 len len (bytes_rep data) data)
    by (rewrite <- Hdn; apply cbuf_ok_whole; auto).
  (* first = adler32_z(start, buf, split) *)
  forward_call (start, buf, split, false, Ews, buf, 0, len, bytes_rep data, A, true, Ews).
  all: side.
  tok_norm. rewrite adler32_z_val_ref by auto.
  (* second = adler32_z(1, buf + split, len - split) *)
  forward_call (1, offset_val split buf, len - split, false, Ews, buf, split, len, bytes_rep data, B, true, Ews).
  all: side.
  tok_norm. rewrite adler32_z_val_ref by apply adler_valid_1.
  (* whole = adler32_z(start, buf, len) *)
  forward_call (start, buf, len, false, Ews, buf, 0, len, bytes_rep data, data, true, Ews).
  all: side.
  tok_norm. rewrite adler32_z_val_ref by auto.
  (* adler32_combine(first, second, (z_off_t) (len - split)) == whole *)
  pose proof (ref_adler32_valid start A Vst) as VA.
  pose proof (ref_adler32_valid 1 B adler_valid_1) as VB.
  assert (RA: 0 <= ref_adler32 start A <= Int64.max_unsigned) by (destruct VA; rep_lia).
  assert (RB: 0 <= ref_adler32 1 B <= Int64.max_unsigned) by (destruct VB; rep_lia).
  forward_call (ref_adler32 start A, ref_adler32 1 B, len - split).
  all: side.
  assert (CMB: adler32_combine_result (ref_adler32 start A) (ref_adler32 1 B) (len - split) = ref_adler32 start data).
  { replace (len - split) with (Zlength B) by (unfold B; rewrite Zlength_sublist; lia).
    rewrite adler32_combine_app by auto. unfold A, B. rewrite <- sublist_split by lia.
    rewrite sublist_same by lia. reflexivity. }
  rewrite CMB.
  forward_call (Int.repr 1).
  { entailer!. simpl. rewrite Int64.eq_true. reflexivity. }
  ret0.
Qed.

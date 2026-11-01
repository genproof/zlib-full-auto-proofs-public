(* The main of harness/ck_crc32_combine.c, proved against main_core_spec (memory manager, crc32.c's
   tables): for any bytes of any length up to PTRDIFF_MAX, any split and any 32-bit start value, both
   crc32_combine and crc32_combine_op with crc32_combine_gen's operator give the CRC-32 of the whole
   (Combine.crc32_combine_val_app). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Zlib.contracts.ck_crc32_combine.
Require Import Zlib.harness.ck_crc32_combine.code.
Require Import Zlib.proof.crc32.Spec Zlib.proof.crc32.SpecCombine Zlib.proof.crc32.Combine.
Require Import Zlib.proof.crc32.Facts.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib Zlib.proof.crc32.Globals.
Require Import Zlib.proof.adler32.Ptr.
Require Import Zlib.proof.harness.laws_common.Spec.

Definition p := Zlib.contracts.ck_crc32_combine.whole_prog.
Definition comps := ltac:(let x := eval vm_compute in (prog_composites p) in exact x).
Definition cprog : Clight.program := Clightdefs.mkprogram comps nil nil 1%positive Logic.I.
#[export] Instance CS : compspecs. make_compspecs cprog. Defined.
#[export] Instance CC1 : change_composite_env Zlib.units.Crc32.CS CS. make_cs_preserve Zlib.units.Crc32.CS CS. Defined.
#[export] Instance CC2 : change_composite_env Zlib.units.Adler32.CS CS. make_cs_preserve Zlib.units.Adler32.CS CS. Defined.

(* The byte object of any_bytes, at the adler32 unit's compspecs, is the same at the law's. *)
Lemma bytes_adler_cs sh n (v: list val) q:
  @data_at Zlib.units.Adler32.CS sh (tarray tuchar n) v q = @data_at CS sh (tarray tuchar n) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC2); [apply JMeq_refl | reflexivity]. Qed.

Ltac tok_cs :=
  match goal with |- context [@malloc_token Zlib.units.Crc32.CS ?sh ?t] =>
    rewrite (@malloc_token_change_composite Zlib.units.Crc32.CS CS CC1 sh t) by reflexivity end;
  cancel.

Ltac tok_norm :=
  repeat match goal with |- context [@malloc_token Zlib.units.Crc32.CS ?sh ?t] =>
    rewrite (@malloc_token_change_composite Zlib.units.Crc32.CS CS CC1 sh t) by reflexivity end.

Ltac side := try (solve [cancel | tok_cs | entailer!; arg_cmp]).

Definition R (gv: globals) : mpred := (crc_table_at Ers gv * x2n_table_at Ers gv)%logic.

Definition Gmain : funspecs := [upto_spec; any_bytes_spec; crc32_z_spec; crc32_combine_spec;
  crc32_combine_gen_spec; crc32_combine_op_spec; (_quickproof_malloc, malloc_spec');
  nondet_u32_spec; nondet_size_spec; nondet_bytes_spec; gp_assert_spec].

Lemma body_main: semax_body (QPvarspecs p) Gmain f_main (_main, main_core_spec R).
Proof.
  start_function.
  unfold R. Intros.
  (* len = upto(PTRDIFF_MAX); split = upto(len) *)
  forward_call 9223372036854775807.
  Intros len.
  forward_call len.
  Intros split.
  (* buf = any_bytes(len) *)
  forward_call (len, gv).
  Intros vret. destruct vret as [buf bs]. simpl fst in *. simpl snd in *.
  destruct (eq_dec buf nullval) as [PB|PB].
  { subst buf.
    forward_if False. { ret0. } { first [contradiction | discriminate]. } }
  match goal with H: Zlength bs = _ |- _ => rename H into Hbn end.
  match goal with H: is_bytes bs |- _ => rename H into Hby end.
  assert_PROP (isptr buf) as Pb by entailer!.
  ifsame.
  { contradiction. }
  { forward. entailer!. }
  (* start = nondet_u32() *)
  rewrite <- seq_assoc.
  eapply semax_seq' with (P' := EX s: Z, PROP (0 <= s <= Int.max_unsigned)
    LOCAL (temp _start (Vlong (Int64.repr s)); temp _buf buf; temp _split (Vlong (Int64.repr split));
           temp _len (Vlong (Int64.repr len)); gvars gv)
    SEP (mem_mgr gv; malloc_token Ews (tarray tuchar len) buf; data_at Ews (tarray tuchar len) (bytes_rep bs) buf;
         crc_table_at Ers gv; x2n_table_at Ers gv)).
  { forward_call tt. Intros s. forward. Exists s. entailer!. }
  Intros s. abbreviate_semax.
  (* first = crc32_z(start, buf, split) *)
  assert (CBa: cbuf_ok false buf Ews buf 0 len split (bytes_rep bs) (sublist 0 split bs)).
  { pose proof (cbuf_ok_prefix Ews buf bs split ltac:(auto) Pb Hby ltac:(lia) ltac:(lia)) as C.
    rewrite Hbn in C. exact C. }
  forward_call (s, buf, split, false, Ews, buf, 0, len, bytes_rep bs, sublist 0 split bs, true, Ews, gv, Ers).
  all: side.
  (* second = crc32_z(0, buf + split, len - split) *)
  assert (CBb: cbuf_ok false (offset_val split buf) Ews buf split len (len - split) (bytes_rep bs)
                 (sublist split len bs)).
  { pose proof (cbuf_ok_slice Ews buf bs split (len - split) ltac:(auto) Pb Hby ltac:(lia) ltac:(lia) ltac:(lia))
      as C.
    rewrite Hbn in C. replace (split + (len - split)) with len in C by lia. exact C. }
  forward_call (0, offset_val split buf, len - split, false, Ews, buf, split, len, bytes_rep bs,
                sublist split len bs, true, Ews, gv, Ers).
  all: side.
  (* whole = crc32_z(start, buf, len) *)
  assert (CBw: cbuf_ok false buf Ews buf 0 len len (bytes_rep bs) bs).
  { pose proof (cbuf_ok_whole Ews buf bs ltac:(auto) Hby Pb) as C. rewrite Hbn in C. exact C. }
  forward_call (s, buf, len, false, Ews, buf, 0, len, bytes_rep bs, bs, true, Ews, gv, Ers).
  all: side.
  pose proof (ref_crc32_range s (sublist 0 split bs) (is_bytes_sublist _ _ _ Hby)) as Ra. unfold is32 in Ra.
  pose proof (ref_crc32_range 0 (sublist split len bs) (is_bytes_sublist _ _ _ Hby)) as Rb. unfold is32 in Rb.
  assert (Happ: crc32_combine_val (ref_crc32 s (sublist 0 split bs)) (ref_crc32 0 (sublist split len bs))
                  (len - split) = ref_crc32 s bs).
  { pose proof (crc32_combine_val_app s (sublist 0 split bs) (sublist split len bs)
      (is_bytes_sublist _ _ _ Hby) (is_bytes_sublist _ _ _ Hby)) as C.
    rewrite Zlength_sublist in C by lia.
    rewrite C by lia. rewrite <- sublist_split by lia. rewrite sublist_same by lia. reflexivity. }
  (* crc32_combine(first, second, len - split) == whole *)
  forward_call (ref_crc32 s (sublist 0 split bs), ref_crc32 0 (sublist split len bs), len - split, gv, Ers).
  all: side.
  rewrite Happ.
  forward_call (Int.repr 1).
  all: side.
  (* op = crc32_combine_gen(len - split); crc32_combine_op(first, second, op) == whole *)
  forward_call (len - split, gv, Ers).
  all: side.
  assert (Rg: is32 (crc32_combine_gen_val (len - split))).
  { unfold crc32_combine_gen_val. destruct (Z.ltb_spec (len - split) 0); [unfold is32; lia | apply x2n_val_is32; rep_lia]. }
  unfold is32 in Rg.
  forward_call (ref_crc32 s (sublist 0 split bs), ref_crc32 0 (sublist split len bs), crc32_combine_gen_val (len - split)).
  all: side.
  change (crc32_combine_op_val (ref_crc32 s (sublist 0 split bs)) (ref_crc32 0 (sublist split len bs))
            (crc32_combine_gen_val (len - split)))
    with (crc32_combine_val (ref_crc32 s (sublist 0 split bs)) (ref_crc32 0 (sublist split len bs)) (len - split)).
  rewrite Happ.
  forward_call (Int.repr 1).
  all: side.
  ret0.
Qed.

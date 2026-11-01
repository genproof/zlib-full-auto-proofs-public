(* The main of harness/crc32_ref.c, proved against main_core_spec (memory manager, crc32.c's tables). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Zlib.contracts.x_crc32_ref.
Require Import Zlib.harness.x_crc32_ref.code.
Require Import Zlib.proof.crc32.SpecCombine Zlib.proof.crc32.Combine Zlib.proof.crc32.HarnessRef.
Require Import Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.MainLib Zlib.proof.crc32.Globals.
Require Import Zlib.proof.adler32.Ptr.

Definition p := Zlib.contracts.x_crc32_ref.whole_prog.
Definition comps := ltac:(let x := eval vm_compute in (prog_composites p) in exact x).
Definition cprog : Clight.program := Clightdefs.mkprogram comps nil nil 1%positive Logic.I.
#[export] Instance CS : compspecs. make_compspecs cprog. Defined.
#[export] Instance CC1 : change_composite_env Zlib.units.Crc32.CS CS. make_cs_preserve Zlib.units.Crc32.CS CS. Defined.
#[export] Instance CC2 : change_composite_env Zlib.units.Adler32.CS CS. make_cs_preserve Zlib.units.Adler32.CS CS. Defined.

Ltac tok_cs :=
  match goal with |- context [@malloc_token Zlib.units.Crc32.CS ?sh ?t] =>
    rewrite (@malloc_token_change_composite Zlib.units.Crc32.CS CS CC1 sh t) by reflexivity end;
  cancel.

Ltac tok_norm :=
  repeat match goal with |- context [@malloc_token Zlib.units.Crc32.CS ?sh ?t] =>
    rewrite (@malloc_token_change_composite Zlib.units.Crc32.CS CS CC1 sh t) by reflexivity end.

Ltac side := try (solve [cancel | tok_cs | entailer!; arg_cmp]).

Definition R (gv: globals) : mpred := (crc_table_at Ers gv * x2n_table_at Ers gv)%logic.

Definition Gmain : funspecs := [crc32_z_spec; crc32_spec; get_crc_table_spec; ref_crc32_spec; ref_crc_byte_spec;
  bytes_copy_spec; bytes_same_spec; (_quickproof_malloc, malloc_spec'); (_quickproof_free, free_spec');
  nondet_u32_spec; nondet_bytes_spec; gp_assert_spec; gp_assume_spec].

Lemma body_main: semax_body (QPvarspecs p) Gmain f_main (_main, main_core_spec R).
Proof.
  start_function.
  unfold R. Intros.
  (* pick(crc) *)
  assert_PROP (field_compatible tulong [] v_crc) as FCc by entailer!.
  sep_apply (data_at_ulong_bytes Tsh v_crc).
  assert_PROP (isptr v_crc) as Pcrc by entailer!.
  assert (Ncrc: v_crc <> nullval) by (destruct v_crc; try contradiction; discriminate).
  forward_call (v_crc, 8, Tsh).
  { rewrite if_false by auto. cancel. }
  Intros bs. rewrite if_false by auto.
  match goal with H1: Zlength bs = 8, H2: Forall _ bs |- _ => sep_apply (pick_tulong Tsh bs v_crc H1 H2 FCc) end.
  Intros vcrc.
  assert (Ecrc: Vlong vcrc = Vlong (Int64.repr (Int64.unsigned vcrc))) by (rewrite Int64.repr_unsigned; auto).
  rewrite Ecrc. clear Ecrc.
  assert (Hcrc: 0 <= Int64.unsigned vcrc <= Int64.max_unsigned) by rep_lia.
  remember (Int64.unsigned vcrc) as crc eqn:Ecrc. clear Ecrc.
  forward_call tt. Intros n.
  forward_call tt. Intros k.
  forward_call tt. Intros len.
  forward_call (Int.repr (if n <=? 2 ^ 20 then 1 else 0)).
  { entailer!. arg_cmp. }
  assumed. apply Z.leb_le in E.
  forward_call (Int.repr (if k <=? n then 1 else 0)).
  { entailer!. arg_cmp. }
  assumed. apply Z.leb_le in E0.
  forward_call (tarray tuchar n, gv).
  { simpl. rewrite Z.max_r by lia. rep_lia. }
  Intros buf.
  forward_call (tarray tuchar n, gv).
  { simpl. rewrite Z.max_r by lia. rep_lia. }
  Intros snap.
  destruct (eq_dec buf nullval) as [PB|PB].
  { subst buf.
    ifpost _t'6 Int.one.
    { forward. entailer!. }
    { contradiction. }
    forward_if False. { ret0. } { first [contradiction | discriminate]. } }
  Intros.
  assert (n0: 0 <= n) by lia.
  destruct (eq_dec snap nullval) as [PS|PS].
  { subst snap.
    ifpost _t'6 Int.one.
    { contradiction. }
    { forward. entailer!. }
    forward_if False. { ret0. } { first [contradiction | discriminate]. } }
  Intros.
  ifpost _t'6 Int.zero.
  { contradiction. }
  { forward. entailer!. destruct snap; try contradiction; reflexivity. }
  ifsame. { first [contradiction | discriminate]. } { forward. entailer!. }
  (* the buffer: n arbitrary bytes, and its snapshot *)
  forward_call (buf, n, Ews).
  { rewrite if_false by auto. cancel. }
  Intros data. rewrite if_false by auto.
  match goal with H: Zlength data = n |- _ => rename H into Hdn end.
  match goal with H: Forall _ data |- _ => rename H into Hdb end.
  assert (Hby: is_bytes data) by exact Hdb.
  subst n.
  assert_PROP (isptr buf) as Pbuf by entailer!.
  assert_PROP (isptr snap) as Psnap by entailer!.
  fold (bytes_rep data).
  assert (CB: cbuf_ok false buf Ews buf 0 (Zlength data) (Zlength data) (bytes_rep data) data)
    by (apply cbuf_ok_whole; auto).
  forward_call (snap, Ews, buf, Ews, buf, 0, Zlength data, bytes_rep data, Zlength data, data).
  (* want = ref_crc32(crc, buf, n) *)
  forward.
  forward_call (crc, buf, Ews, buf, 0, Zlength data, bytes_rep data, Zlength data, data).
  forward.
  (* a = crc32_z(crc, buf, n) *)
  forward.
  forward_call (crc, buf, Zlength data, false, Ews, buf, 0, Zlength data, bytes_rep data, data, true, Ews, gv, Ers).
  all: side.
  forward.
  pose proof (ref_crc32_range crc data Hby) as Rcrc. unfold is32 in Rcrc.
  tok_norm.
  forward_call (Int.repr 1).
  all: side.
  forward_call (Int.repr 1).
  all: side.
  (* crc32(crc, buf, n) *)
  forward.
  forward_call (crc, buf, Zlength data, false, Ews, buf, 0, Zlength data, bytes_rep data, data, true, Ews, gv, Ers).
  all: side.
  tok_norm.
  forward_call (Int.repr 1).
  all: side.
  (* crc32_z(crc32_z(crc, buf, k), buf + k, n - k) *)
  forward.
  assert (CBk: cbuf_ok false buf Ews buf 0 (Zlength data) k (bytes_rep data) (sublist 0 k data))
    by (apply cbuf_ok_prefix; auto; lia).
  forward_call (crc, buf, k, false, Ews, buf, 0, Zlength data, bytes_rep data, sublist 0 k data, true, Ews, gv, Ers).
  all: side.
  tok_norm.
  pose proof (ref_crc32_range crc (sublist 0 k data) (is_bytes_sublist _ _ _ Hby)) as Rk. unfold is32 in Rk.
  assert (CBk2: cbuf_ok false (offset_val k buf) Ews buf k (Zlength data) (Zlength data - k) (bytes_rep data)
                  (sublist k (Zlength data) data)).
  { replace (sublist k (Zlength data) data) with (sublist k (k + (Zlength data - k)) data) by (f_equal; lia).
    apply cbuf_ok_slice; auto; lia. }
  forward_call (ref_crc32 crc (sublist 0 k data), offset_val k buf, Zlength data - k, false, Ews, buf, k, Zlength data,
                bytes_rep data, sublist k (Zlength data) data, true, Ews, gv, Ers).
  all: side.
  tok_norm.
  rewrite ref_crc32_app by (apply is_bytes_sublist; auto).
  rewrite <- sublist_split by lia. rewrite sublist_same by lia.
  forward_call (Int.repr 1).
  all: side.
  (* crc32(crc, Z_NULL, len) and crc32_z(crc, Z_NULL, len) *)
  forward.
  forward_call (crc, nullval, len, true, Ews, nullval, 0, 0, @nil val, @nil Z, false, Ews, gv, Ers).
  all: side.
  forward_call (Int.repr 1).
  all: side.
  forward.
  forward_call (crc, nullval, len, true, Ews, nullval, 0, 0, @nil val, @nil Z, false, Ews, gv, Ers).
  all: side.
  forward_call (Int.repr 1).
  all: side.
  (* bytes_same(buf, snap, n) *)
  assert (CBs: cbuf_ok false snap Ews snap 0 (Zlength data) (Zlength data) (bytes_rep data) data)
    by (apply cbuf_ok_whole; auto).
  forward_call (buf, Ews, buf, 0, Zlength data, bytes_rep data, data, snap, Ews, snap, 0, Zlength data,
                bytes_rep data, data, Zlength data).
  all: side.
  destruct (list_eq_dec Z.eq_dec data data) as [_|NE]; [ | contradiction].
  forward_call (Int.repr 1).
  all: side.
  (* the table *)
  forward_call (gv, Ers).
  all: side.
  forward_for_simple_bound 256 (EX i: Z,
    PROP ()
    LOCAL (temp _t (gv Zlib.crc32.code._crc_table); temp _buf buf; temp _snap snap; lvar _crc tulong v_crc; gvars gv)
    SEP (crc_table_at Ers gv; x2n_table_at Ers gv; mem_mgr gv;
         malloc_token Ews (tarray tuchar (Zlength data)) buf;
         data_at Ews (tarray tuchar (Zlength data)) (bytes_rep data) buf;
         malloc_token Ews (tarray tuchar (Zlength data)) snap;
         data_at Ews (tarray tuchar (Zlength data)) (bytes_rep data) snap;
         data_at Tsh tulong (Vlong (Int64.repr crc)) v_crc)).
  { entailer!. }
  { assert (Z8: Int.zero_ext 8 (Int.repr i) = Int.repr i)
      by (apply zero_ext_inrange; rewrite Int.unsigned_repr by rep_lia; change (two_p 8 - 1) with 255; lia).
    forward_call (0, i).
    { entailer!. simpl. rewrite !Z8. reflexivity. }
    all: try (split; rep_lia).
    unfold crc_table_at. change_compspecs CS.
    forward.
    { entailer!. unfold crc_table_rep. rewrite Znth_map by (rewrite Zlength_crc_table_vals; lia). simpl. auto. }
    assert (Ti: @Znth val Vundef i crc_table_rep = Vint (Int.repr (ref_crc_byte 0 i))).
    { unfold crc_table_rep. rewrite Znth_map by (rewrite Zlength_crc_table_vals; lia).
      rewrite Znth_crc_table_vals by lia. reflexivity. }
    rewrite Ti.
    assert (Ri: 0 <= ref_crc_byte 0 i < 2 ^ 32) by (apply ref_crc_byte_range; lia).
    forward_call (Int.repr 1).
    all: side.
    all: try (entailer!; unfold crc_table_at; change_compspecs CS; cancel). }
  (* free, free, return 0 *)
  forward_call (tarray tuchar (Zlength data), buf, gv).
  { rewrite if_false by auto. sep_apply (data_at_data_at_ Ews (tarray tuchar (Zlength data)) (bytes_rep data) buf).
    cancel. }
  forward_call (tarray tuchar (Zlength data), snap, gv).
  { rewrite if_false by auto. sep_apply (data_at_data_at_ Ews (tarray tuchar (Zlength data)) (bytes_rep data) snap).
    cancel. }
  ret0.
Qed.

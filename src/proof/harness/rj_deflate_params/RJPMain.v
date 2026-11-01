(* Law rj_deflate_params: main of harness/rj_deflate_params.c against main_core_spec R (statement in
   RJPMainStmt.v).  main draws the five parameters, computes the harness's [valid], initializes the stream
   with new_stream, calls deflateInit2_ and checks its return code: Z_OK when [valid], else Z_STREAM_ERROR
   (Z_MEM_ERROR returns at once).  The return code comes from deflateInit2__spec_v9 and LawFacts.af_init; the
   harness's [valid] is LawFacts.params_ok. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DCS Zlib.proof.deflate.Rep Zlib.proof.deflate.DSpec Zlib.proof.deflate.DSpec9.
Require Import Zlib.proof.deflate.LawFacts Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.deflate.Obligations.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.rj_deflate_params.RJPCS Zlib.proof.harness.rj_deflate_params.RJPMainStmt.
Require Import Zlib.harness.rj_deflate_params.code.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.
Module DC := Zlib.deflate.code.

(* the harness's [valid], as main computes it (the short-circuit && and || of int comparisons) *)
Definition rjp_valid (level method wbits mem strategy : Z) : bool :=
  (-1 <=? level) && (level <=? 9) && (method =? 8) && (1 <=? mem) && (mem <=? 9) &&
  (0 <=? strategy) && (strategy <=? 4) &&
  ((8 <=? wbits) && (wbits <=? 15) || (-15 <=? wbits) && (wbits <=? -9) ||
   (25 <=? wbits) && (wbits <=? 31)).

(* it is deflateInit2_'s parameter check (LawFacts.params_ok): windowBits 8 is accepted only with the zlib
   wrapper, -8 and 24 are rejected *)
Lemma rjp_valid_params_ok level method wbits mem strategy :
  rjp_valid level method wbits mem strategy = params_ok level method wbits mem strategy.
Proof.
  unfold rjp_valid, params_ok, wb_of, wrap_of.
  destruct (wbits <? 0) eqn:E1; destruct (wbits >? 15) eqn:E2; destruct (level =? -1) eqn:E3;
  apply eq_iff_eq_true;
  repeat rewrite ?andb_true_iff, ?orb_true_iff, ?negb_true_iff, ?Z.leb_le, ?Z.ltb_lt, ?Z.eqb_eq, ?Z.gtb_ltb,
    ?Z.ltb_ge, ?Z.eqb_neq in *; lia.
Qed.

(* the local z_stream at the compress unit's compspecs (new_stream's) and at DCS.CS (deflateInit2_'s) *)
Lemma rjp_strm_cs sh (v : @reptype Zlib.units.Compress.CS t_zs) (p : val) :
  @data_at Zlib.units.Compress.CS sh t_zs v p = @data_at DCS.CS sh t_strm v p.
Proof.
  apply equal_f. apply (@data_at_change_composite _ _ CC_compress_dcs); [apply JMeq_refl | reflexivity].
Qed.

(* the uninitialized local as new_stream's precondition *)
Lemma rjp_strm_undef (p : val) :
  data_at_ Ews t_strm p |--
  @data_at Zlib.units.Compress.CS Ews t_zs
    (zs_val Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef) p.
Proof. rewrite rjp_strm_cs. apply derives_refl. Qed.

(* new_stream's postcondition as deflateInit2__spec_v9's precondition pieces, the three fields the spec does not
   mention (avail_in, next_out, avail_out) and the padding *)
Lemma rjp_new_stream_split (p : val) :
  @data_at Zlib.units.Compress.CS Ews t_zs
    (zs_val nullval (vi 0) Vundef nullval (vi 0) Vundef Vundef Vundef nullval nullval nullval Vundef Vundef Vundef) p
  |-- field_at Ews t_strm (DOT DC._next_in) nullval p * reset_fields p Vundef Vundef Vundef Vundef *
      (field_at Ews t_strm (DOT DC._avail_in) (vi 0) p * field_at Ews t_strm (DOT DC._next_out) nullval p *
       field_at Ews t_strm (DOT DC._avail_out) (vi 0) p) *
      field_at Ews t_strm (DOT DC._zalloc) nullval p * field_at Ews t_strm (DOT DC._zfree) nullval p *
      field_at Ews t_strm (DOT DC._opaque) nullval p * field_at Ews t_strm (DOT DC._data_type) Vundef p *
      field_at Ews t_strm (DOT DC._state) Vundef p * field_at_ Ews t_strm (DOT DC._reserved) p *
      BoundKit.strm_pad p.
Proof.
  rewrite rjp_strm_cs. unfold reset_fields, BoundKit.strm_pad. unfold_data_at (data_at _ _ _ p). cancel.
Qed.

(* the stream's fields, whatever their values, back to the whole uninitialized struct *)
Lemma rjp_fields_back (p nin tin tout msgv adler ai no ao st za zf op dt : val) :
  field_at Ews t_strm (DOT DC._next_in) nin p * reset_fields p tin tout msgv adler *
  (field_at Ews t_strm (DOT DC._avail_in) ai p * field_at Ews t_strm (DOT DC._next_out) no p *
   field_at Ews t_strm (DOT DC._avail_out) ao p) *
  field_at Ews t_strm (DOT DC._state) st p * field_at Ews t_strm (DOT DC._zalloc) za p *
  field_at Ews t_strm (DOT DC._zfree) zf p * field_at Ews t_strm (DOT DC._opaque) op p *
  field_at Ews t_strm (DOT DC._data_type) dt p * field_at_ Ews t_strm (DOT DC._reserved) p *
  BoundKit.strm_pad p
  |-- data_at_ Ews t_strm p.
Proof.
  apply derives_trans with (@data_at Zlib.units.Compress.CS Ews t_zs
    (zs_val nin ai tin no ao tout msgv st za zf op dt adler Vundef) p);
    rewrite rjp_strm_cs; [| apply data_at_data_at_].
  unfold_data_at (data_at _ _ _ p). unfold reset_fields, BoundKit.strm_pad, field_at_; simpl. cancel.
Qed.

(* deflateInit2__spec_v9's postcondition, whatever the outcome, back to the struct (the stream's allocations
   and the allocator's function pointers are dropped) *)
Lemma rjp_init_back (os : option dstate) (code : Z) (p : val) (gv : globals) :
  ob_dstream_to_end ->
  forall nin tin tout msgv adler ai no ao : val,
  match os with
  | Some _ => dstream 2 os p nullval gv
  | None => EX st : val, EX za : val, EX zf : val, EX op' : val, EX dt' : val,
            !! (code = Z_VERSION_ERROR -> st = Vundef) &&
            (zfuncs gv * field_at_ Ews t_strm (DOT DC._reserved) p *
             field_at Ews t_strm (DOT DC._state) st p * field_at Ews t_strm (DOT DC._zalloc) za p *
             field_at Ews t_strm (DOT DC._zfree) zf p * field_at Ews t_strm (DOT DC._opaque) op' p *
             field_at Ews t_strm (DOT DC._data_type) dt' p)
  end *
  field_at Ews t_strm (DOT DC._next_in) nin p * reset_fields p tin tout msgv adler *
  (field_at Ews t_strm (DOT DC._avail_in) ai p * field_at Ews t_strm (DOT DC._next_out) no p *
   field_at Ews t_strm (DOT DC._avail_out) ao p) *
  BoundKit.strm_pad p
  |-- data_at_ Ews t_strm p * TT.
Proof.
  intros TE nin tin tout msgv adler ai no ao. destruct os as [s|].
  - sep_apply (TE (Some s) p nullval gv). unfold dstream_end. Intros p0 dt.
    sep_apply (rjp_fields_back p nin tin tout msgv adler ai no ao (p_s p0) (gv DC._zcalloc) (gv DC._zcfree)
                 nullval dt). cancel.
  - Intros st za zf op' dt'.
    sep_apply (rjp_fields_back p nin tin tout msgv adler ai no ao st za zf op' dt'). cancel.
Qed.

(* forward over an [if] that sets the temporary [t] to [v] in both branches *)
Ltac fif t v := match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
  forward_if (PROPx P (LOCALx (temp t v :: Q) (SEPx R))) end.

(* == of two ints, as Z.eqb *)
Lemma int_eq_repr_signed (a b : Z) :
  Int.min_signed <= a <= Int.max_signed -> Int.min_signed <= b <= Int.max_signed ->
  Int.eq (Int.repr a) (Int.repr b) = (a =? b).
Proof.
  intros. rewrite Int.eq_signed, !Int.signed_repr by assumption.
  destruct (zeq a b), (Z.eqb_spec a b); congruence.
Qed.

(* the value of a comparison chain, by cases on its comparisons (main's tests are on such values) *)
Ltac vcase := unfold Int.lt in *; rewrite ?Int.signed_repr in * by rep_lia;
  rewrite ?int_eq_repr_signed in * by rep_lia;
  repeat match goal with
  | |- context [Z.leb ?a ?b] => destruct (Z.leb_spec a b)
  | |- context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b)
  | |- context [zlt ?a ?b] => destruct (zlt a b)
  | |- context [zeq ?a ?b] => destruct (zeq a b)
  | H : ?T |- _ =>
      lazymatch T with typed_true _ _ => idtac | typed_false _ _ => idtac end;
      match T with
      | context [Z.leb ?a ?b] => destruct (Z.leb_spec a b)
      | context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b)
      end
  end; cbn [andb orb negb] in *; try lia;
  try match goal with H : typed_true _ _ |- _ => inversion H; fail end;
  try match goal with H : typed_false _ _ |- _ => inversion H; fail end;
  reflexivity.

(* the same for a value built from main's four boolean tests (bv: level, method, memLevel, strategy; zl, rw, gz:
   the three windowBits ranges) *)
Ltac bcase a b c d := destruct a, b, c, d; cbn [andb orb negb] in *;
  try match goal with H : typed_true _ _ |- _ => inversion H; fail end;
  try match goal with H : typed_false _ _ |- _ => inversion H; fail end;
  reflexivity.

Lemma body_main : rjp_main_stmt.
Proof.
  intros [I [Iend AF]] TE. unfold rjp_main_stmt.
  start_function.
  forward_call tt. Intros n1.
  forward_call tt. Intros n2.
  forward_call tt. Intros n3.
  forward_call tt. Intros n4.
  forward_call tt. Intros n5.
  (* the five (int) casts: each parameter is the signed value of the drawn u32 *)
  rewrite <- (Int.repr_signed (Int.repr n1)), <- (Int.repr_signed (Int.repr n2)),
    <- (Int.repr_signed (Int.repr n3)), <- (Int.repr_signed (Int.repr n4)), <- (Int.repr_signed (Int.repr n5)).
  pose proof (Int.signed_range (Int.repr n1)). pose proof (Int.signed_range (Int.repr n2)).
  pose proof (Int.signed_range (Int.repr n3)). pose proof (Int.signed_range (Int.repr n4)).
  pose proof (Int.signed_range (Int.repr n5)).
  forget (Int.signed (Int.repr n1)) as level. forget (Int.signed (Int.repr n2)) as method.
  forget (Int.signed (Int.repr n3)) as wbits. forget (Int.signed (Int.repr n4)) as mem.
  forget (Int.signed (Int.repr n5)) as strategy.
  clear n1 n2 n3 n4 n5 H H0 H1 H2 H3.
  (* valid = level >= -1 && level <= 9 && method == Z_DEFLATED, then memLevel and strategy, then windowBits *)
  fif _t'6 (Val.of_bool ((-1 <=? level) && (level <=? 9))); [forward; entailer!; vcase .. |].
  fif _t'7 (Val.of_bool ((-1 <=? level) && (level <=? 9) && (method =? 8))); [forward; entailer!; vcase .. |].
  forward.
  set (b1 := ((-1 <=? level) && (level <=? 9) && (method =? 8))%bool).
  fif _t'8 (Val.of_bool (b1 && (1 <=? mem))); [forward; entailer!; subst b1; vcase .. |].
  fif _t'9 (Val.of_bool (b1 && (1 <=? mem) && (mem <=? 9))); [forward; entailer!; subst b1; vcase .. |].
  fif _t'10 (Val.of_bool (b1 && (1 <=? mem) && (mem <=? 9) && (0 <=? strategy)));
    [forward; entailer!; subst b1; vcase .. |].
  fif _t'11 (Val.of_bool (b1 && (1 <=? mem) && (mem <=? 9) && (0 <=? strategy) && (strategy <=? 4)));
    [forward; entailer!; subst b1; vcase .. |].
  forward.
  fif _t'12 (Val.of_bool ((8 <=? wbits) && (wbits <=? 15))); [forward; entailer!; vcase .. |].
  forward.
  fif _t'13 (Val.of_bool ((-15 <=? wbits) && (wbits <=? -9))); [forward; entailer!; vcase .. |].
  forward.
  fif _t'14 (Val.of_bool ((25 <=? wbits) && (wbits <=? 31))); [forward; entailer!; vcase .. |].
  forward.
  assert (HV : rjp_valid level method wbits mem strategy =
    (b1 && (1 <=? mem) && (mem <=? 9) && (0 <=? strategy) && (strategy <=? 4) &&
     ((8 <=? wbits) && (wbits <=? 15) || (-15 <=? wbits) && (wbits <=? -9) ||
      (25 <=? wbits) && (wbits <=? 31)))%bool) by reflexivity.
  forget (b1 && (1 <=? mem) && (mem <=? 9) && (0 <=? strategy) && (strategy <=? 4))%bool as bv.
  forget ((8 <=? wbits) && (wbits <=? 15))%bool as zl.
  forget ((-15 <=? wbits) && (wbits <=? -9))%bool as rw.
  forget ((25 <=? wbits) && (wbits <=? 31))%bool as gz.
  fif _t'15 (Val.of_bool (bv && (zl || rw || gz))).
  { fif _t'16 (Val.of_bool (zl || rw)).
    { forward. entailer!. bcase bv zl rw gz. }
    { forward. entailer!. bcase bv zl rw gz. }
    forward_if.
    { forward. entailer!. bcase bv zl rw gz. }
    { forward. forward. entailer!. bcase bv zl rw gz. } }
  { forward. entailer!. bcase bv zl rw gz. }
  forward.
  (* valid is params_ok *)
  rewrite <- HV, rjp_valid_params_ok.
  deadvars!. clear HV b1 bv zl rw gz.
  (* new_stream(&strm) and deflateInit2_ on the Ews half of the local *)
  rewrite (BoundKit.data_at__Tsh_split (Tstruct _z_stream_s noattr) v_strm).
  sep_apply (rjp_strm_undef v_strm).
  forward_call (v_strm, Ews, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef,
                Vundef, Vundef, Vundef, Vundef).
  sep_apply (rjp_new_stream_split v_strm).
  unfold R, version_at.
  assert (S : s32 level /\ s32 method /\ s32 wbits /\ s32 mem /\ s32 strategy) by (unfold s32; rep_lia).
  destruct S as (S1 & S2 & S3 & S4 & S5).
  pose proof (fun a1 a2 a3 a4 a5 => af_init _ _ AF level method wbits mem strategy a1 a2 a3 a4 a5 zrst0
                S1 S2 S3 S4 S5) as FIN.
  forward_call (v_strm, level, method, wbits, mem, strategy, gv vlit, Ers, [49; 46; 51; 46; 50; 0], 112,
                nullval, Vundef, Vundef, Vundef, Vundef, nullval, Vundef, Vundef, gv).
  { change (Zlength [49; 46; 51; 46; 50; 0]) with 6. cancel. }
  { split; [unfold s32_ok; rep_lia|]. split; [list_solve|]. split; [cbn; rep_lia|].
    intros a1 a2 a3 a4 a5. exact (proj1 (FIN a1 a2 a3 a4 a5)). }
  Intros vret. destruct vret as [[[[[a1 a2] a3] a4] a5] [[os z'] code]]. cbn [fst snd] in *.
  match goal with H : c_deflateInit2_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _ |- _ => rename H into HI end.
  change (Znth 0 [49; 46; 51; 46; 50; 0] =? 49) with true in HI. change (112 =? 112) with true in HI.
  destruct (proj2 (FIN a1 a2 a3 a4 a5) _ _ _ HI) as (Hc & Hse & Hok). clear FIN.
  Intros msgv'.
  (* the stream is not used any more: its memory back to the local's *)
  sep_apply (rjp_init_back os code v_strm gv TE).
  gather_SEP 0 4. replace_SEP 0 (data_at_ Tsh (Tstruct _z_stream_s noattr) v_strm * TT).
  { entailer!. rewrite (BoundKit.data_at__Tsh_split (Tstruct _z_stream_s noattr) v_strm). cancel. }
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx ((code <> Z_MEM_ERROR) :: P) (LOCALx Q (SEPx R))) end.
  { forward. Exists (Int.repr 0). entailer!. }
  { forward. entailer!. }
  Intros.
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx Q (SEPx R))) end.
  { destruct (params_ok level method wbits mem strategy) eqn:E; [| inversion H1].
    assert (code = Z_OK) by (destruct Hc as [-> | [-> | ->]]; [reflexivity | | contradiction];
                              pose proof (proj1 Hse eq_refl); discriminate).
    subst code.
    forward_call (Int.one). entailer!. }
  { destruct (params_ok level method wbits mem strategy) eqn:E; [inversion H1 |].
    assert (code = Z_STREAM_ERROR) by (apply Hse; reflexivity).
    subst code.
    forward_call (Int.one). entailer!. }
  forward. Exists (Int.repr 0). entailer!.
Qed.


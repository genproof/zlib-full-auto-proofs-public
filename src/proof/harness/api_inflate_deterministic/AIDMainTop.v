(* Law api_inflate_deterministic, main: the whole body from the do-while body (AIDMainKit.body_stmt):
   windowBits and gp_assume(inflate_window_ok(windowBits)) (windowBits in zlib.h's ranges, so that inflateInit2_
   returns Z_OK or Z_MEM_ERROR), input_len, the input (alloc_any_bytes) and `if (input == NULL) return 0;`,
   new_stream() on both streams, the two inflateInit2() calls, `return 0` on a Z_MEM_ERROR,
   gp_assert(code_first == Z_OK && code_second == Z_OK) (AIDFacts.df_init, df_init_swf), `read = 0`, the
   do-while (invariant AIDMainKit.dinv) and return 0. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.EnvBodies.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.proof.harness.laws_session.Facts.
Require Import Zlib.proof.harness.api_inflate_deterministic.AIDMainDefs.
Require Import Zlib.proof.harness.api_inflate_deterministic.AIDMainKit.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.harness.api_inflate_deterministic.code.
Local Open Scope logic.

(* VST's after_forward_call simplifies remove_localdef_temp with `simpl rlt_ident_eq`, which runs away on main's
   identifiers (_input against _input_len); each identifier comparison is decided by vm_compute instead. *)
Ltac aid_rlt_fix u :=
  lazymatch u with
  | context C [rlt_ident_eq ?a ?b] =>
      let v := eval vm_compute in (rlt_ident_eq a b) in
      let u2 := context C [v] in aid_rlt_fix u2
  | _ => u
  end.

Ltac simplify_remove_localdef_temp ::=
  match goal with |- context [remove_localdef_temp ?i ?L] =>
    let u := constr:(remove_localdef_temp i L) in
    let u' := eval lazy delta [remove_localdef_temp] beta iota in u in
    let u' := aid_rlt_fix u' in
    let u' := eval lazy beta iota in u' in
    let u' := eval lazy zeta in u' in
    change u with u'
  end.

(* a branch that cannot be taken *)
Ltac top_infeas := exfalso; first [ match goal with H: ?a <> ?b |- _ => solve [apply H; reflexivity] end
                              | match goal with H: _ |- _ => solve [discriminate H] end
                              | contradiction
                              | match goal with H: Int.repr _ = Int.repr _ |- _ =>
                                  apply repr_inj_signed in H; [lia | rep_lia | rep_lia] end
                              | lia ].

(* at a `return` after inflateInit2_ returned Z_OK: the struct given back to the stack frame *)
Lemma live_raw_frame gv sh q r L: istream_raw gv sh q r L |-- @data_at_ CS sh t_z q * TT.
Proof.
  unfold istream_raw. Intros.
  sep_apply (raw_frame gv sh q r nullval (l_sp L) (gv Zlib.inflate.code._zcalloc) (gv Zlib.inflate.code._zcfree)
               nullval).
  cancel.
Qed.

Lemma main_of : body_stmt -> aid_main_stmt.
Proof.
  intros DB J AF.
  start_function.
  unfold R_aid, R_of. Intros.
  make_func_ptr Zlib.inflate.code._zcalloc. make_func_ptr Zlib.inflate.code._zcfree.
  gather_SEP (func_ptr' _ (gv inflate.code._zcalloc)) (func_ptr' _ (gv inflate.code._zcfree)).
  fold (zfuncs gv).
  forward_call tt. Intros wb.
  (* the (int) cast: windowBits is the signed value of the drawn u32 *)
  rewrite <- (Int.repr_signed (Int.repr wb)).
  pose proof (Int.signed_range (Int.repr wb)) as Hw.
  forget (Int.signed (Int.repr wb)) as w.
  (* gp_assume(inflate_window_ok(window_bits)): windowBits is in zlib.h's ranges, the ones inflateInit2_
     accepts (laws_session/Facts.inflate_window_valid_ok) *)
  forward_call (w).
  forward_call (if Zlib.proof.harness.laws_session.Spec.inflate_window_valid w then Int.one else Int.zero).
  { destruct (Zlib.proof.harness.laws_session.Spec.inflate_window_valid w); entailer!. }
  Intros.
  assert (WB: wbits_ok w = true).
  { rewrite <- Zlib.proof.harness.laws_session.Facts.inflate_window_valid_ok.
    destruct (Zlib.proof.harness.laws_session.Spec.inflate_window_valid w); [reflexivity | contradiction]. }
  forward_call (9223372036854775807). Intros len.
  forward_call (len, gv).
  Intros vret. destruct vret as [inp src]. simpl fst in *; simpl snd in *.
  match goal with H: Zlength src = len |- _ => subst len end.
  (* if (input == NULL) return 0 *)
  destruct (eq_dec inp nullval) as [PN|PN].
  { subst inp. forward_if; [ | contradiction]. forward. Exists (Int.repr 0). entailer!. }
  rewrite tok_adler_cs, bytes_adler_cs. Intros.
  forward_if; [contradiction | ].
  change (data_at_ Tsh (Tstruct _z_stream_s noattr) v_first) with (data_at_ Tsh t_z v_first).
  change (data_at_ Tsh (Tstruct _z_stream_s noattr) v_second) with (data_at_ Tsh t_z v_second).
  rewrite (strm_undef Tsh v_first), (strm_undef Tsh v_second).
  forward_call (v_first, Tsh, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef,
                Vundef, Vundef, Vundef, Vundef).
  forward_call (v_second, Tsh, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef,
                Vundef, Vundef, Vundef, Vundef).
  (* both streams are now the raw struct of zf_new *)
  pose proof (new_raw_c v_first zf_new) as Ea. pose proof (new_raw_c v_second zf_new) as Eb.
  unfold zf_new in Ea, Eb. cbn [zf_ni zf_ai zf_no zf_ao] in Ea, Eb. fold zf_new in Ea, Eb.
  rewrite <- Ea, <- Eb. clear Ea Eb.
  assert_PROP (isptr v_first) as Pa by (unfold new_raw; entailer!).
  assert_PROP (isptr v_second) as Pb by (unfold new_raw; entailer!).
  rewrite (new_raw_i gv v_first zf_new).
  (* the version literal at inflate's compspecs (replace_SEP: a `rewrite hversion` on the whole semax goal
     is slow) *)
  replace_SEP 9 (@data_at Zlib.units.Inflate.CS Ers (tarray tschar (Zlength hv_list)) hv_list
    (gv ___stringlit_api_inflate_deterministic_1)).
  { go_lower. rewrite hversion. apply derives_refl. }
  assert_PROP (isptr (gv ___stringlit_api_inflate_deterministic_1)) as Pver by entailer!.
  (* code_first = inflateInit2_(&first, w): Z_OK or Z_MEM_ERROR (w is accepted) *)
  forward_call (gv, Tsh, v_first, nr_raw zf_new, Vundef, Vundef, nullval, w,
                gv ___stringlit_api_inflate_deterministic_1, Ers, hv_list, 49, 112).
  { rewrite if_false by (intro; subst; contradiction). cancel. }
  { change (Zlength hv_list) with 6; repeat split; auto; rep_lia. }
  Intros vret. destruct vret as [aok sp]. simpl fst in *; simpl snd in *.
  assert (Hret: init_ret v_first 49 112 w aok = if aok then Z_OK else Z_MEM_ERROR).
  { unfold init_ret. simpl. rewrite if_false by (intro; subst; contradiction). rewrite WB.
    destruct aok; reflexivity. }
  rewrite Hret. clear Hret.
  (* code_second = inflateInit2_(&second, w), whatever the first returned *)
  rewrite (new_raw_i gv v_second zf_new).
  forward_call (gv, Tsh, v_second, nr_raw zf_new, Vundef, Vundef, nullval, w,
                gv ___stringlit_api_inflate_deterministic_1, Ers, hv_list, 49, 112).
  { rewrite if_false by (intro; subst; contradiction). cancel. }
  { change (Zlength hv_list) with 6; repeat split; auto; rep_lia. }
  Intros vret. destruct vret as [aok2 sp2]. simpl fst in *; simpl snd in *.
  assert (Hret: init_ret v_second 49 112 w aok2 = if aok2 then Z_OK else Z_MEM_ERROR).
  { unfold init_ret. simpl. rewrite if_false by (intro; subst; contradiction). rewrite WB.
    destruct aok2; reflexivity. }
  rewrite Hret. clear Hret.
  destruct aok, aok2; unfold init_mem; rewrite !if_false by (intro; subst; contradiction); simpl Z.eqb; cbv iota.
  2,3,4: (* a Z_MEM_ERROR: return 0 *)
    apply -> seq_assoc; apply -> seq_assoc; apply semax_if_seq; forward_if; [ first [top_infeas | forward] .. ];
    (forward_if; [ | top_infeas]); forward; Exists (Int.repr 0);
    repeat first [ sep_apply (live_raw_frame gv Tsh v_first) | sep_apply (live_raw_frame gv Tsh v_second)
                 | sep_apply (raw_frame gv Tsh v_first) | sep_apply (raw_frame gv Tsh v_second) ];
    entailer!.
  (* both Z_OK: the test of Z_MEM_ERROR fails, the assert holds *)
  apply -> seq_assoc. apply -> seq_assoc. apply semax_if_seq. forward_if; [top_infeas | ]. forward. forward_if; [top_infeas | ].
  repeat apply -> seq_assoc. apply semax_if_seq. forward_if; [ | top_infeas]. forward.
  forward_call (Int.repr 1).
  (* both streams are live: istreamA's with the model adler adl0 (the same for both streams: i_wrap of
     init_live does not depend on the state pointer) *)
  assert (Psa: isptr sp) by auto. assert (Psb: isptr sp2) by auto.
  set (La0 := init_live sp w) in *. set (Lb0 := init_live sp2 w) in *.
  assert_PROP (live_ok La0) as HLa by (unfold istream_raw; entailer!).
  assert_PROP (live_ok Lb0) as HLb by (unfold istream_raw; entailer!).
  set (adl0 := if w <? 0 then 0 else Z.land (i_wrap (l_s La0)) 1).
  assert (Hra: raw_live (Some La0) = (w <? 0)) by (apply init_raw; auto).
  assert (Hrb: raw_live (Some Lb0) = (w <? 0)) by (apply init_raw; auto).
  assert (Ha0: 0 <= adl0 <= Int64.max_unsigned).
  { unfold adl0. destruct (w <? 0); [rep_lia | pose proof (land1_range (i_wrap (l_s La0))); rep_lia]. }
  assert (Hwa: raw_live (Some La0) = false -> adl0 = Z.land (i_wrap (l_s La0)) 1).
  { intros X. rewrite Hra in X. unfold adl0. rewrite X. reflexivity. }
  assert (Hwb: raw_live (Some Lb0) = false -> adl0 = Z.land (i_wrap (l_s Lb0)) 1) by exact Hwa.
  assert (Zn: zf_ok zf_new) by (unfold zf_ok, zf_new; simpl; rep_lia).
  sep_apply (new_init gv v_first zf_new adl0 La0 Zn Ha0 Hwa).
  sep_apply (new_init gv v_second zf_new adl0 Lb0 Zn Ha0 Hwb).
  replace_SEP 2 (hversion_at ___stringlit_api_inflate_deterministic_1 gv).
  { go_lower. rewrite hversion. apply derives_refl. }
  forward. (* read = 0 *)
  assert_PROP (isptr inp) as Pinp by entailer!.
  assert (GF: g_facts J w inp src v_first v_second).
  { refine (conj AF (conj WB (conj Hw (conj _ (conj H3 (conj Pinp (conj Pa Pb))))))).
    change Int64.max_signed with 9223372036854775807. lia. }
  assert (Zi: zf_ok (zf_init zf_new adl0)) by (unfold zf_ok, zf_init, zf_new in *; simpl; rep_lia).
  forward_loop (dinv J gv v_first v_second w inp src)
    continue: (dinv J gv v_first v_second w inp src)
    break: (dinv J gv v_first v_second w inp src).
  - (* entry: position 0, both streams just initialized *)
    assert (DP: dprop J w src 0 (zf_init zf_new adl0) La0 (zf_init zf_new adl0) Lb0).
    { refine (conj _ (conj (df_init_swf _ AF w sp WB) (conj (df_init_swf _ AF w sp2 WB) (conj Hra Hrb)))).
      apply (df_init _ AF); auto. }
    unfold dinv, dinv_at. Exists 0 (zf_init zf_new adl0) La0 (zf_init zf_new adl0) Lb0.
    entailer!.
  - (* the do-while body *)
    unfold dinv. Intros pos za La zb Lb.
    unfold abbreviate in POSTCONDITION, MORE_COMMANDS. subst POSTCONDITION MORE_COMMANDS.
    apply (DB Espec J gv v_first v_second w inp src pos za La zb Lb GF).
  - (* the test nondet_u8() != 0 *)
    unfold dinv. Intros pos za La zb Lb. unfold dinv_at.
    forward_call tt. Intros c.
    forward_if.
    + forward. unfold dinv. Exists pos za La zb Lb. unfold dinv_at. entailer!.
    + forward. unfold dinv. Exists pos za La zb Lb. unfold dinv_at. entailer!.
  - (* after the do-while: return 0 *)
    unfold dinv. Intros pos za La zb Lb. unfold dinv_at. Intros.
    forward. Exists (Int.repr 0).
    sep_apply (a_frame gv v_first). sep_apply (a_frame gv v_second). entailer!.
Qed.

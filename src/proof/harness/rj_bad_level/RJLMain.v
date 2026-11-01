(* Law rj_bad_level: main of harness/rj_bad_level.c against main_core_spec R (statement in RJLMainStmt.v).
   main draws a level outside -1..9, the data and the output space, calls compress2 once and checks that it
   returns Z_STREAM_ERROR; compress2_spec_w's precondition (a model result for every allocation outcome) and
   the outcome come from RJLTheory. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.roundtrip.RTC2 Zlib.proof.roundtrip.RTCSpec Zlib.proof.roundtrip.RTCSpecW.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.rj_bad_level.RJLCS Zlib.proof.harness.rj_bad_level.RJLGlobals
               Zlib.proof.harness.rj_bad_level.RJLTheory Zlib.proof.harness.rj_bad_level.RJLMainStmt.
Require Import Zlib.harness.rj_bad_level.code.

(* Byte arrays, their malloc tokens and an unsigned long are the same at the units' compspecs (the byte helpers
   are specified at the adler32 unit's, compress2 at the compress unit's) and at the law's. *)
Lemma rjl_bytes_a sh n (c: list val) p:
  @data_at Zlib.units.Adler32.CS sh (tarray tuchar n) c p = @data_at CS sh (tarray tuchar n) c p.
Proof.
  erewrite (@data_at_change_composite _ _ CC_adler32 sh (tarray tuchar n)); [reflexivity | apply JMeq_refl | reflexivity].
Qed.

Lemma rjl_tok_a sh n p:
  @malloc_token Zlib.units.Adler32.CS sh (tarray tuchar n) p = @malloc_token CS sh (tarray tuchar n) p.
Proof. rewrite (@malloc_token_change_composite _ _ CC_adler32) by reflexivity. reflexivity. Qed.

Lemma rjl_bytes_c sh n (c: list val) p:
  @data_at Zlib.units.Compress.CS sh (tarray tuchar n) c p = @data_at CS sh (tarray tuchar n) c p.
Proof.
  erewrite (@data_at_change_composite _ _ CC_compress sh (tarray tuchar n)); [reflexivity | apply JMeq_refl | reflexivity].
Qed.

Lemma rjl_ulong_c sh (v: val) p:
  @data_at Zlib.units.Compress.CS sh tulong v p = @data_at CS sh tulong v p.
Proof.
  erewrite (@data_at_change_composite _ _ CC_compress sh tulong); [reflexivity | apply JMeq_refl | reflexivity].
Qed.

(* the move of the byte helpers' arguments from the law's compspecs to the adler32 unit's (forward_call
   looks for it) *)
#[local] Instance CC_to_adler32 : change_composite_env CS Zlib.units.Adler32.CS.
  make_cs_preserve CS Zlib.units.Adler32.CS. Defined.

(* q = any_bytes(len), as two steps: the call (its result in the temp t) and the assignment of t to the
   variable (a single forward_call stalls proving the type of the result, which is NULL or a pointer
   according to the if in the SEP) *)
Ltac rjl_new_bytes t len gv call :=
  repeat (apply -> seq_assoc);
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    eapply semax_seq' with
      (P' := EX q: val, EX bs: list Z,
             PROPx ((Zlength bs = len) :: is_bytes bs :: is_pointer_or_null q :: P)
             (LOCALx (temp t q :: Q)
             (SEPx ((if eq_dec q nullval then emp
                     else (malloc_token Ews (tarray tuchar len) q *
                           data_at Ews (tarray tuchar len) (bytes_rep bs) q)) :: R))))
  end;
  [ call; let v := fresh "v" in Intros v; rewrite ?rjl_bytes_a, ?rjl_tok_a;
    Exists (fst v) (snd v); destruct (eq_dec (fst v) nullval); entailer!
  | ].

(* forward_call's frame when the spec's SEP list is a definition [d] (RTCSpecW.c2w_sep_pre) *)
Ltac rjl_sep_cancel d :=
  unfold d;
  repeat (eapply syntactic_cancel_cons_succeed;
          [find_nth ecancel_local_tac | cbv iota; unfold delete_nth; cbv zeta iota ]);
  apply syntactic_cancel_nil.

(* compress2's precondition for a rejected level: the model result exists for every allocation outcome
   (RJLTheory.rjl_c2_exists) and destLen may be anything *)
Lemma rjl_c2w_pre level gv dp cap dlp sp src :
  ~ (-1 <= level <= 9) -> isptr dp -> isptr sp -> 0 <= cap <= Int64.max_unsigned ->
  Zlength src <= Int64.max_unsigned -> rbytes src -> rs32 level ->
  fold_right_and True (c2w_pre level gv dp (Zrepeat Vundef cap) cap dlp Ews sp src).
Proof.
  intros Hl Hd Hs Hc Hn Hb Hr. unfold c2w_pre. simpl. unfold Zrepeat. rewrite Zlength_repeat by lia.
  split; [exact Hd | ]. split; [reflexivity | ]. split; [lia | ]. split; [right; exact Hl | ].
  split; [auto | ]. split; [destruct sp; try contradiction; exact I | ]. split; [exact Hn | ]. split; [exact Hb | ]. split; [exact Hr | ].
  split; [ | exact I]. intros. apply rjl_c2_exists. exact Hl.
Qed.

Lemma body_main : rjl_main_stmt.
Proof.
  unfold rjl_main_stmt.
  start_function.
  unfold R. Intros.
  forward_call tt. Intros u.
  assert (Eu: Int.repr u = Int.repr (Int.signed (Int.repr u))) by (rewrite Int.repr_signed; auto).
  rewrite Eu. clear Eu. set (level := Int.signed (Int.repr u)).
  assert (Hlv: Int.min_signed <= level <= Int.max_signed) by apply Int.signed_range. clearbody level.
  (* gp_assume(level < -1 || level > 9) *)
  ifpost _t'2 (Int.repr (if ((level <? -1) || (9 <? level))%bool then 1 else 0)).
  { forward. entailer!. rewrite Int.signed_repr in H0 by rep_lia.
    destruct (Z.ltb_spec level (-1)); [reflexivity | lia]. }
  { forward. entailer!. rewrite Int.signed_repr in H0 by rep_lia.
    destruct (Z.ltb_spec level (-1)); [lia | ]. simpl. unfold Int.lt.
    destruct (zlt 9 level), (Z.ltb_spec 9 level); try lia; reflexivity. }
  forward_call (Int.repr (if ((level <? -1) || (9 <? level))%bool then 1 else 0)).
  assumed.
  assert (Hbad: ~ (-1 <= level <= 9)) by (apply orb_prop in E as [E | E]; [apply Z.ltb_lt in E | apply Z.ltb_lt in E]; lia).
  clear E.
  (* data_len = upto(PTRDIFF_MAX); capacity = upto(PTRDIFF_MAX) *)
  forward_call (Int64.max_signed). Intros n.
  forward_call (Int64.max_signed). Intros cap.
  (* data = any_bytes(data_len); compressed = malloc(capacity) *)
  rjl_new_bytes _t'5 n gv ltac:(forward_call (n, gv)).
  Intros data src. forward.
  forward_call (tarray tuchar cap, gv).
  { simpl. rewrite Z.max_r by lia. rep_lia. }
  Intros dp.
  (* if (data == NULL || compressed == NULL) return 0; *)
  destruct (eq_dec data nullval) as [PI | PI].
  { subst data.
    ifpost _t'7 (Int.repr 1).
    - forward. entailer!.
    - contradiction.
    - forward_if False; [ret0 | discriminate]. }
  Intros.
  destruct (eq_dec dp nullval) as [PO | PO].
  { subst dp.
    ifpost _t'7 (Int.repr 1).
    - congruence.
    - forward. entailer!.
    - forward_if False; [ret0 | discriminate]. }
  Intros.
  assert_PROP (isptr dp) as Pdp by entailer!.
  assert_PROP (isptr data) as Pdata by entailer!.
  ifpost _t'7 (Int.repr 0).
  { congruence. }
  { forward. entailer!. destruct dp; try contradiction; reflexivity. }
  forward_if True; [congruence | forward; entailer! | ].
  (* compressed_len = capacity; code = compress2(compressed, &compressed_len, data, data_len, level) *)
  forward.
  subst n.
  assert (Hrb: rbytes src) by (eapply Forall_impl; [ | exact H3]; simpl; intros; rep_lia).
  replace (data_at_ Ews (tarray tuchar cap) dp) with (data_at Ews (tarray tuchar cap) (Zrepeat Vundef cap) dp)
    by reflexivity.
  change (bytes_rep src) with (map Zlib.proof.deflate.Rep.vi src).
  rewrite <- (rjl_bytes_c Ews cap _ dp), <- (rjl_bytes_c Ews (Zlength src) _ data),
    <- (rjl_ulong_c Tsh _ v_compressed_len), <- (c2_src_obj Ews data src Pdata).
  forward_call (gv, dp, Zrepeat Vundef cap, cap, v_compressed_len, Ews, data, src, level).
  rjl_sep_cancel c2w_sep_pre.
  apply rjl_c2w_pre; [exact Hbad | exact Pdp | exact Pdata | rep_lia | rep_lia | exact Hrb | unfold rs32; rep_lia].
  unfold c2w_sep_post. simpl app.
  Intros vret. destruct vret as [[[[[[a1 a2] a3] a4] a5] r] out]. simpl fst in *; simpl snd in *.
  match goal with Hc: c2_res _ _ _ _ _ _ _ _ _ _ _ |- _ => apply rjl_c2_res in Hc; [subst r | exact Hbad] end.
  (* gp_assert(code == Z_STREAM_ERROR) *)
  forward_call (Int.repr 1).
  forward. Exists (Int.repr 0). entailer!.
Qed.

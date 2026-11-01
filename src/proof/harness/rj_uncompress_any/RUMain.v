(* Law rj_uncompress_any: the body of main (RUMainDefs.body_main_stmt), from UTheoryWAny.uw_any_stmt through
   [uw_any_main_stmt], the facts main uses. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.uncompr.USpecW.
Require Import Zlib.proof.uncompr.UTheoryWAny.
Require Import Zlib.proof.zutil.Libc.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.laws_common.CopyOfNull.
Require Import Zlib.proof.harness.rj_uncompress_any.RUCS.
Require Import Zlib.proof.harness.rj_uncompress_any.RUGlobals.
Require Import Zlib.proof.harness.rj_uncompress_any.RUMainDefs.
Require Import Zlib.harness.rj_uncompress_any.code.
#[local] Existing Instance Zlib.proof.harness.rj_uncompress_any.RUCS.CS.
Local Open Scope logic.

(* The theory as main uses it: on any input, a documented code, at most the output size reported written with no
   more bytes written than reported (out may be shorter than dlen: when inflateInit_ fails, nothing is written and
   destLen stays cap), and at most the input length reported read.  UTheoryWAny.uw_any_stmt implies it. *)
Definition uw_any_main_stmt : Prop :=
  forall (src: list Z) (cap r slen dlen: Z) (out: list Z),
    bytes_ok src -> Zlength src <= Int64.max_unsigned -> 0 <= cap <= Int64.max_unsigned ->
    uncompressw_rel src cap r slen dlen out ->
    (r = Z_OK \/ r = Z_MEM_ERROR \/ r = Z_BUF_ERROR \/ r = Z_DATA_ERROR) /\
    Zlength out <= dlen <= cap /\ 0 <= slen <= Zlength src.

Lemma uw_any_main : uw_any_stmt -> uw_any_main_stmt.
Proof.
  intros H src cap r slen dlen out B Ls C U.
  destruct (H src cap r slen dlen out B Ls C U) as [Hc Hr].
  split; [exact Hc | lia].
Qed.

(* Moves of byte arrays, malloc tokens and unsigned longs between the units' compspecs (uncompr.c's, where
   uncompress2 is specified, and adler32's, where the laws_common.h helpers are) and the law's. *)
Lemma ru_bytes_adler sh n (v: list val) q:
  @data_at Zlib.units.Adler32.CS sh (tarray tuchar n) v q = @data_at CS sh (tarray tuchar n) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_adler32); [apply JMeq_refl | reflexivity]. Qed.
Lemma ru_tok_adler sh n q:
  @malloc_token Zlib.units.Adler32.CS sh (tarray tuchar n) q = @malloc_token CS sh (tarray tuchar n) q.
Proof. apply equal_f; apply (@malloc_token_change_composite _ _ CC_adler32). reflexivity. Qed.
Lemma ru_bytes_uncompr sh n (v: list val) q:
  @data_at Zlib.units.Uncompr.CS sh (tarray tuchar n) v q = @data_at CS sh (tarray tuchar n) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_uncompr); [apply JMeq_refl | reflexivity]. Qed.
Lemma ru_tok_uncompr sh n q:
  @malloc_token Zlib.units.Uncompr.CS sh (tarray tuchar n) q = @malloc_token CS sh (tarray tuchar n) q.
Proof. apply equal_f; apply (@malloc_token_change_composite _ _ CC_uncompr). reflexivity. Qed.
Lemma ru_ulong_uncompr sh (v: val) q:
  @data_at Zlib.units.Uncompr.CS sh tulong v q = @data_at CS sh tulong v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_uncompr); [apply JMeq_refl | reflexivity]. Qed.

Ltac ru_law := repeat first [ rewrite ru_bytes_adler | rewrite ru_tok_adler | rewrite ru_bytes_uncompr
                            | rewrite ru_tok_uncompr | rewrite ru_ulong_uncompr ].

(* the globals as uncompress2 takes them (Spec5's inflate_globals) *)
Lemma ru_ig_to gv:
  tables_rep Ers gv * Zlib.proof.crc32.Spec.crc_table_at Ers gv * version_lit gv * zfuncs gv |-- inflate_globals Ers Ers gv.
Proof. unfold inflate_globals. cancel. Qed.

(* A result of alloc_any_bytes or copy_of, Z_NULL or not, under a flag (true: Z_NULL) *)
Lemma ru_if_null {A} (b: bool) (q: val) (x y: A) :
  (if b then q = nullval else q <> nullval) -> (if eq_dec q nullval then x else y) = (if b then x else y).
Proof. destruct b; intros H; [rewrite if_true | rewrite if_false]; auto. Qed.

Lemma ru_if_split (b: bool) (P Q: mpred) :
  (if b then emp else P * Q) = (if b then emp else P) * (if b then emp else Q).
Proof. destruct b; [rewrite emp_sepcon | ]; reflexivity. Qed.

(* the output space and the input as uncompress2 takes them (USpecN.dest_rep, USpecW.src_rep) *)
Lemma ru_dest_in (dnull: bool) (q: val) (cap: Z) (dc: list val) :
  (if dnull then emp else malloc_token Ews (tarray tuchar cap) q) *
  (if dnull then emp else data_at Ews (tarray tuchar cap) dc q) =
  dest_rep dnull Ews q cap dc (negb dnull).
Proof.
  unfold dest_rep. destruct dnull; simpl; [apply emp_sepcon | ].
  rewrite ru_bytes_uncompr, ru_tok_uncompr. apply sepcon_comm.
Qed.

Lemma ru_src_in (snull: bool) (q: val) (n: Z) (sc: list val) :
  (if snull then emp else malloc_token Ews (tarray tuchar n) q * data_at Ews (tarray tuchar n) sc q) =
  src_rep snull Ews q n sc (negb snull).
Proof.
  unfold src_rep. destruct snull; simpl; [reflexivity | ].
  rewrite ru_bytes_uncompr, ru_tok_uncompr. apply sepcon_comm.
Qed.

Lemma ru_int_eq a b: Int.min_signed <= a <= Int.max_signed -> Int.min_signed <= b <= Int.max_signed ->
  Int.eq (Int.repr a) (Int.repr b) = (a =? b).
Proof.
  intros A B. destruct (Z.eqb_spec a b).
  - subst. apply Int.eq_true.
  - apply Int.eq_false. intro E. apply repr_inj_signed in E; auto.
Qed.

Lemma ru_cmpu_le a b: 0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned ->
  Int64.cmpu Cle (Int64.repr a) (Int64.repr b) = (a <=? b).
Proof.
  intros A B. unfold Int64.cmpu, Int64.ltu. rewrite !Int64.unsigned_repr by lia.
  destruct (zlt b a), (Z.leb_spec a b); simpl; reflexivity || lia.
Qed.

(* the tests `x > 0` on an unsigned long, and the value of an int test *)
Lemma ru_gt0 a: 0 <= a <= Int64.max_unsigned ->
  bool2val (Int64.cmpu Cgt (Int64.repr a) (Int64.repr 0)) = Vint (Int.repr (if 0 <? a then 1 else 0)).
Proof.
  intros A. unfold Int64.cmpu, Int64.ltu. rewrite !Int64.unsigned_repr by rep_lia.
  destruct (zlt 0 a), (Z.ltb_spec 0 a); try lia; reflexivity.
Qed.

Lemma ru_true (b: bool): Int.repr (if b then 1 else 0) <> Int.zero -> b = true.
Proof. destruct b; [auto | intros H; contradiction H; reflexivity]. Qed.

Lemma ru_false (b: bool): Int.repr (if b then 1 else 0) = Int.zero -> b = false.
Proof. destruct b; [intros H; discriminate H | auto]. Qed.

Ltac ru_tf E := match goal with
  | H: Int.repr (if ?b then 1 else 0) <> Int.zero |- _ => apply ru_true in H; rename H into E
  | H: Int.repr (if ?b then 1 else 0) = Int.zero |- _ => apply ru_false in H; rename H into E
  end.

(* out's bytes from what uncompress2 reports written on are the original ones *)
Lemma ru_dest_tail bs cap out dlen: Zlength out <= dlen <= cap -> Zlength bs = cap ->
  sublist dlen cap (dest_after (bytes_rep bs) cap out) = bytes_rep (sublist dlen cap bs).
Proof.
  intros D B. unfold dest_after, byte_vals, bytes_rep. list_solve.
Qed.

(* VST's after_forward_call simplifies remove_localdef_temp with `simpl rlt_ident_eq`, which runs away on main's
   identifiers (_source against _source_len); each identifier comparison is decided by vm_compute instead. *)
Ltac ru_rlt_fix u :=
  lazymatch u with
  | context C [rlt_ident_eq ?a ?b] =>
      let v := eval vm_compute in (rlt_ident_eq a b) in
      let u2 := context C [v] in ru_rlt_fix u2
  | _ => u
  end.

Ltac simplify_remove_localdef_temp ::=
  match goal with |- context [remove_localdef_temp ?i ?L] =>
    let u := constr:(remove_localdef_temp i L) in
    let u' := eval lazy delta [remove_localdef_temp] beta iota in u in
    let u' := ru_rlt_fix u' in
    let u' := eval lazy beta iota in u' in
    let u' := eval lazy zeta in u' in
    change u with u'
  end.

(* the int tests on uncompress2's code *)
Ltac ru_dz := repeat match goal with
  | H: Int.repr ?a = Int.repr ?b |- _ => apply repr_inj_signed in H; [ | rep_lia | rep_lia]
  | H: Int.repr ?a <> Int.repr ?b |- _ =>
      let E := fresh in assert (E: a <> b) by (intro; subst; apply H; reflexivity); clear H
  | |- context [Int.eq (Int.repr ?a) (Int.repr ?b)] => rewrite (ru_int_eq a b) by rep_lia
  | H: context [Z.eqb ?a ?b] |- _ => destruct (Z.eqb_spec a b)
  | |- context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b)
  end; simpl in *; try reflexivity; try lia;
  try (exfalso; match goal with H: Int.repr 1 = Int.zero |- _ => apply Int.one_not_zero; exact H
                              | H: Int.repr 0 <> Int.zero |- _ => apply H; reflexivity
                              | H: Int.zero <> Int.zero |- _ => apply H; reflexivity
                              | H: Int.one = Int.zero |- _ => apply Int.one_not_zero; exact H end).

(* `if (len > 0 || null_if_empty == 0) p = alloc_any_bytes(len);` with p Z_NULL before: after it, p is Z_NULL or
   an object of len bytes, as alloc_any_bytes returns it (Z_NULL is an empty list of bytes of length 0). *)
Ltac ru_alloc_if p n := match goal with |- semax _ (PROPx _ (LOCALx (temp _ _ :: temp p _ :: ?Q) (SEPx ?R))) _ _ =>
  forward_if (EX q: val, EX bs: list Z,
    PROPx [Zlength bs = n; is_bytes bs] (LOCALx (temp p q :: Q)
      (SEPx ((if eq_dec q nullval then emp
              else (malloc_token Ews (tarray tuchar n) q * data_at Ews (tarray tuchar n) (bytes_rep bs) q)) :: R))))
  end.

(* main: the source and the output space are Z_NULL (not allocated: null_if_empty with length 0, or
   alloc_any_bytes failed) or objects with their malloc tokens (flags snull, dnull; Z_NULL only with length 0, else
   main returns); the copy decompressed_copy (flag bnull: Z_NULL only with decompressed_size 0) of decompressed;
   uncompress2 through USpecW.uncompress2_spec_w; the asserts from uw_any_main_stmt, the last one
   (decompressed_size > 0) from ru_dest_tail: decompressed and decompressed_copy agree from decompressed_len on. *)
Lemma body_main_of : uw_any_main_stmt -> semax_body (QPvarspecs p) Gmain f_main (_main, main_core_spec R).
Proof.
  intros UF.
  start_function.
  unfold R, Zlib.proof.harness.uncompress_any.UAGlobals.R. Intros.
  make_func_ptr Zlib.inflate.code._zcalloc. make_func_ptr Zlib.inflate.code._zcfree.
  gather_SEP (func_ptr' _ (gv Zlib.inflate.code._zcalloc)) (func_ptr' _ (gv Zlib.inflate.code._zcfree)).
  fold (zfuncs gv).
  forward_call 9223372036854775807. Intros n.
  forward_call 9223372036854775807. Intros cap.
  forward_call 1. Intros ne.
  (* source = Z_NULL; if (source_len > 0 || null_if_empty == 0) source = alloc_any_bytes(source_len); *)
  forward.
  change (Vlong (Int64.repr (Int.signed (Int.repr 0)))) with nullval.
  ifpost _t'5 (Int.repr (if ((0 <? n) || (ne =? 0))%bool then 1 else 0)).
  { rewrite !Int64.unsigned_repr in * by rep_lia. forward. entailer!.
    destruct (Z.ltb_spec 0 n); [reflexivity | lia]. }
  { rewrite !Int64.unsigned_repr in * by rep_lia. forward. entailer!.
    destruct (Z.ltb_spec 0 n); [lia | ]. assert (ne = 0 \/ ne = 1) as [-> | ->] by lia; reflexivity. }
  ru_alloc_if _source n.
  { forward_call (n, gv). Intros vret. destruct vret as [q bs]. simpl fst in *; simpl snd in *. ru_law.
    forward. Exists q bs. entailer!. }
  { ru_tf E. apply orb_false_iff in E. destruct E as [E1 _]. apply Z.ltb_ge in E1.
    forward. Exists nullval (@nil Z). entailer!. split; [rewrite Zlength_nil; lia | apply Forall_nil]. }
  Intros inp src.
  (* the same for decompressed and decompressed_size *)
  forward.
  change (Vlong (Int64.repr (Int.signed (Int.repr 0)))) with nullval.
  ifpost _t'7 (Int.repr (if ((0 <? cap) || (ne =? 0))%bool then 1 else 0)).
  { rewrite !Int64.unsigned_repr in * by rep_lia. forward. entailer!.
    destruct (Z.ltb_spec 0 cap); [reflexivity | lia]. }
  { rewrite !Int64.unsigned_repr in * by rep_lia. forward. entailer!.
    destruct (Z.ltb_spec 0 cap); [lia | ]. assert (ne = 0 \/ ne = 1) as [-> | ->] by lia; reflexivity. }
  ru_alloc_if _decompressed cap.
  { forward_call (cap, gv). Intros vret. destruct vret as [q bs]. simpl fst in *; simpl snd in *. ru_law.
    forward. Exists q bs. entailer!. }
  { ru_tf E. apply orb_false_iff in E. destruct E as [E1 _]. apply Z.ltb_ge in E1.
    forward. Exists nullval (@nil Z). entailer!. split; [rewrite Zlength_nil; lia | apply Forall_nil]. }
  Intros outp ob. subst n cap.
  (* source and decompressed: Z_NULL (flags snull, dnull) or objects *)
  assert (Hs: exists snull: bool, if snull then inp = nullval else inp <> nullval)
    by (destruct (eq_dec inp nullval); [exists true | exists false]; auto).
  destruct Hs as [snull Hs]. rewrite (ru_if_null snull inp) by exact Hs.
  assert (Hd: exists dnull: bool, if dnull then outp = nullval else outp <> nullval)
    by (destruct (eq_dec outp nullval); [exists true | exists false]; auto).
  destruct Hd as [dnull Hd]. rewrite (ru_if_null dnull outp) by exact Hd.
  (* if ((source == NULL && source_len > 0) || (decompressed == NULL && decompressed_size > 0)) return 0; *)
  ifpost _t'8 (Int.repr (if (snull && (0 <? Zlength src))%bool then 1 else 0)).
  { destruct snull.
    - subst inp. entailer!.
    - eapply (@malloc_test_eq CS _ (Zlength src)); [lia | ].
      sep_apply (data_at_data_at_ Ews (tarray tuchar (Zlength src)) (bytes_rep src) inp). cancel. }
  { destruct snull; [ | congruence]. forward. entailer!. rewrite ru_gt0 by rep_lia. reflexivity. }
  { forward. destruct snull; [congruence | ]. entailer!. }
  ifpost _t'9 (Int.repr (if ((snull && (0 <? Zlength src)) || (dnull && (0 <? Zlength ob)))%bool then 1 else 0)).
  { ru_tf E. forward. entailer!. rewrite E. reflexivity. }
  { ru_tf E. rewrite E. simpl orb.
    forward_if.
    { destruct dnull.
      - subst outp. entailer!.
      - eapply (@malloc_test_eq CS _ (Zlength ob)); [lia | ].
        sep_apply (data_at_data_at_ Ews (tarray tuchar (Zlength ob)) (bytes_rep ob) outp). cancel. }
    { destruct dnull; [ | congruence]. forward. forward. entailer!. rewrite ru_gt0 by rep_lia.
      rewrite E. simpl. destruct (0 <? Zlength ob); split; reflexivity. }
    { forward. destruct dnull; [congruence | ]. entailer!. rewrite E. split; reflexivity. } }
  forward_if.
  { ret0. }
  ru_tf E. apply orb_false_iff in E. destruct E as [E1 E2].
  assert (Hsn: snull = true -> src = []).
  { intros ->. simpl in E1. apply Z.ltb_ge in E1. apply Zlength_nil_inv. pose proof (Zlength_nonneg src). lia. }
  assert (Hdn: dnull = true -> ob = []).
  { intros ->. simpl in E2. apply Z.ltb_ge in E2. apply Zlength_nil_inv. pose proof (Zlength_nonneg ob). lia. }
  clear E1 E2.
  (* decompressed_copy = copy_of(decompressed, decompressed_size) *)
  assert_PROP (dnull = false -> isptr outp) as Po by (destruct dnull; entailer!).
  assert_PROP (snull = false -> isptr inp) as Pi by (destruct snull; entailer!).
  rewrite (ru_if_split dnull). Intros.
  rewrite <- (ru_bytes_adler Ews (Zlength ob) (bytes_rep ob) outp).
  forward_call (dnull, outp, Ews, outp, 0, Zlength ob, bytes_rep ob, Zlength ob, ob, gv).
  { destruct dnull.
    - rewrite (Hdn eq_refl). auto.
    - unfold cbuf_ok. rewrite isptr_offset_val_zero by exact (Po eq_refl).
      unfold bytes_rep. repeat split; auto; try rep_lia; try list_solve. }
  Intros q. ru_law.
  (* if (decompressed_copy == NULL && decompressed_size > 0) return 0; *)
  assert (Hb: exists bnull: bool, if bnull then q = nullval else q <> nullval)
    by (destruct (eq_dec q nullval); [exists true | exists false]; auto).
  destruct Hb as [bnull Hb]. rewrite (ru_if_null bnull q) by exact Hb.
  ifpost _t'11 (Int.repr (if (bnull && (0 <? Zlength ob))%bool then 1 else 0)).
  { destruct bnull.
    - subst q. entailer!.
    - eapply (@malloc_test_eq CS _ (Zlength ob)); [lia | ].
      sep_apply (data_at_data_at_ Ews (tarray tuchar (Zlength ob)) (bytes_rep ob) q). cancel. }
  { destruct bnull; [ | congruence]. forward. entailer!. rewrite ru_gt0 by rep_lia. reflexivity. }
  { forward. destruct bnull; [congruence | ]. entailer!. }
  forward_if.
  { ret0. }
  ru_tf E. assert (Hbn: bnull = true -> Zlength ob = 0).
  { intros ->. simpl in E. apply Z.ltb_ge in E. pose proof (Zlength_nonneg ob). lia. }
  clear E.
  (* decompressed_len = decompressed_size; source_consumed_len = source_len;
     code = uncompress2(decompressed, &decompressed_len, source, &source_consumed_len); *)
  forward. forward.
  gather_SEP (if dnull then emp else malloc_token _ _ outp) (if dnull then emp else data_at _ _ _ outp).
  rewrite (ru_dest_in dnull outp), (ru_src_in snull inp).
  rewrite <- (ru_ulong_uncompr Tsh _ v_decompressed_len), <- (ru_ulong_uncompr Tsh _ v_source_consumed_len).
  sep_apply (ru_ig_to gv).
  forward_call (gv, dnull, Ews, outp, Zlength ob, bytes_rep ob, Zlength ob, v_decompressed_len, negb dnull,
                snull, negb snull, Ews, inp, Zlength src, bytes_rep src, src, v_source_consumed_len, Ers, Ers).
  { split.
    - unfold dest_ok_w. destruct dnull.
      + rewrite (Hdn eq_refl). repeat split; auto.
      + pose proof (Po eq_refl). unfold bytes_rep.
        split; [apply writable_Ews | repeat split; auto; try rep_lia; try list_solve].
    - unfold src_ok_w. destruct snull.
      + rewrite (Hsn eq_refl). repeat split; auto.
      + pose proof (Pi eq_refl). unfold bytes_rep, byte_vals.
        repeat split; auto; try rep_lia; try list_solve. }
  Intros vret. destruct vret as [[[r slen] dlen] out]. simpl fst in *; simpl snd in *.
  match goal with H: uncompressw_rel _ _ _ _ _ _ |- _ => rename H into Hrel end.
  destruct (UF src (Zlength ob) r slen dlen out ltac:(assumption) ltac:(rep_lia) ltac:(rep_lia) Hrel) as (Hr & Hdl & Hsl).
  assert (Rr: -5 <= r <= 0) by (unfold Z_OK, Z_MEM_ERROR, Z_BUF_ERROR, Z_DATA_ERROR in Hr; lia).
  ru_law.
  (* gp_assert(code == Z_OK || code == Z_MEM_ERROR || code == Z_BUF_ERROR || code == Z_DATA_ERROR); *)
  ifpost _t'13 (Int.repr (if ((r =? 0) || (r =? -4))%bool then 1 else 0)).
  { forward. entailer!; ru_dz. }
  { forward. entailer!; ru_dz. }
  ifpost _t'14 (Int.repr (if ((r =? 0) || (r =? -4) || (r =? -5))%bool then 1 else 0)).
  { forward. entailer!; ru_dz. }
  { forward. entailer!; ru_dz. }
  ifpost _t'15 (Int.repr (if ((r =? 0) || (r =? -4) || (r =? -5) || (r =? -3))%bool then 1 else 0)).
  { forward. entailer!; ru_dz. }
  { forward. entailer!; ru_dz. }
  forward_call (Int.repr (if ((r =? 0) || (r =? -4) || (r =? -5) || (r =? -3))%bool then 1 else 0)).
  { unfold Z_OK, Z_MEM_ERROR, Z_BUF_ERROR, Z_DATA_ERROR in Hr. ru_dz. }
  (* gp_assert(decompressed_len <= decompressed_size && source_consumed_len <= source_len); *)
  forward.
  ifpost _t'16 (Int.repr 1).
  { forward. forward. entailer!. rewrite ru_cmpu_le by rep_lia.
    destruct (Z.leb_spec slen (Zlength src)); [reflexivity | lia]. }
  { lia. }
  forward_call (Int.repr 1).
  (* if (decompressed_size > 0) gp_assert(bytes_eq(decompressed + decompressed_len,
                                                   decompressed_copy + decompressed_len, ...)); *)
  forward_if (PROP () LOCAL (lvar _source_consumed_len tulong v_source_consumed_len; lvar _decompressed_len tulong v_decompressed_len; gvars gv)
              SEP (data_at Tsh tulong (Vlong (Int64.repr dlen)) v_decompressed_len;
                   data_at Tsh tulong (Vlong (Int64.repr slen)) v_source_consumed_len; TT)).
  { match goal with H: Int64.unsigned _ < Int64.unsigned _ |- _ => rename H into Hgt end.
    rewrite !Int64.unsigned_repr in Hgt by rep_lia.
    (* decompressed_size > 0: decompressed and decompressed_copy are objects *)
    destruct dnull; [rewrite (Hdn eq_refl) in Hgt; rewrite Zlength_nil in Hgt; lia | ].
    destruct bnull; [pose proof (Hbn eq_refl); lia | ].
    pose proof (Po eq_refl) as Pout.
    unfold dest_rep. cbn [negb]. Intros. ru_law.
    assert_PROP (isptr q) as Pq by entailer!.
    forward. forward. forward.
    rewrite <- (ru_bytes_adler Ews (Zlength ob) (dest_after (bytes_rep ob) (Zlength ob) out) outp),
            <- (ru_bytes_adler Ews (Zlength ob) (bytes_rep ob) q).
    forward_call (offset_val dlen outp, Ews, outp, dlen, Zlength ob, dest_after (bytes_rep ob) (Zlength ob) out,
                  sublist dlen (Zlength ob) ob, offset_val dlen q, Ews, q, dlen, Zlength ob, bytes_rep ob,
                  sublist dlen (Zlength ob) ob, Zlength ob - dlen).
    { pose proof (Zlength_nonneg out). unfold cbuf_ok. replace (dlen + (Zlength ob - dlen)) with (Zlength ob) by lia.
      assert (is_bytes (sublist dlen (Zlength ob) ob)) by (apply Forall_sublist; auto).
      rewrite ru_dest_tail by lia. unfold bytes_rep. rewrite sublist_map.
      repeat split; auto with share; try lia; try (rewrite Zlength_sublist by lia; lia). }
    destruct (list_eq_dec Z.eq_dec (sublist dlen (Zlength ob) ob) (sublist dlen (Zlength ob) ob));
      [ | contradiction].
    forward_call (Int.repr 1).
    entailer!. }
  { forward. entailer!. }
  forward. Exists (Int.repr 0). entailer!.
Qed.

Lemma body_main : body_main_stmt.
Proof. intros H. exact (body_main_of (uw_any_main H)). Qed.

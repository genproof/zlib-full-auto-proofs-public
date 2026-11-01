(* Law inflate_buffers, main: the statements after the dispatch (seg_checks): the checks of avail_in/out,
   next_in/out, the input and the untouched output (bytes_same), the totals; pos += used; the three free()s;
   `if (stop == 0) break`. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.inflate_common.HarnessLib.
Require Import Zlib.proof.harness.inflate_buffers.IBLawCS Zlib.proof.harness.inflate_buffers.IBGlobals
               Zlib.proof.harness.inflate_buffers.IBFacts Zlib.proof.harness.inflate_buffers.IBMainKit.
Require Import Zlib.harness.x_inflate_buffers.code.
Require Import Zlib.proof.crc32.Spec.

Section TestEq.
Local Transparent denote_tc_test_eq.
(* ib + used == ib + used (within or one past a malloc'd byte object, also of 0 bytes) *)
Lemma ibc_test_eq_self {cs: compspecs} P n k q:
  0 <= k <= n ->
  P |-- (malloc_token Ews (tarray tuchar n) q * data_at_ Ews (tarray tuchar n) q * TT)%logic ->
  P |-- denote_tc_test_eq (offset_val k q) (offset_val k q).
Proof.
  intros Hk H. eapply derives_trans; [exact H | ].
  assert_PROP (isptr q) as Hq by (saturate_local; entailer!).
  destruct q; try contradiction.
  assert (W: (malloc_token Ews (tarray tuchar n) (Vptr b i) * data_at_ Ews (tarray tuchar n) (Vptr b i) * TT)%logic
             |-- weak_valid_pointer (offset_val k (Vptr b i))).
  { apply sepcon_weak_valid_pointer1.
    destruct (zlt 0 n).
    - apply sepcon_weak_valid_pointer2. rewrite data_at__memory_block. normalize.
      simpl sizeof. rewrite Z.max_r by lia. rewrite Z.mul_1_l.
      apply memory_block_weak_valid_pointer; auto; lia.
    - assert (n = 0) by lia. assert (k = 0) by lia. subst.
      apply sepcon_weak_valid_pointer1.
      eapply derives_trans; [apply malloc_token_valid_pointer; simpl; lia | ].
      replace (offset_val 0 (Vptr b i)) with (Vptr b i) by (simpl; rewrite ptrofs_add_repr_0_r; auto).
      apply valid_pointer_weak. }
  simpl offset_val in *. unfold denote_tc_test_eq, test_eq_ptrs, sameblock.
  destruct (peq b b) as [E | X]; [ | contradiction]. simpl.
  apply andp_right; exact W.
Qed.

Lemma ibc_test_eq_null P: P |-- denote_tc_test_eq nullval (Vlong (Int64.repr 0)).
Proof. unfold denote_tc_test_eq, nullval. cbv [Archi.ptr64]. apply andp_right; apply prop_right; reflexivity. Qed.
End TestEq.

Lemma ibc_cbuf0 sh p data n: readable_share sh -> isptr p -> is_bytes data -> Zlength data = n ->
  cbuf_ok false p sh p 0 n n (bytes_rep data) data.
Proof.
  intros Hsh Hp Hb Hn. pose proof (Zlength_nonneg data). pose proof (Zlib.proof.adler32.Ptr.cbuf_ok_prefix sh p data n Hsh Hp Hb ltac:(lia) ltac:(lia)) as X.
  rewrite sublist_same in X by lia. subst n. exact X.
Qed.

Lemma ibc_cbuf sh p data n lo: readable_share sh -> isptr p -> is_bytes data -> Zlength data = n -> 0 <= lo <= n ->
  cbuf_ok false (offset_val lo p) sh p lo n (n - lo) (bytes_rep data) (sublist lo n data).
Proof.
  intros Hsh Hp Hb Hn Hlo. pose proof (Zlib.proof.adler32.Ptr.cbuf_ok_slice sh p data lo (n - lo) Hsh Hp Hb ltac:(lia) ltac:(lia) ltac:(lia)) as X.
  replace (lo + (n - lo)) with n in X by lia. subst n. exact X.
Qed.

Lemma ibc_u64 x: Int64.repr (Zlib.proof.inflate.Model.u64 x) = Int64.repr x.
Proof.
  unfold Zlib.proof.inflate.Model.u64. change (2 ^ 64) with Int64.modulus.
  rewrite <- Int64.unsigned_repr_eq. apply Int64.repr_unsigned.
Qed.

Lemma seg_checks_ok {Espec: OracleKind} gv vs vosn vdl srcp src pos aout flush arg op innull outnull stop ain
    ibp obp q bs z L Fr r reset z' L' obl snl :
  ops_hyps srcp src pos aout flush arg op innull outnull stop ain ibp obp q bs L -> zf_ok z ->
  semax Delta_m
    (ops_post_at gv vs vosn vdl srcp src pos aout flush arg op innull outnull stop ain ibp obp q z Fr
       r reset z' L' obl snl)
    seg_checks
    (loop_nocontinue_ret_assert (ib_loop_inv gv vs vosn vdl srcp src Fr)
       (overridePost (ib_loop_inv gv vs vosn vdl srcp src Fr) POST_m)).
Proof.
  intros H ZO.
  destruct H as (FI & HI & Hpos & Hain & Hpa & Hsrc & Hsb & Haout & Hbsl & Hbsb & Hfl & Harg & Hopr & Hin & Hout & Hst & Psrc & Pib & Pob & Pq).
  unfold ops_post_at, ops_locals.
  Intros.
  rewrite ib_istream_unfold. Intros.
  match goal with H: ops_out _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => rename H into OUT end.
  unfold seg_checks, Delta_m, Gmain_k. simplify_func_tycontext. abbreviate_semax.
  unfold ib_tup.
  destruct OUT as (Hr & Hreset & Hai & Hao & Eni & Hnin & Eno & Hnout & Hobl & Hsnl & Hoblb & Hsnlb & Hsub & Hrs1 & Hrs0).
  forward.
  forward_call (Int.repr 1).
  { entailer!. simpl. unfold Int.ltu. rewrite !Int.unsigned_repr by rep_lia. destruct (zlt _ _); [lia | reflexivity]. }
  forward.
  forward_call (Int.repr 1).
  { entailer!. simpl. unfold Int.ltu. rewrite !Int.unsigned_repr by rep_lia. destruct (zlt _ _); [lia | reflexivity]. }
  forward. forward. forward. forward.
  rewrite !sub_repr.
  set (used := ain - zf_ai z') in *. set (made := aout - zf_ao z') in *.
  assert (Hused: 0 <= used <= ain) by (unfold used; lia). assert (Hmade: 0 <= made <= aout) by (unfold made; lia).
  clearbody used made.
  ifsame.
  { assert (NIN: ib_nin op innull = true) by (destruct (ib_nin op innull); [reflexivity | hl_absurd]).
    rewrite NIN in Eni, Hnin. specialize (Hnin eq_refl).
    forward. { entailer!. rewrite Eni. hnf; auto. }
    rewrite Eni. forward_call (Int.repr 1).
    forward_call (Int.repr 1).
    { entailer!. }
    rewrite Eni. unfold loop_nocontinue_ret_assert; simpl RA_normal. entailer!. }
  { assert (NIN: ib_nin op innull = false) by (destruct (ib_nin op innull); [hl_absurd | reflexivity]).
    rewrite NIN in Eni.
    forward. { entailer!. rewrite Eni. destruct ibp; try contradiction. hnf; auto. }
    rewrite Eni. forward_call (Int.repr 1).
    { apply (ibc_test_eq_self _ ain); [lia | ].
      sep_apply (data_at_data_at_ Ews (tarray tuchar ain) (bytes_rep (sublist pos (pos + ain) src)) ibp). cancel. }
    rewrite Eni. unfold loop_nocontinue_ret_assert; simpl RA_normal. entailer!. }
  ifsame.
  { assert (NOUT: ib_nout op outnull = true) by (destruct (ib_nout op outnull); [reflexivity | hl_absurd]).
    rewrite NOUT in Eno, Hnout. specialize (Hnout eq_refl).
    forward. { entailer!. rewrite Eno. hnf; auto. }
    rewrite Eno. forward_call (Int.repr 1).
    forward_call (Int.repr 1).
    { entailer!. }
    rewrite Eno. unfold loop_nocontinue_ret_assert; simpl RA_normal. entailer!. }
  { assert (NOUT: ib_nout op outnull = false) by (destruct (ib_nout op outnull); [hl_absurd | reflexivity]).
    rewrite NOUT in Eno.
    forward. { entailer!. rewrite Eno. destruct obp; try contradiction. hnf; auto. }
    rewrite Eno. forward_call (Int.repr 1).
    { match goal with |- context [data_at Ews (tarray tuchar ?n) (bytes_rep obl) obp] =>
        apply (ibc_test_eq_self _ n); [lia | ];
        sep_apply (data_at_data_at_ Ews (tarray tuchar n) (bytes_rep obl) obp); cancel end. }
    rewrite Eno. unfold loop_nocontinue_ret_assert; simpl RA_normal. entailer!. }
  set (D := sublist pos (pos + ain) src).
  assert (HD: Zlength D = ain) by (unfold D; rewrite Zlength_sublist; lia).
  assert (HDb: is_bytes D) by (unfold D; apply is_bytes_sublist; auto).
  forward_call (ibp, Ews, ibp, 0, ain, bytes_rep D, D,
                offset_val pos srcp, Ews, srcp, pos, Zlength src, bytes_rep src, D, ain).
  { rewrite !bytes_adler_cs. cancel. }
  { split; [apply ibc_cbuf0; auto | ].
    unfold D. apply Zlib.proof.adler32.Ptr.cbuf_ok_slice; auto; lia. }
  rewrite if_true by reflexivity.
  rewrite !bytes_adler_cs.
  forward_call (Int.repr 1).
  forward.
  forward_call (offset_val made obp, Ews, obp, made, aout, bytes_rep obl, sublist made aout obl,
                offset_val made q, Ews, q, made, aout, bytes_rep snl, sublist made aout snl, aout - made).
  { rewrite !bytes_adler_cs. cancel. }
  { split; apply ibc_cbuf; auto; lia. }
  rewrite Hsub, if_true by reflexivity.
  rewrite !bytes_adler_cs.
  forward_call (Int.repr 1).
  ifsame.
  { assert (R1: reset = 1) by (destruct Hreset as [-> | ->]; [hl_absurd | reflexivity]).
    destruct (Hrs1 R1) as [T0 O0].
    forward.
    ifpost _t'48 (Int.repr 1).
    { forward. forward. rewrite O0. entailer!. }
    { exfalso. rewrite T0 in *. contradiction. }
    forward_call (Int.repr 1).
    unfold loop_nocontinue_ret_assert; simpl RA_normal. entailer!. }
  { assert (R0: reset = 0) by (destruct Hreset as [-> | ->]; [reflexivity | hl_absurd]).
    ifpost _t'49 (Int.repr (if ((op <? 200) && (r =? -4))%bool then 1 else 0)).
    { forward. entailer!. rewrite hl_int_eq by rep_lia. cbn [Z.opp].
      destruct (Z.ltb_spec op 200); [ | lia]. simpl andb. destruct (r =? -4); reflexivity. }
    { forward. entailer!. destruct (Z.ltb_spec op 200); [lia | ]. reflexivity. }
    destruct ((op <? 200) && (r =? -4))%bool eqn:B.
    { ifsame.
      { hl_absurd. }
      { forward. entailer!. }
      unfold loop_nocontinue_ret_assert; simpl RA_normal. entailer!. }
    change Z_MEM_ERROR with (-4) in Hrs0. destruct (Hrs0 R0 B) as [T O].
    ifsame.
    { forward.
      forward_call (Int.repr 1).
      { entailer!. rewrite T, ibc_u64, Int64.eq_true. reflexivity. }
      forward.
      forward_call (Int.repr 1).
      { entailer!. rewrite O, ibc_u64, Int64.eq_true. reflexivity. }
      unfold loop_nocontinue_ret_assert; simpl RA_normal. entailer!. }
    { forward. entailer!. }
    unfold loop_nocontinue_ret_assert; simpl RA_normal. entailer!. }
  forward.
  rewrite add_repr.
  ifsame.
  { forward. unfold loop_nocontinue_ret_assert; simpl RA_normal. entailer!. }
  { forward. unfold loop_nocontinue_ret_assert; simpl RA_normal. entailer!. }
  forward_call (tarray tuchar ain, ibp, gv).
  { rewrite if_false by (destruct ibp; try contradiction; discriminate).
    sep_apply (data_at_data_at_ Ews (tarray tuchar ain) (bytes_rep D) ibp). cancel. }
  forward_call (tarray tuchar aout, obp, gv).
  { rewrite if_false by (destruct obp; try contradiction; discriminate).
    sep_apply (data_at_data_at_ Ews (tarray tuchar aout) (bytes_rep obl) obp). cancel. }
  forward.
  forward_call (tarray tuchar aout, q, gv).
  { rewrite if_false by (destruct q; try contradiction; discriminate).
    sep_apply (data_at_data_at_ Ews (tarray tuchar aout) (bytes_rep snl) q). cancel. }
  sep_apply (ib_istream_fold gv Tsh vs z' L'); auto.
  forward_if.
  { forward. unfold ib_loop_inv. Exists (pos + used) z' L'. entailer!. }
  { forward. unfold ib_loop_inv. Exists (pos + used) z' L'. entailer!. }
Qed.

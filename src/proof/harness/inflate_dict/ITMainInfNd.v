(* Law inflate_dict, main, inflate half: the branch r == Z_NEED_DICT (ITMainInfKit.v it_nd_stmt): gp_asserts, the wrong dictionary when wsel == 0, the right one, dict_set = 1; then seg_L3 (given). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessRef Zlib.proof.adler32.HarnessBytes
               Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.inflate_common.HarnessLib.
Require Import Zlib.proof.harness.inflate_common.DRefSpec.
Require Import Zlib.proof.harness.inflate_dict.ITLawCS Zlib.proof.harness.inflate_dict.ITGlobals
               Zlib.proof.harness.inflate_dict.ITFacts Zlib.proof.harness.inflate_dict.ITMainKit
               Zlib.proof.harness.inflate_dict.ITMainInfKit.
Require Import Zlib.harness.x_inflate_dict.code.
Require Import Zlib.proof.crc32.Spec.
Local Open Scope logic.

Lemma itnd_lxor b: 0 <= b <= Byte.max_unsigned -> 0 <= Z.lxor b 1 <= Byte.max_unsigned.
Proof.
  intros H. change Byte.max_unsigned with 255 in *. split.
  - apply Z.lxor_nonneg; lia.
  - destruct (Z.eq_dec b 0) as [->|Hb0]; [simpl; lia | ].
    assert (L: Z.log2 (Z.lxor b 1) <= Z.max (Z.log2 b) (Z.log2 1)) by (apply Z.log2_lxor; lia).
    assert (Z.log2 b < 8) by (apply Z.log2_lt_pow2; lia).
    destruct (Z.eq_dec (Z.lxor b 1) 0) as [->|Hx]; [lia | ].
    assert (0 < Z.lxor b 1) by (pose proof (Z.lxor_nonneg b 1); lia).
    assert (Z.lxor b 1 < 2 ^ 8) by (apply Z.log2_lt_pow2; [lia | simpl Z.log2 in L; lia]).
    simpl in *; lia.
Qed.

Lemma itnd_bad G: is_bytes (g_dict G) -> Zlength (g_dict G) <= 2 ^ 16 ->
  is_bytes (it_bad G) /\ 1 <= Zlength (it_bad G) <= 2 ^ 16.
Proof.
  intros B L. unfold it_bad. destruct (g_dict G) as [|b r].
  - simpl. split; [constructor; [cbv; split; congruence | constructor] | rewrite Zlength_cons, Zlength_nil; lia].
  - inversion B; subst. rewrite Zlength_cons in *. split; [constructor; auto; apply itnd_lxor; auto | ].
    pose proof (Zlength_nonneg r). lia.
Qed.

Ltac itnd_gpa := forward_call (Int.repr 1); [ solve [entailer!; try reflexivity] .. | ].

Lemma it_nd {Espec: OracleKind} : it_nd_stmt.
Proof.
  intros I gv vw vs vosn vdl dictp badp datap srcp G wsel dcont scont Fr Inv Brk
         pos lim opos dset aout ibp obp q bs r pos2 made z' L' ow cont GL MF Er K.
  subst r.
  destruct GL as (IF & Gok & Hwsel & Hdc & Hdcs & Hsc & Hscs & Bd & Bdata & Bsrc & Pdict & Pbad & Pdata & Psrc).
  destruct MF as (Hpos & Hlim & Hopos & Haout & Hbs & Bbs & Pib & Pob & Pq & Hpos2 & Hmade & Hpost & Hnm & Hrr
                  & LOK & ZOK & Hcont & Hcs).
  unfold it_post in Hpost. cbv zeta in Hpost.
  destruct Hpost as (Hai & Hao & Hlow & Hbok & [(_ & Hz & Hd & Hm0 & Ho0 & Had & HI) | (Hr & _)]);
    [ | exfalso; unfold Z_NEED_DICT, Z_OK, Z_BUF_ERROR, Z_STREAM_END in Hr; lia].
  subst dset opos.
  assert (made = 0) by lia. subst made.
  destruct (itnd_bad G Bd ltac:(destruct Gok as (_ & _ & ? & _); lia)) as [Bbad Lbad].
  unfold it_mid, seg_L2, it_PL, loop_nocontinue_ret_assert, overridePost, POST_m.
  abbreviate_semax.
  forward_if (EX z3: zfields, EX L3: live,
    !! it_mid2_facts I G pos2 lim 0 true Z_OK z3 L3 (lim - pos) aout ibp obp q
         (bytes_rep (sublist pos lim (it_src G))) cont (bytes_rep bs) &&
    it_mid2 gv vw vs vosn vdl dictp badp datap srcp G wsel dcont scont Fr pos2 lim 0 true Z_OK z3 L3
      (lim - pos) aout ibp obp q (bytes_rep (sublist pos lim (it_src G))) cont (bytes_rep bs)).
  2: { exfalso. match goal with H: Int.repr Z_NEED_DICT <> _ |- _ => apply H; reflexivity end. }
  2: { apply semax_extract_exists; intro z3. apply semax_extract_exists; intro L3.
       apply semax_extract_prop; intro MF2. apply K; exact MF2. }
  rewrite Hz, Hm0. drop_LOCAL 0%nat.
  subst pos2.
  assert_PROP (isptr vs) as Pvs by (unfold istream; entailer!).
  (* gp_assert(zlib && !dict_set) *)
  ifpost _t'42 (Int.repr 1).
  { forward. entailer!. }
  { exfalso. match goal with H: Int.repr 1 = Int.zero |- _ => apply Int.one_not_zero; exact H end. }
  itnd_gpa.
  (* gp_assert(made == 0 && opos == 0) *)
  ifpost _t'43 (Int.repr 1).
  { forward. entailer!. }
  { exfalso. match goal with H: Int.repr 0 <> _ |- _ => apply H; reflexivity end. }
  itnd_gpa.
  (* gp_assert(s.adler == dictid) *)
  rewrite it_istream_unfold. Intros.
  forward.
  match goal with |- semax _ (PROPx _ (LOCALx (temp _ ?v :: _) _)) _ _ =>
    let v' := eval cbv beta iota zeta delta [it_tup] in v in change v with v' end.
  rewrite Had.
  forward_call (Int.repr 1).
  { entailer!. rewrite Int64.eq_true. reflexivity. }
  sep_apply (it_istream_fold gv Tsh vs z' L'); auto.
  (* if (wsel == 0) the wrong dictionary *)
  ifsame.
  { rewrite <- (it_bytes_inflate_cs Ews (Zlength (it_bad G)) _ badp),
            <- (it_tok_inflate_cs Ews (Zlength (it_bad G)) badp).
    forward_call (gv, Tsh, vs, z', Some L', Ews, badp, 0, Zlength (it_bad G), bytes_rep (it_bad G), it_bad G, true).
    { rewrite it_istream_opt by auto. cancel. }
    { split; [rewrite Zlength_bytes_rep; reflexivity | ].
      rewrite sublist_same; [reflexivity | lia | rewrite Zlength_bytes_rep; reflexivity]. }
    Intros vret. destruct vret as [aok winp]. simpl fst; simpl snd.
    rewrite it_on_live by auto.
    rewrite (it_bad_dict I IF G _ z' L' aok winp HI).
    unfold fst3, snd3, thd3; simpl fst; simpl snd.
    rewrite it_istream_opt by auto.
    rewrite (it_bytes_inflate_cs Ews (Zlength (it_bad G)) _ badp), (it_tok_inflate_cs Ews (Zlength (it_bad G)) badp).
    itnd_gpa.
    entailer!. }
  { forward. entailer!. }
  (* the right dictionary *)
  rewrite <- (it_bytes_inflate_cs Ews (Zlength (g_dict G)) _ dictp),
          <- (it_tok_inflate_cs Ews (Zlength (g_dict G)) dictp).
  forward_call (gv, Tsh, vs, z', Some L', Ews, dictp, 0, Zlength (g_dict G), bytes_rep (g_dict G), g_dict G, true).
  { rewrite it_istream_opt by auto. cancel. }
  { assert (Zlength (g_dict G) <= 2 ^ 16) by (destruct Gok as (_ & _ & ? & _); lia).
    split; [rewrite Zlength_bytes_rep; reflexivity | ]. split3; [rep_lia | rep_lia | ].
    rewrite sublist_same; [reflexivity | lia | rewrite Zlength_bytes_rep; reflexivity]. }
  Intros vret. destruct vret as [aok winp]. simpl fst; simpl snd.
  rewrite it_on_live by auto.
  pose proof (it_good_dict I IF G _ z' L' aok winp HI LOK ZOK) as SP.
  destruct (setdict_f (g_dict G) aok winp z' L') as [[r z3] L3] eqn:E.
  unfold fst3, snd3, thd3 in *; simpl fst in *; simpl snd in *.
  rewrite it_istream_opt by auto.
  rewrite (it_bytes_inflate_cs Ews (Zlength (g_dict G)) _ dictp), (it_tok_inflate_cs Ews (Zlength (g_dict G)) dictp).
  assert_PROP (live_ok L3 /\ zf_ok z3) as LZ3 by (unfold istream; entailer!).
  destruct LZ3 as [LOK3 ZOK3].
  destruct SP as [[Er|Er] SPI]; subst r.
  2: { forward_if (PROP (False) LOCAL () SEP ()).
       { forward. Exists (Int.repr 0).
         sep_apply it_istream_to_undef. sep_apply (data_at_data_at_ Tsh (tptr tuchar) q vosn). entailer!. }
       all: try (exfalso; match goal with H: Int.repr Z_MEM_ERROR <> _ |- _ => apply H; reflexivity end).
       all: try (Intros; contradiction). }
  ifsame.
  all: try (exfalso; match goal with H: Int.repr Z_OK = _ |- _ =>
                       apply (f_equal Int.signed) in H; vm_compute in H; discriminate H end).
  all: try (forward; entailer!).
  itnd_gpa.
  forward.
  Exists z3 L3.
  unfold it_mid2. rewrite Hz.
  entailer!.
  unfold it_mid2_facts. split; [intros X; unfold Z_OK, Z_STREAM_END in X; lia | ].
  split; [intros _; apply SPI; reflexivity | ].
  rewrite !Zlength_bytes_rep, Zlength_sublist by lia. unfold Z_OK.
  refine (conj _ (conj _ (conj _ (conj _ (conj LOK3 (conj ZOK3 (conj _ (conj _ (conj _ (conj _ (conj _
    (conj Pib (conj Pob Pq))))))))))))); try lia; rep_lia.
Qed.

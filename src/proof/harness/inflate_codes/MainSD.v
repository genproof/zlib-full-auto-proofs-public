(* Law inflate_codes, main: the branch `op < 24` of the loop (inflateSetDictionary(&s, ob, aout) and its checks). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessRef Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.inflate_common.HarnessLib.
Require Import Zlib.proof.harness.inflate_codes.LawCS Zlib.proof.harness.inflate_codes.Globals
               Zlib.proof.harness.inflate_codes.Facts Zlib.proof.harness.inflate_codes.MainKit.
Require Import Zlib.harness.x_inflate_codes.code.

Ltac gpa := forward_call (Int.repr 1); [ solve [entailer!; try reflexivity] .. | ].

Ltac infeas := exfalso; first [ match goal with H: ?a <> ?b |- _ => solve [apply H; reflexivity] end
                              | match goal with H: _ |- _ => solve [discriminate H] end
                              | contradiction
                              | match goal with H: Int.repr _ = Int.repr _ |- _ =>
                                  apply repr_inj_signed in H; [lia | rep_lia | rep_lia] end
                              | lia ].

Lemma sd_on_live (vs: val) z L f: isptr vs ->
  on_live vs z (Some L) f = let '(r, z', L') := f z L in (r, z', Some L').
Proof. intros P. unfold on_live, is_live. destruct (eq_dec vs nullval); [subst; contradiction | reflexivity]. Qed.

Lemma sd_istream_opt gv shs (vs: val) z st: isptr vs -> istream_opt gv shs vs z st = istream gv shs vs z st.
Proof. intros P. unfold istream_opt. destruct (eq_dec vs nullval); [subst; contradiction | reflexivity]. Qed.

Lemma sd_ret dict a winp z L:
  let r := fst3 (setdict_f dict a winp z L) in r = Z_OK \/ r = Z_STREAM_ERROR \/ r = Z_DATA_ERROR \/ r = Z_MEM_ERROR.
Proof.
  unfold setdict_f. destruct (setdict_check (l_s L) dict); unfold fst3; simpl; auto.
  destruct (i_win (l_s L)); simpl; auto. destruct a; simpl; auto.
Qed.

(* the stream at the law's compspecs *)
Definition sd_strm_tuple : Type :=
  (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * val)))))))))))))%type.

Lemma sd_strm_cs sh (v: sd_strm_tuple) q:
  @data_at Zlib.units.Inflate.CS sh Rep.t_strm v q = @data_at CS sh (Tstruct _z_stream_s noattr) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_inflate); [apply JMeq_refl | reflexivity]. Qed.

Definition sd_tup (gv: globals) (z: zfields) (sp: val) :=
  (zf_ni z, (Vint (Int.repr (zf_ai z)), (Vlong (Int64.repr (zf_tin z)), (zf_no z, (Vint (Int.repr (zf_ao z)),
   (Vlong (Int64.repr (zf_tout z)), (msg_val gv (zf_msg z), (sp, (gv Zlib.inflate.code._zcalloc,
   (gv Zlib.inflate.code._zcfree, (nullval, (Vint (Int.repr (zf_dt z)), (Vlong (Int64.repr (zf_adler z)),
   zf_res z))))))))))))).

Lemma sd_istream_unfold gv shs vs z L:
  istream gv shs vs z (Some L) =
  !! (zf_ok z /\ writable_share shs /\ live_ok L) &&
  (@data_at CS shs (Tstruct _z_stream_s noattr) (sd_tup gv z (l_sp L)) vs * state_mem gv vs L)%logic.
Proof.
  unfold istream, zstrm_at, strm_rep.
  rewrite sd_strm_cs.
  apply pred_ext; entailer!.
Qed.

Lemma seg_setdict_ok {Espec: OracleKind} I gv vs vo vosn vb vdl w srcp src pos final indict z L
    ain aout flush innull outnull stop ibp obp bs Fr (Post: ret_assert) :
  br_facts I w srcp src pos final indict z L ain aout flush innull outnull stop ibp obp bs ->
  semax Delta_m
    (br_pre gv vs vo vosn vb vdl w srcp src pos final indict z L ain aout flush innull outnull stop ibp obp bs Fr)
    seg_setdict
    (overridePost (br_post I gv vs vo vosn vb vdl w srcp src pos ain aout stop ibp obp Fr) Post).
Proof.
  intros BF.
  destruct BF as (CF & HI & Hwok & Hw & Hpos & Hain & Hpa & Hsrc & Hsb & Haout & Hbsl & Hbsb & Hfl & Hin & Hout & Hst & Psrc & Pib & Pob).
  unfold br_pre.
  assert_PROP (live_ok L /\ zf_ok z /\ isptr vs) as LZ by (unfold istream; entailer!).
  destruct LZ as (LOK & ZOK & Pvs).
  unfold seg_setdict.
  rewrite <- (bytes_inflate_cs Ews aout _ obp), <- (tok_inflate_cs Ews aout obp).
  forward_call (gv, Tsh, vs, z, Some L, Ews, obp, 0, aout, bytes_rep bs, bs, true).
  { entailer!. }
  { rewrite sd_istream_opt by auto. cancel. }
  { split; [rewrite Zlength_bytes_rep; lia | ]. rewrite sublist_same; [reflexivity | lia | rewrite Zlength_bytes_rep; lia]. }
  Intros vret. destruct vret as [aok winp]. simpl fst; simpl snd.
  pose proof (sd_ret bs aok winp z L) as Hr.
  pose proof (cf_setdict I CF w src pos final indict z L bs aok winp HI LOK ZOK Hbsb ltac:(lia)) as SP.
  rewrite sd_on_live by auto.
  destruct (setdict_f bs aok winp z L) as [[r z'] L'] eqn:E.
  unfold fst3, snd3, thd3 in *; simpl in Hr |- *. simpl in SP.
  rewrite sd_istream_opt by auto.
  destruct SP as (SPneg & SPnd & SPd & SPI).
  ifsame.
  { (* wbits < 0 *)
    destruct (SPneg ltac:(lia)) as [Er | Er]; subst r.
    - ifpost _t'31 (Int.repr 1).
      { forward. entailer!. }
      { infeas. }
      gpa. entailer!.
    - ifpost _t'31 (Int.repr 1).
      { infeas. }
      { forward. entailer!. }
      gpa. entailer!. }
  { assert (Hid: indict = 0 \/ indict = 1) by apply (proj2 (cf_range I CF _ _ _ _ _ _ _ HI)).
    ifsame.
    { assert (indict = 0).
      { destruct Hid; auto; subst. match goal with H: Int.repr 1 = Int.zero |- _ =>
          exfalso; apply Int.one_not_zero; exact H end. }
      assert (r = Z_STREAM_ERROR) by (apply SPnd; lia). subst r. gpa. entailer!. }
    assert (indict = 1) by (destruct Hid; subst; auto; contradiction). subst indict.
    destruct (SPd ltac:(lia) ltac:(lia)) as [Hda Hro].
    rewrite <- (bytes_adler_cs Ews aout _ obp).
    forward_call (1, obp, Ews, obp, 0, aout, bytes_rep bs, aout, bs).
    { subst aout. apply cbuf_ok_whole; auto. }
    rewrite (bytes_adler_cs Ews aout _ obp).
    rewrite sd_istream_unfold. Intros.
    forward.
    match goal with |- context [temp _t'74 ?v] => let v' := eval cbv beta iota zeta delta [sd_tup] in v in change v with v' end.
    assert (Hv1: Zlib.proof.adler32.Model.adler_valid 1) by (cbv; repeat split; congruence).
    pose proof (Zlib.proof.adler32.Model.ref_adler32_valid 1 bs Hv1) as Hra. destruct Hra as [Hra _].
    set (ra := ref_adler32 1 bs) in *. clearbody ra.
    match goal with H: zf_ok z' |- _ => pose proof H as ZOK'; destruct H as (_ & _ & _ & _ & _ & Had) end.
    destruct Hro as [Er|[Er|Er]]; subst r.
    - assert (Eq: ra = zf_adler z')
        by (destruct (Z.eq_dec ra (zf_adler z')) as [ | X]; auto; apply Hda in X; discriminate).
      rewrite Eq.
      forward_call (Int.repr 1).
      { entailer!. rewrite Int64.eq_true. reflexivity. }
      ifpost _t'33 (Int.repr 1).
      { forward. entailer!. }
      { infeas. }
      ifpost _t'34 (Int.repr 1).
      { forward. entailer!. }
      { infeas. }
      gpa. rewrite sd_istream_unfold. entailer!.
    - assert (Hne: ra <> zf_adler z') by (apply Hda; auto).
      assert (Hne64: Int64.eq (Int64.repr ra) (Int64.repr (zf_adler z')) = false)
        by (apply Int64.eq_false; intro X; apply repr_inj_unsigned64 in X; [contradiction | rep_lia | rep_lia]).
      forward_call (Int.repr 1).
      { entailer!. rewrite Hne64. reflexivity. }
      ifpost _t'33 (Int.repr 1).
      { infeas. }
      { forward. entailer!. }
      ifpost _t'34 (Int.repr 1).
      { forward. entailer!. }
      { infeas. }
      gpa. rewrite sd_istream_unfold. entailer!.
    - assert (Eq: ra = zf_adler z')
        by (destruct (Z.eq_dec ra (zf_adler z')) as [ | X]; auto; apply Hda in X; discriminate).
      rewrite Eq.
      forward_call (Int.repr 1).
      { entailer!. rewrite Int64.eq_true. reflexivity. }
      ifpost _t'33 (Int.repr 0).
      { infeas. }
      { forward. entailer!. }
      ifpost _t'34 (Int.repr 1).
      { infeas. }
      { forward. entailer!. }
      gpa. rewrite sd_istream_unfold. entailer!. }
destruct (Z.eqb_spec r Z_MEM_ERROR) as [Em | Em].
  { subst r. forward_if (br_post I gv vs vo vosn vb vdl w srcp src pos ain aout stop ibp obp Fr).
    { forward. forward. unfold br_post. Exists pos Z_MEM_ERROR 0 z' L' (bytes_rep bs). entailer!. }
    { infeas. }
    destruct Post; apply andp_left2, derives_refl. }
  { forward_if (br_post I gv vs vo vosn vb vdl w srcp src pos ain aout stop ibp obp Fr).
    { exfalso. match goal with H: Int.repr r = _ |- _ =>
        destruct Hr as [E1|[E1|[E1|E1]]]; subst r; try contradiction;
        apply (f_equal Int.signed) in H; vm_compute in H; discriminate H end. }
    { forward. unfold br_post. Exists pos final indict z' L' (bytes_rep bs). entailer!. }
    destruct Post; apply andp_left2, derives_refl. }
Qed.

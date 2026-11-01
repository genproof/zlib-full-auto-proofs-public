(* Law compress_roundtrip, part RT-CL: main's body (harness/compress_roundtrip.c) against
   MainLib.main_core_spec R under RTCLMainDefs.Gmain, from c2_ok and ufacts. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Zlib.proof.compress.CSpec.
Require Import Zlib.proof.roundtrip.RTCSpec.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.uncompr.USpec5.
Require Import Zlib.proof.roundtrip.RTC2 Zlib.proof.roundtrip.RTIIface.
Require Import Zlib.proof.roundtrip.RTCLCS Zlib.proof.roundtrip.RTCLGlobals Zlib.proof.roundtrip.RTCLMainDefs.
Require Zlib.proof.roundtrip.RTCLFacts.
Require Import Zlib.harness.x_compress_roundtrip.code.
#[local] Existing Instance RTCLCS.CS.
Local Open Scope logic.

Lemma rtcl_cb_range n : 0 <= n <= 2 ^ 20 -> n + 13 <= c_compressBound n <= n + 400.
Proof.
  intros Hn. unfold c_compressBound, compressBound_z.
  rewrite !Z.shiftr_div_pow2 by lia.
  assert (0 <= n / 2 ^ 12 <= 256) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
  assert (0 <= n / 2 ^ 14 <= 64) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
  assert (n / 2 ^ 25 = 0) by (apply Z.div_small; lia).
  unfold Zlib.proof.huffman.Model.u64. rewrite Z.mod_small by lia.
  destruct (Z.ltb_spec (n + n / 2 ^ 12 + n / 2 ^ 14 + n / 2 ^ 25 + 13) n); lia.
Qed.

(* moves between the units' compspecs and the law's *)
Lemma cl_bytes_compress sh n (v: list val) q:
  @data_at Zlib.units.Compress.CS sh (tarray tuchar n) v q = @data_at CS sh (tarray tuchar n) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_compress); [apply JMeq_refl | reflexivity]. Qed.
Lemma cl_ulong_compress sh (v: val) q:
  @data_at Zlib.units.Compress.CS sh tulong v q = @data_at CS sh tulong v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_compress); [apply JMeq_refl | reflexivity]. Qed.
Lemma cl_bytes_uncompr sh n (v: list val) q:
  @data_at Zlib.units.Uncompr.CS sh (tarray tuchar n) v q = @data_at CS sh (tarray tuchar n) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_uncompr); [apply JMeq_refl | reflexivity]. Qed.
Lemma cl_tok_uncompr sh n q:
  @malloc_token Zlib.units.Uncompr.CS sh (tarray tuchar n) q = @malloc_token CS sh (tarray tuchar n) q.
Proof. apply equal_f; apply (@malloc_token_change_composite _ _ CC_uncompr). reflexivity. Qed.
Lemma cl_ulong_uncompr sh (v: val) q:
  @data_at Zlib.units.Uncompr.CS sh tulong v q = @data_at CS sh tulong v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_uncompr); [apply JMeq_refl | reflexivity]. Qed.
Lemma cl_bytes_adler sh n (v: list val) q:
  @data_at Zlib.units.Adler32.CS sh (tarray tuchar n) v q = @data_at CS sh (tarray tuchar n) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_adler32); [apply JMeq_refl | reflexivity]. Qed.

Ltac cl_law := repeat first [ rewrite cl_bytes_compress | rewrite cl_ulong_compress | rewrite cl_bytes_uncompr
                            | rewrite cl_tok_uncompr | rewrite cl_ulong_uncompr | rewrite cl_bytes_adler ].

(* compress / compress2's precondition, from c2_ok *)
Lemma cl_c2_pre (CF: c2_ok) lvl gv dp dlp sp src :
  isptr dp -> isptr sp -> rbytes src -> Zlength src <= 2 ^ 20 -> rs32 lvl ->
  fold_right_and True
    (c2_pre lvl gv dp (Zrepeat Vundef (c_compressBound (Zlength src))) (c_compressBound (Zlength src)) dlp Ews sp
       src).
Proof.
  intros Hd Hs Hb Hn Hl. pose proof (rtcl_cb_range (Zlength src) ltac:(rep_lia)) as Hcb.
  unfold c2_pre. simpl. unfold Zrepeat. rewrite Zlength_repeat by rep_lia. unfold umax.
  assert (0 <= Zlength src) by apply Zlength_nonneg.
  split; [exact Hd | ]. split; [reflexivity | ]. split; [rep_lia | ]. split; [auto | ].
  split; [exact Hs | ]. split; [rep_lia | ]. split; [exact Hb | ]. split; [exact Hl | ]. split; [ | exact I].
  intros. apply (CF src lvl a1 a2 a3 a4 a5 _ Hb ltac:(rep_lia) Hl).
Qed.

(* compress / compress2's outcome, from c2_ok *)
Lemma cl_c2_post (CF: c2_ok) src lvl a1 a2 a3 a4 a5 r out :
  rbytes src -> Zlength src <= 1048576 -> rs32 lvl ->
  c2_res src (c_compressBound (Zlength src)) lvl a1 a2 a3 a4 a5 Zlib.proof.deflate.DSpec9.zrst0 r out ->
  (r = Z_OK \/ r = Z_STREAM_ERROR \/ r = Z_MEM_ERROR) /\ (r = Z_STREAM_ERROR <-> ~ (-1 <= lvl <= 9)) /\
  (r = Z_OK -> RTFinal.dfinal [] 1 15 None src out).
Proof.
  intros Hb Hn Hl Hrel. destruct (CF src lvl a1 a2 a3 a4 a5 Zlib.proof.deflate.DSpec9.zrst0 Hb Hn Hl) as [_ P].
  destruct (P r out Hrel) as (A & B & _ & D). auto.
Qed.

(* deflate_globals without crc32's table (which uncompress's inflate_globals takes, at share Ers) *)
Definition cl_dgr (gv : globals) : mpred :=
  trees_globals gv * errmsg_at gv *
  @data_at Zlib.proof.deflate.DCS.CS Ers (tarray t_config 10) (config_vals gv) (gv Zlib.deflate.code._configuration_table) *
  @data_at Zlib.proof.deflate.DCS.CS Ers (tarray tschar 6) (map vi [49; 46; 51; 46; 50; 0]) (gv Zlib.deflate.code._my_version).

Lemma cl_ig_to gv :
  deflate_globals gv * tables_rep Ers gv * version_lit gv * Zlib.proof.inflate.Callees.zfuncs gv |--
  inflate_globals Ers Ers gv * cl_dgr gv.
Proof. unfold deflate_globals, cl_dgr, inflate_globals. cancel. Qed.

Lemma cl_ig_from gv :
  inflate_globals Ers Ers gv * cl_dgr gv |--
  deflate_globals gv * tables_rep Ers gv * version_lit gv * Zlib.proof.inflate.Callees.zfuncs gv.
Proof. unfold deflate_globals, cl_dgr, inflate_globals. cancel. Qed.

Lemma cl_unc_dlen src cap r slen dlen out : uncompress_rel src cap r slen dlen out -> 0 <= cap -> 0 <= dlen.
Proof.
  intros [(_ & _ & -> & _) | (err & _ & -> & _)] Hc; [lia | apply Zlength_nonneg].
Qed.

(* forward_call's frame when the spec's SEP list is a definition [d] (RTCSpec.c2_sep_pre) *)
Ltac cl_sep_cancel d :=
  unfold d;
  repeat (eapply syntactic_cancel_cons_succeed;
          [find_nth ecancel_local_tac | cbv iota; unfold delete_nth; cbv zeta iota ]);
  apply syntactic_cancel_nil.

Lemma body_main : body_main_stmt.
Proof.
  intros CF UF.
  start_function.
  unfold R. Intros.
  make_func_ptr Zlib.inflate.code._zcalloc. make_func_ptr Zlib.inflate.code._zcfree.
  gather_SEP (func_ptr' _ (gv Zlib.inflate.code._zcalloc)) (func_ptr' _ (gv Zlib.inflate.code._zcfree)).
  fold (Zlib.proof.inflate.Callees.zfuncs gv).
  forward_call tt. Intros n. forward_call tt. Intros lv. forward_call tt. Intros k. forward_call tt. Intros pl.
  forward_call (Int.repr (if n <=? 2^20 then 1 else 0)).
  { entailer!. arg_cmp. }
  assumed. apply Z.leb_le in E.
  forward_call (tarray tuchar n, gv).
  { simpl. rewrite Z.max_r by lia. rep_lia. }
  Intros datap.
  destruct (eq_dec datap nullval) as [PS|PS].
  { subst datap. forward_if. { ret0. } { contradiction. } }
  Intros.
  forward_if.
  { contradiction. }
  forward_call (datap, n, Ews).
  { rewrite if_false by auto. cancel. }
  Intros src. rewrite if_false by auto.
  match goal with H: Zlength src = n |- _ => rename H into Hsrcn end.
  match goal with H: Forall _ src |- _ => rename H into Hsrcb end.
  subst n.
  pose proof (rtcl_cb_range (Zlength src) ltac:(rep_lia)) as Hcb.
  forward_call (Zlength src).
  set (cb := c_compressBound (Zlength src)) in *.
  forward_call (tarray tuchar cb, gv).
  { simpl. rewrite Z.max_r by lia. rep_lia. }
  Intros destp.
  destruct (eq_dec destp nullval) as [PD|PD].
  { subst destp. forward_if. { ret0. } { contradiction. } }
  Intros.
  forward_if.
  { contradiction. }
  forward.
  assert_PROP (isptr destp) as Pdest by entailer!.
  assert_PROP (isptr datap) as Pdata by entailer!.
  replace (data_at_ Ews (tarray tuchar cb) destp) with (data_at Ews (tarray tuchar cb) (Zrepeat Vundef cb) destp)
    by reflexivity.
  assert (Hrb: rbytes src) by (eapply Forall_impl; [ | exact Hsrcb]; simpl; intros; rep_lia).
  forward_if (EX lvl : Z, EX a1 : bool, EX a2 : bool, EX a3 : bool, EX a4 : bool, EX a5 : bool, EX r : Z,
    EX out : list Z,
    PROP (lvl = (if pl =? 0 then -1 else Int.signed (Int.repr lv));
          c2_res src cb lvl a1 a2 a3 a4 a5 Zlib.proof.deflate.DSpec9.zrst0 r out; Zlength out <= cb)
    LOCAL (temp _r (Vint (Int.repr r)); temp _cb (Vlong (Int64.repr cb)); temp _dest destp; temp _data datap;
           temp _plain (Vint (Int.repr pl)); temp _k (Vint (Int.repr k)); temp _level (Vint (Int.repr lv));
           temp _n (Vint (Int.repr (Zlength src))); lvar _slen tulong v_slen; lvar _olen tulong v_olen;
           lvar _dlen tulong v_dlen; gvars gv)
    SEP (data_at Ews (tarray tuchar cb) (map vi out ++ sublist (Zlength out) cb (Zrepeat Vundef cb)) destp;
         malloc_token Ews (tarray tuchar cb) destp;
         data_at Tsh tulong (vl (Zlength out)) v_dlen;
         data_at Ews (tarray tuchar (Zlength src)) (map (fun b : Z => Vint (Int.repr b)) src) datap;
         malloc_token Ews (tarray tuchar (Zlength src)) datap;
         mem_mgr gv; data_at_ Tsh tulong v_slen; data_at_ Tsh tulong v_olen;
         deflate_globals gv; cversion_lit gv; tables_rep Ers gv; version_lit gv; uversion_lit gv;
         Zlib.proof.inflate.Callees.zfuncs gv; TT)).
  { rewrite <- (cl_bytes_compress Ews cb _ destp), <- (cl_bytes_compress Ews (Zlength src) _ datap),
      <- (cl_ulong_compress Tsh _ v_dlen).
    forward_call (gv, destp, Zrepeat Vundef cb, cb, v_dlen, Ews, datap, src).
    cl_sep_cancel c2_sep_pre.
    apply (cl_c2_pre CF); [exact Pdest | exact Pdata | exact Hrb | rep_lia | unfold rs32; lia].
    unfold c2_sep_post. simpl app.
    Intros vret. destruct vret as [[[[[[a1 a2] a3] a4] a5] r] out]. simpl fst in *; simpl snd in *.
    forward. subst pl. Exists (-1) a1 a2 a3 a4 a5 r out. cl_law. entailer!. }
  { rewrite <- (cl_bytes_compress Ews cb _ destp), <- (cl_bytes_compress Ews (Zlength src) _ datap),
      <- (cl_ulong_compress Tsh _ v_dlen).
    forward_call (gv, destp, Zrepeat Vundef cb, cb, v_dlen, Ews, datap, src, Int.signed (Int.repr lv)).
    { entailer!. simpl. unfold vi, vl. rewrite Int.repr_signed. simpl. rewrite Int.unsigned_repr by rep_lia.
      reflexivity. }
    cl_sep_cancel c2_sep_pre.
    apply (cl_c2_pre CF); [exact Pdest | exact Pdata | exact Hrb | rep_lia | ].
    unfold rs32; pose proof (Int.signed_range (Int.repr lv)); rep_lia.
    unfold c2_sep_post. simpl app.
    Intros vret. destruct vret as [[[[[[a1 a2] a3] a4] a5] r] out]. simpl fst in *; simpl snd in *.
    forward. Exists (Int.signed (Int.repr lv)) a1 a2 a3 a4 a5 r out. cl_law. entailer!.
    rewrite (proj2 (Z.eqb_neq pl 0) H5). auto. }
  Intros lvl a1 a2 a3 a4 a5 r out.
  set (L := Int.signed (Int.repr lv)) in *.
  assert (HL: Int.min_signed <= L <= Int.max_signed) by apply Int.signed_range.
  set (lok := ((pl =? 0) || ((-1 <=? L) && (L <=? 9)))%bool).
  ifpost _t'10 (Int.repr (if lok then 1 else 0)).
  { forward. entailer!. }
  { forward_if.
    - forward. forward. entailer!. unfold lok. rewrite (proj2 (Z.eqb_neq pl 0) H8). simpl.
      change (Int.signed (Int.repr (- (1)))) with (-1) in *. fold L in H9.
      unfold Int.lt. change (Int.signed (Int.repr 9)) with 9. fold L.
      destruct (zlt 9 L); destruct (Z.leb_spec (-1) L), (Z.leb_spec L 9); simpl; try reflexivity; lia.
    - forward. entailer!. unfold lok. rewrite (proj2 (Z.eqb_neq pl 0) H8). simpl.
      change (Int.signed (Int.repr (- (1)))) with (-1) in *. fold L in H9.
      destruct (Z.leb_spec (-1) L); simpl; try reflexivity; lia. }
  forward.
  assert (Hlok: lok = true <-> -1 <= lvl <= 9).
  { subst lvl. unfold lok. destruct (Z.eqb_spec pl 0); simpl.
    - split; intros; [lia | reflexivity].
    - rewrite andb_true_iff, !Z.leb_le. lia. }
  assert (Hlvl: rs32 lvl).
  { subst lvl. unfold rs32. destruct (pl =? 0); rep_lia. }
  destruct (cl_c2_post CF src lvl a1 a2 a3 a4 a5 r out Hrb ltac:(rep_lia) Hlvl H6) as (Hr & Hr2 & Hok).
  forward_if.
  { ret0. }
  forward_call (Int.repr 1).
  { entailer!. assert (r <> -4) by (intro; subst; apply H8; reflexivity).
    unfold Z_OK, Z_STREAM_ERROR, Z_MEM_ERROR in *.
    destruct lok eqn:EL; destruct Hr as [-> | [-> | ->]]; try lia; simpl; try reflexivity. }
  forward_if.
  { destruct lok; [discriminate | ]. ret0. }
  assert (Hl9: -1 <= lvl <= 9).
  { apply (proj1 Hlok). destruct lok; [reflexivity | ].
    match goal with H: Int.repr 0 <> Int.zero |- _ => contradiction H; reflexivity end. }
  assert (r = 0) by (unfold Z_OK, Z_STREAM_ERROR, Z_MEM_ERROR in *; destruct Hr as [? | [? | ?]]; try lia;
                     subst; exfalso; apply H8; reflexivity).
  subst r.
  specialize (Hok eq_refl).
  clear H8 Hr Hr2 Hlok.
  forward_call (Int.repr 1).
  forward.
  forward_call (Int.repr 1).
  { entailer!. simpl. unfold Int64.ltu. rewrite !Int64.unsigned_repr by rep_lia.
    destruct (zlt _ _); [lia | reflexivity]. }
  (* out = malloc(n) *)
  forward_call (tarray tuchar (Zlength src), gv).
  { simpl. rewrite Z.max_r by lia. rep_lia. }
  Intros outp.
  destruct (eq_dec outp nullval) as [PO|PO].
  { subst outp. forward_if. { ret0. } { contradiction. } }
  Intros.
  forward_if.
  { contradiction. }
  forward_call (outp, Zlength src, Ews).
  { rewrite if_false by auto. cancel. }
  Intros ob. rewrite if_false by auto.
  forward. forward.
  rewrite Int.unsigned_repr by rep_lia.
  assert_PROP (isptr outp) as Pout by entailer!.
  assert (Hob: bytes_ok out) by exact (Zlib.proof.roundtrip.RTCLFacts.rtcl_dfinal_bytes _ _ Hok).
  set (dc := map vi out ++ sublist (Zlength out) cb (Zrepeat Vundef cb)) in *.
  assert (Hdc: Zlength dc = cb) by (unfold dc, Zrepeat; list_solve).
  assert (Hdc0: sublist 0 (Zlength out) dc = byte_vals out) by (unfold dc, byte_vals, vi; list_solve).
  (* r = uncompress(out, &olen, dest, dlen) *)
  rewrite <- (cl_bytes_uncompr Ews (Zlength src) _ outp), <- (cl_tok_uncompr Ews (Zlength src) outp),
    <- (cl_bytes_uncompr Ews cb _ destp), <- (cl_tok_uncompr Ews cb destp), <- (cl_ulong_uncompr Tsh _ v_olen).
  sep_apply (cl_ig_to gv).
  forward_call (gv, Ews, outp, Zlength src, map (fun b : Z => Vint (Int.repr b)) ob, Zlength src, v_olen, true, true,
                Ews, destp, cb, dc, out, Ers, Ers).
  { cancel. }
  { repeat split; try list_solve; auto. }
  Intros vret. destruct vret as [[[r1 slen1] dlen1] out1]. simpl fst in *; simpl snd in *.
  match goal with H: uncompress_rel _ _ _ _ _ _ |- _ => rename H into Hu1 end.
  destruct (uf_full UF src out r1 slen1 dlen1 out1 Hok ltac:(rep_lia) ltac:(rep_lia) Hu1) as [Hm1 | (Hr1 & Hd1 & Ho1 & Hs1)].
  { subst r1. forward. forward_if. { ret0. } { exfalso. auto. } }
  subst r1 dlen1 out1.
  forward. cl_law. sep_apply (cl_ig_from gv).
  forward_if.
  { discriminate. }
  Intros.
  assert (Hda: dest_after (map (fun b : Z => Vint (Int.repr b)) ob) (Zlength src) src =
               map (fun b : Z => Vint (Int.repr b)) src) by (unfold dest_after, byte_vals; list_solve).
  rewrite Hda.
  ifpost _t'13 (Int.repr 1).
  { forward. forward. entailer!. }
  { forward. entailer!. }
  ifpost _t'14 (Int.repr 1).
  { rewrite <- (cl_bytes_adler Ews (Zlength src) _ outp), <- (cl_bytes_adler Ews (Zlength src) _ datap).
    forward_call (outp, Ews, outp, 0, Zlength src, map (fun b : Z => Vint (Int.repr b)) src, src,
                  datap, Ews, datap, 0, Zlength src, map (fun b : Z => Vint (Int.repr b)) src, src, Zlength src).
    { unfold cbuf_ok. rewrite !isptr_offset_val_zero by auto. unfold bytes_rep, is_bytes.
      rewrite sublist_same by list_solve. repeat split; auto; try rep_lia. }
    forward. destruct (list_eq_dec Z.eq_dec src src); [ | contradiction]. cl_law. entailer!. }
  { discriminate. }
  forward_call (Int.repr 1).
  clear Hda Hu1 Hs1 slen1 ob H10 H11.
  (* uncompress2(out, &olen, dest, &slen) *)
  forward_call (outp, Zlength src, Ews).
  { rewrite if_false by auto. sep_apply (data_at_data_at_ Ews (tarray tuchar (Zlength src))). cancel. }
  Intros ob. rewrite if_false by auto.
  forward. forward. forward.
  rewrite Int.unsigned_repr by rep_lia.
  rewrite <- (cl_bytes_uncompr Ews (Zlength src) _ outp), <- (cl_tok_uncompr Ews (Zlength src) outp),
    <- (cl_bytes_uncompr Ews cb _ destp), <- (cl_tok_uncompr Ews cb destp), <- (cl_ulong_uncompr Tsh _ v_olen),
    <- (cl_ulong_uncompr Tsh _ v_slen).
  sep_apply (cl_ig_to gv).
  forward_call (gv, Ews, outp, Zlength src, map (fun b : Z => Vint (Int.repr b)) ob, Zlength src, v_olen, true, true,
                Ews, destp, cb, dc, out, v_slen, Ers, Ers).
  { cancel. }
  { repeat split; try list_solve; auto. }
  Intros vret. destruct vret as [[[r2 slen2] dlen2] out2]. simpl fst in *; simpl snd in *.
  match goal with H: uncompress_rel _ _ _ _ _ _ |- _ => rename H into Hu2 end.
  destruct (uf_full UF src out r2 slen2 dlen2 out2 Hok ltac:(rep_lia) ltac:(rep_lia) Hu2) as [Hm2 | (Hr2 & Hd2 & Ho2 & Hs2)].
  { subst r2. forward_if. { ret0. } { exfalso. auto. } }
  subst r2 dlen2 out2 slen2.
  cl_law. sep_apply (cl_ig_from gv).
  forward_if.
  { discriminate. }
  Intros.
  assert (Hda: dest_after (map (fun b : Z => Vint (Int.repr b)) ob) (Zlength src) src =
               map (fun b : Z => Vint (Int.repr b)) src) by (unfold dest_after, byte_vals; list_solve).
  rewrite Hda.
  ifpost _t'17 (Int.repr 1).
  { forward. forward. entailer!. }
  { forward. entailer!. }
  ifpost _t'18 (Int.repr 1).
  { forward. forward. forward. entailer!. }
  { discriminate. }
  ifpost _t'19 (Int.repr 1).
  { rewrite <- (cl_bytes_adler Ews (Zlength src) _ outp), <- (cl_bytes_adler Ews (Zlength src) _ datap).
    forward_call (outp, Ews, outp, 0, Zlength src, map (fun b : Z => Vint (Int.repr b)) src, src,
                  datap, Ews, datap, 0, Zlength src, map (fun b : Z => Vint (Int.repr b)) src, src, Zlength src).
    { unfold cbuf_ok. rewrite !isptr_offset_val_zero by auto. unfold bytes_rep, is_bytes.
      rewrite sublist_same by list_solve. repeat split; auto; try rep_lia. }
    forward. destruct (list_eq_dec Z.eq_dec src src); [ | contradiction]. cl_law. entailer!. }
  { discriminate. }
  forward_call (Int.repr 1).
  clear Hda Hu2.
  forward_if (PROP ()
    LOCAL (temp _out outp; temp _dest destp; temp _k (Vint (Int.repr k)); temp _n (Vint (Int.repr (Zlength src)));
           lvar _slen tulong v_slen; lvar _olen tulong v_olen; lvar _dlen tulong v_dlen; gvars gv)
    SEP (deflate_globals gv; tables_rep Ers gv; version_lit gv; zfuncs gv;
         data_at Ews (tarray tuchar (Zlength src)) (map (fun b : Z => Vint (Int.repr b)) src) outp;
         malloc_token Ews (tarray tuchar (Zlength src)) outp;
         data_at_ Tsh tulong v_olen; data_at Ews (tarray tuchar cb) dc destp;
         malloc_token Ews (tarray tuchar cb) destp; data_at_ Tsh tulong v_slen;
         uversion_lit gv; mem_mgr gv; data_at Tsh tulong (vl (Zlength out)) v_dlen; TT)).
  { (* small = malloc(n - 1); uncompress with one byte too few *)
    assert (Hn0: 0 < Zlength src) by assumption.
    forward_call (tarray tuchar (Zlength src - 1), gv).
    { simpl. rewrite Z.max_r by lia. rep_lia. }
    Intros smallp.
    destruct (eq_dec smallp nullval) as [PSm|PSm].
    { subst smallp. forward_if. { ret0. } { contradiction. } }
    Intros.
    forward_if.
    { contradiction. }
    forward. forward.
    assert_PROP (isptr smallp) as Psm by entailer!.
    replace (data_at_ Ews (tarray tuchar (Zlength src - 1)) smallp)
      with (data_at Ews (tarray tuchar (Zlength src - 1)) (Zrepeat Vundef (Zlength src - 1)) smallp)
      by reflexivity.
    rewrite sub_repr, (Int.unsigned_repr (Zlength src - 1)) by rep_lia.
    rewrite <- (cl_bytes_uncompr Ews (Zlength src - 1) _ smallp), <- (cl_tok_uncompr Ews (Zlength src - 1) smallp),
      <- (cl_bytes_uncompr Ews cb _ destp), <- (cl_tok_uncompr Ews cb destp), <- (cl_ulong_uncompr Tsh _ v_olen).
    sep_apply (cl_ig_to gv).
    forward_call (gv, Ews, smallp, Zlength src - 1, Zrepeat Vundef (Zlength src - 1), Zlength src - 1, v_olen,
                  true, true, Ews, destp, cb, dc, out, Ers, Ers).
    { cancel. }
    { repeat split; try list_solve; auto; try lia. }
    Intros vret. destruct vret as [[[r3 slen3] dlen3] out3]. simpl fst in *; simpl snd in *.
    match goal with H: uncompress_rel _ _ _ _ _ _ |- _ => rename H into Hu3 end.
    destruct (uf_short UF src out r3 slen3 dlen3 out3 Hok ltac:(rep_lia) ltac:(rep_lia) Hu3) as [Hm3 | (Hr3 & Hd3)].
    { subst r3. forward. forward_if. { ret0. } { exfalso. auto. } }
    subst r3.
    forward. cl_law. sep_apply (cl_ig_from gv).
    forward_if.
    { discriminate. }
    Intros.
    pose proof (cl_unc_dlen _ _ _ _ _ _ Hu3 ltac:(lia)) as Hd3'.
    ifpost _t'23 (Int.repr 1).
    { forward. forward. entailer!. simpl. unfold Int64.ltu.
      rewrite !Int64.unsigned_repr by rep_lia.
      destruct (zlt _ _); [lia | reflexivity]. }
    { exfalso. match goal with H: Int.repr Z_BUF_ERROR <> _ |- _ => apply H; reflexivity end. }
    forward_call (Int.repr 1).
    entailer!. }
  { forward. entailer!. }
  (* the prefix: gp_assume(k < dlen); uncompress(out, &olen, dest, k) *)
  forward.
  forward_call (Int.repr (if k <? Zlength out then 1 else 0)).
  { entailer!. simpl. unfold Int64.ltu. rewrite !Int64.unsigned_repr by rep_lia.
    destruct (zlt _ _), (Z.ltb_spec k (Zlength out)); try lia; reflexivity. }
  assumed. match goal with H: (k <? _) = true |- _ => apply Z.ltb_lt in H; rename H into Hk end.
  forward.
  rewrite Int.unsigned_repr by rep_lia.
  rewrite <- (cl_bytes_uncompr Ews (Zlength src) _ outp), <- (cl_tok_uncompr Ews (Zlength src) outp),
    <- (cl_bytes_uncompr Ews cb _ destp), <- (cl_tok_uncompr Ews cb destp), <- (cl_ulong_uncompr Tsh _ v_olen).
  sep_apply (cl_ig_to gv).
  forward_call (gv, Ews, outp, Zlength src, map (fun b : Z => Vint (Int.repr b)) src, Zlength src, v_olen, true, true,
                Ews, destp, cb, dc, sublist 0 k out, Ers, Ers).
  { entailer!. simpl. rewrite Zlength_sublist by lia. rewrite Z.sub_0_r, Int.unsigned_repr by rep_lia. reflexivity. }
  { cancel. }
  { assert (Zlength (sublist 0 k out) = k) by (rewrite Zlength_sublist; lia).
    split; [list_solve | ]. split; [lia | ]. split.
    - rewrite H14. rewrite <- (sublist_sublist00 k (Zlength out) dc) by lia. rewrite Hdc0.
      unfold byte_vals. rewrite sublist_map. reflexivity.
    - apply Forall_sublist. exact Hob. }
  Intros vret. destruct vret as [[[r4 slen4] dlen4] out4]. simpl fst in *; simpl snd in *.
  match goal with H: uncompress_rel _ _ _ _ _ _ |- _ => rename H into Hu4 end.
  destruct (uf_prefix UF src out k r4 slen4 dlen4 out4 Hok ltac:(rep_lia) ltac:(rep_lia) ltac:(lia) Hu4)
    as [Hm4 | Hr4].
  { subst r4. forward_if. { ret0. } { exfalso. auto. } }
  forward_if.
  { exfalso. unfold Z_DATA_ERROR, Z_BUF_ERROR in Hr4.
    match goal with H: Int.repr r4 = _ |- _ =>
      destruct Hr4 as [-> | ->]; apply (f_equal Int.signed) in H; vm_compute in H; discriminate H end. }
  ifpost _t'25 (Int.repr 1).
  { forward. entailer!. }
  { forward. entailer!. unfold Z_DATA_ERROR, Z_BUF_ERROR in Hr4.
    destruct Hr4 as [-> | ->]; [ exfalso; auto | reflexivity ]. }
  forward_call (Int.repr 1).
  ret0.
Qed.

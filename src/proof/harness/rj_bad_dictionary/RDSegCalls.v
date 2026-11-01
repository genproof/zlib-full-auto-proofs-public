(* Law rj_bad_dictionary, main (RDMain.v), statements 17-19: offer(&strm, stream, clip(stream_len), out,
   room), inflate() on the bytes offered (the theory: Z_NEED_DICT), inflateSetDictionary (Z_DATA_ERROR), return 0 *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.SpecW.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.proof.adler32.Spec.
Require Import Zlib.proof.harness.rj_bad_dictionary.RDLawCS.
Require Import Zlib.proof.harness.rj_bad_dictionary.RDGlobals.
Require Import Zlib.proof.harness.rj_bad_dictionary.RDFacts.
Require Import Zlib.proof.harness.rj_bad_dictionary.RDKit.
Require Import Zlib.harness.rj_bad_dictionary.code.
Local Open Scope Z_scope.

Lemma seg_calls_ok : seg_calls_stmt.
Proof.
  intros TH Espec gv v_strm t1 t2 room dlen streamp s3 outp dictp dict cinfo x sp.
  unfold rd_seg17, rd_A17, POST_B, POST_rd, t_zsl. abbreviate_semax.
  Intros. rename H7 into H15, H6 into Hne, H3 into Ns, H4 into No, H5 into Nd, Pv_strm into Ps.
  rename H2 into H6', H1 into H5'.
  destruct H0 as (Hs3 & Hb3 & H7 & Hx & S30 & S31).
  destruct H as (H & H0 & H1 & H2). rename H5' into H5, H6' into H6.
  assert (Ns': v_strm <> nullval) by (destruct v_strm; try contradiction; discriminate).
  destruct (rbd_init_facts sp (8 + t1) ltac:(lia)) as (Wok & Wrap & Hd).
  set (L := init_live sp (8 + t1)) in *.
  forward_call (6 + t2).
  set (c := Z.min (6 + t2) Int.max_unsigned).
  assert (Hcr: 6 <= c <= Int.max_unsigned) by (unfold c; rep_lia).
  forward_call (v_strm, Tsh, streamp, c, outp, room, nullval, Vint (Int.repr 0), Vlong (Int64.repr 0), nullval,
                Vint (Int.repr 0), Vlong (Int64.repr 0), nullval, l_sp L, gv Zlib.inflate.code._zcalloc,
                gv Zlib.inflate.code._zcfree, nullval, Vint (Int.repr 0), Vlong (Int64.repr 1), Vundef).
  sep_apply (rbd_istream_fold gv v_strm L streamp c outp room H15 ltac:(rep_lia) ltac:(rep_lia)).
  set (z := ZF streamp c 0 outp room 0 None 0 1 Vundef).
  assert (Zok: zf_ok z) by (unfold zf_ok, z; simpl; rep_lia).
  (* inflate(&strm, (int) nondet_u32()) on the bytes offered, inp, then the theory of that call *)
  set (inp := sublist 0 c s3).
  assert (Li: Zlength inp = c) by (unfold inp; rewrite Zlength_sublist by rep_lia; lia).
  assert (I0: Znth 0 inp = rbd_b0 cinfo) by (unfold inp; rewrite Znth_sublist by lia; exact S30).
  assert (I1: Znth 1 inp = rbd_b1 cinfo x) by (unfold inp; rewrite Znth_sublist by lia; exact S31).
  assert (Iid: rbd_dictid inp = rbd_dictid s3) by (unfold inp, rbd_dictid; rewrite !Znth_sublist by lia; reflexivity).
  assert (Ib: is_bytes inp) by (unfold inp, is_bytes in *; apply Forall_sublist; exact Hb3).
  assert_PROP (isptr streamp) as Pst by entailer!.
  assert_PROP (isptr outp) as Pou by entailer!.
  forward_call tt. Intros u.
  set (ib := InBuf Ews streamp 0 (6 + t2) (bytes_rep s3)).
  set (o := OutBuf Ews outp 0 room (Zrepeat Vundef room)).
  sep_apply (rbd_bufs_pre L streamp (6 + t2) (bytes_rep s3) outp room ltac:(lia)).
  fold ib o.
  assert (RL: raw_live (Some L) = false) by (unfold raw_live; rewrite Wrap; reflexivity).
  forward_call (gv, Tsh, v_strm, z, Vundef, Some L, ib, inp, Some o, Int.signed (Int.repr u), Ers, Ers, true, true).
  { entailer!. simpl. rewrite Int.repr_signed. reflexivity. }
  { unfold istreamA_opt, is_live. rewrite !if_false by auto. rewrite istreamA_istream by exact RL.
    simpl head_opt. unfold head_mem. rewrite Hd. cancel. }
  { unfold ib, o, z; simpl.
    assert (OZ: forall q, isptr q -> q = offset_val (0 + 0) q)
      by (intros q Q; destruct q; try contradiction; simpl; rewrite Ptrofs.add_zero; reflexivity).
    assert (LB: Zlength (bytes_rep s3) = 6 + t2) by (unfold bytes_rep; rewrite Zlength_map; lia).
    unfold in_ok, out_ok. rewrite LB, Zlength_Zrepeat, Li by lia.
    repeat match goal with |- _ /\ _ => split end; auto with share; try rep_lia.
    rewrite Z.add_0_l. unfold inp, bytes_rep. rewrite sublist_map. reflexivity.
    apply (rbd_init_swfW sp (8 + t1)); lia. }
  Intros vret. destruct vret as [[[r z'] st'] ow]. simpl fst in *; simpl snd in *.
  match goal with Hr: raw_live st' = raw_live (Some L) |- _ => rewrite RL in Hr; rename Hr into RL' end.
  match goal with Hr: inflate_rel _ _ _ _ _ _ _ _ _ _ _ |- _ => rename Hr into Hrel end.
  destruct (TH (8 + t1) cinfo x inp (Int.signed (Int.repr u)) v_strm sp z ib o r z' st' ow
              ltac:(lia) ltac:(lia) Hx Ib ltac:(rep_lia) I0 I1 Ns' ltac:(discriminate) Zok ltac:(simpl; lia) Hrel)
    as [Er [L' [Est SD]]].
  subst r st'.
  (* gp_assert(r == Z_NEED_DICT): the theory *)
  forward_call (Int.repr 1).
  (* inflateSetDictionary(&strm, dict, dict_len): the dictionary's Adler-32 is not DICTID *)
  assert_PROP (isptr dictp) as Pd by entailer!.
  rewrite <- (rbd_bytes_inflate_cs Ews dlen (bytes_rep dict) dictp), <- (rbd_tok_inflate_cs Ews dlen dictp).
  forward_call (gv, Tsh, v_strm, z', Vundef, Some L', Ews, dictp, 0, dlen, bytes_rep dict, dict, true).
  { entailer!. simpl. rewrite Int64.Z_mod_modulus_eq, Z.mod_small by rep_lia. reflexivity. }
  { split; [unfold bytes_rep; rewrite Zlength_map; lia | ].
    rewrite sublist_same; auto. unfold bytes_rep; rewrite Zlength_map; lia. }
  Intros vret. destruct vret as [aok winp]. simpl fst in *; simpl snd in *.
  assert (Hc: setdict_check (l_s L') dict = SDData)
    by (apply SD; rewrite Iid; exact Hne).
  replace (on_live v_strm z' (Some L') (setdict_f dict aok winp)) with (Z_DATA_ERROR, z', Some L')
    by (unfold on_live, is_live, setdict_f; rewrite if_false by auto; rewrite Hc; reflexivity).
  unfold fst3, snd3, thd3. simpl fst. simpl snd.
  (* gp_assert(... == Z_DATA_ERROR), return 0 *)
  forward_call (Int.repr 1).
  unfold istreamA_opt. rewrite if_false by auto. rewrite istreamA_istream by exact RL'. sep_apply rbd_istream_undef.
  rbd_ret.
Qed.

(* Law inflate_dict, main: the inflate half (after `slen = w.len`: inflateInit2, the raw dictionary, the loop of
   inflate() calls with the Z_NEED_DICT branch and the inflateGetDictionary checks, inflateEnd), from enc_done
   (ITMainKit.v), for ANY invariant I with the facts of ITFacts.v. *)
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
               Zlib.proof.harness.inflate_dict.ITFacts Zlib.proof.harness.inflate_dict.ITMainKit.
Require Import Zlib.harness.x_inflate_dict.code.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.harness.inflate_dict.ITMainInfKit Zlib.proof.harness.inflate_dict.ITBytes
               Zlib.proof.harness.inflate_dict.ITMainInfPre Zlib.proof.harness.inflate_dict.ITMainInfCall
               Zlib.proof.harness.inflate_dict.ITMainInfNd Zlib.proof.harness.inflate_dict.ITMainInfElse
               Zlib.proof.harness.inflate_dict.ITMainInfWin.

(* ---------------------------------------------------------------------------------------------- *)
(* Helpers of the init part (as inflate_check/IKMain.v, inflate_codes/MainHelp.v)                  *)

Lemma itm_tschar_cs sh n (v: list val) q:
  @data_at Zlib.units.Inflate.CS sh (tarray tschar n) v q = @data_at CS sh (tarray tschar n) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_inflate); [apply JMeq_refl | reflexivity]. Qed.

Definition itm_hver : list val := map (fun c => Vint (Int.repr c)) [49; 46; 51; 46; 50; 0].

Lemma itm_hver_lit gv:
  it_hversion_lit gv =
  @data_at Zlib.units.Inflate.CS Ers (tarray tschar (Zlength itm_hver)) itm_hver
    (gv Zlib.harness.x_inflate_dict.code.___stringlit_x_inflate_dict_1).
Proof. unfold it_hversion_lit. rewrite (itm_tschar_cs Ers (Zlength itm_hver)). reflexivity. Qed.

(* a stream left by a failed inflateInit2_ is the local variable's memory *)
Lemma itm_init_fail_mem gv vs r msgv stv opq ret sp w:
  isptr vs -> ret <> Z_OK ->
  init_mem gv Tsh vs r msgv stv opq ret sp w |-- @data_at_ CS Tsh (Tstruct _z_stream_s noattr) vs.
Proof.
  intros P Hr. unfold init_mem.
  destruct (eq_dec vs nullval); [subst; contradiction | ].
  destruct (ret =? Z_VERSION_ERROR); [unfold raw_strm; apply it_strm_to_undef | ].
  destruct (ret =? Z_MEM_ERROR); [unfold raw_strm; apply it_strm_to_undef | ].
  destruct (Z.eqb_spec ret Z_OK); [contradiction | ].
  unfold raw_strm; apply it_strm_to_undef.
Qed.

(* the stream after a successful inflateInit2_ *)
Definition itm_z_init (adl rs: Z) (L: live) : zfields :=
  ZF nullval 0 0 nullval 0 0 None 0 (if i_wrap (l_s L) =? 0 then adl else Z.land (i_wrap (l_s L)) 1)
     (Vlong (Int64.repr rs)).

Lemma itm_z_init_ok adl rs L: 0 <= adl <= Int64.max_unsigned -> zf_ok (itm_z_init adl rs L).
Proof.
  intros A. unfold zf_ok, itm_z_init; simpl. split; [rep_lia | ]. split; [rep_lia | ]. split; [rep_lia | ].
  split; [rep_lia | ]. split; [rep_lia | ].
  destruct (i_wrap (l_s L) =? 0); [auto | ].
  assert (M: Z.land (i_wrap (l_s L)) 1 = i_wrap (l_s L) mod 2) by (apply (Z.land_ones _ 1); lia).
  rewrite M. pose proof (Z.mod_pos_bound (i_wrap (l_s L)) 2 ltac:(lia)). rep_lia.
Qed.

Lemma itm_init_istream gv vs tin tout adl dt rs L:
  0 <= adl <= Int64.max_unsigned ->
  istream_raw gv Tsh vs
    (raw_after_init (RF nullval (Vint (Int.repr 0)) (Vlong (Int64.repr tin)) nullval (Vint (Int.repr 0))
       (Vlong (Int64.repr tout)) (Vint (Int.repr dt)) (Vlong (Int64.repr adl)) (Vlong (Int64.repr rs))) (l_s L)) L
  = istream gv Tsh vs (itm_z_init adl rs L) (Some L).
Proof.
  intros A. rewrite <- istream_raw_istream.
  - unfold raw_after_init, itm_z_init; simpl. f_equal. f_equal. destruct (i_wrap (l_s L) =? 0); reflexivity.
  - apply itm_z_init_ok; auto.
  - reflexivity.
Qed.

Lemma itm_init_ret (vs: val) w a: isptr vs ->
  init_ret vs 49 112 w a = if a then (if wbits_ok w then Z_OK else Z_STREAM_ERROR) else Z_MEM_ERROR.
Proof.
  intros P. unfold init_ret, sizeof_z_stream. simpl.
  rewrite if_false by (destruct vs; try contradiction; discriminate). destruct a; reflexivity.
Qed.

Ltac itm_fail := forward; Exists (Int.repr 0);
  match goal with Ps: isptr ?vs |- context [init_mem ?gv _ _ ?rr _ _ _ ?ret ?sp ?w] =>
    sep_apply (itm_init_fail_mem gv vs rr Vundef Vundef nullval ret sp w Ps ltac:(discriminate)) end;
  entailer!.

Ltac ifpostv t v := match goal with |- semax _ (PROPx _ (LOCALx ?Q (SEPx ?R))) _ _ =>
  forward_if (PROPx [] (LOCALx (temp t v :: Q) (SEPx R))) end.
Ltac csig := repeat match goal with H: context [Int.signed {| Int.intval := ?v; Int.intrange := ?r |}] |- _ =>
  change (Int.signed {| Int.intval := v; Int.intrange := r |}) with v in H end;
  repeat match goal with |- context [Int.signed {| Int.intval := ?v; Int.intrange := ?r |}] =>
  change (Int.signed {| Int.intval := v; Int.intrange := r |}) with v end.
Ltac isel_case := csig; repeat match goal with |- context [?a <? ?b] => destruct (Z.ltb_spec a b) end;
  first [reflexivity | exfalso; lia
        | unfold Int.add; simpl Int.unsigned; rewrite (Int.unsigned_repr (g_wb _)) by rep_lia; reflexivity].
Ltac gpa := forward_call (Int.repr 1); [ solve [entailer!; try reflexivity] .. | ].
Ltac show := match goal with |- semax _ ?P _ _ => fail 100 "PRE" P | |- ?G => fail 100 "GOAL" G end.

(* ---------------------------------------------------------------------------------------------- *)
(* One iteration of the loop: the parts, then seg_L4 (the three free()s, `if (r == 1) break;`)        *)

Lemma itm_L4_ok {Espec: OracleKind} I gv vw vs vosn vdl dictp badp datap srcp G wsel dcont scont Fr
    pos lim opos dset r z L ain aout ibp obp q ic oc qc :
  it_glob I G dictp badp datap srcp wsel dcont scont ->
  it_mid2_facts I G pos lim opos dset r z L ain aout ibp obp q ic oc qc ->
  semax Delta_m
    (it_mid2 gv vw vs vosn vdl dictp badp datap srcp G wsel dcont scont Fr pos lim opos dset r z L
       ain aout ibp obp q ic oc qc)
    seg_L4
    (it_PL (it_inv_a I gv vw vs vosn vdl dictp badp datap srcp G wsel dcont scont Fr)
           (it_brk gv vw vs vosn vdl dictp badp datap srcp G wsel dcont scont Fr)).
Proof.
  intros GL MF.
  destruct MF as (Hend & Hnend & Hpos & Hlim & Hopos & Hr & LOK & ZOK & Hain & Haout & Hic & Hoc & Hqc & Pib & Pob & Pq).
  unfold it_mid2, seg_L4, it_PL, Delta_m, Gmain_k. simplify_func_tycontext. abbreviate_semax.
  forward_call (tarray tuchar ain, ibp, gv).
  { rewrite if_false by (destruct ibp; try contradiction; discriminate).
    sep_apply (data_at_data_at_ Ews (tarray tuchar ain)). cancel. }
  forward_call (tarray tuchar aout, obp, gv).
  { rewrite if_false by (destruct obp; try contradiction; discriminate).
    sep_apply (data_at_data_at_ Ews (tarray tuchar aout) oc obp). cancel. }
  forward.
  forward_call (tarray tuchar aout, q, gv).
  { rewrite if_false by (destruct q; try contradiction; discriminate).
    sep_apply (data_at_data_at_ Ews (tarray tuchar aout) qc q). cancel. }
  forward_if.
  { assert (Er: r = Z_STREAM_END)
      by (match goal with H: Int.repr r = _ |- _ =>
            apply (f_equal Int.signed) in H; rewrite Int.signed_repr in H by rep_lia; csig; exact H end).
    destruct (Hend Er) as (Eo & Ep & _).
    forward. unfold it_brk. Exists pos lim opos dset z L. entailer!. }
  { assert (Er: r <> Z_STREAM_END)
      by (intro X; subst r; match goal with H: Int.repr _ <> _ |- _ => apply H; reflexivity end).
    pose proof (Hnend Er) as HI.
    forward. unfold it_inv_a. Exists pos lim opos dset z L. entailer!. }
Qed.

Lemma itm_loop_ok {Espec: OracleKind} I gv vw vs vosn vdl dictp badp datap srcp G wsel dcont scont Fr
    pos lim opos dset z L :
  it_glob I G dictp badp datap srcp wsel dcont scont ->
  I G pos opos dset false z L -> pos <= lim <= Zlength (it_src G) ->
  semax Delta_m (it_at gv vw vs vosn vdl dictp badp datap srcp G wsel dcont scont Fr pos lim opos dset z L)
    seg_loop
    (it_PL (it_inv_a I gv vw vs vosn vdl dictp badp datap srcp G wsel dcont scont Fr)
           (it_brk gv vw vs vosn vdl dictp badp datap srcp G wsel dcont scont Fr)).
Proof.
  intros GL HI Hl.
  apply (it_pre I gv vw vs vosn vdl dictp badp datap srcp G wsel dcont scont Fr); auto.
  intros lim' aout flush ibp obp q bs BF.
  apply (it_call I gv vw vs vosn vdl dictp badp datap srcp G wsel dcont scont Fr); auto.
  intros r pos2 made z' L' ow cont MF.
  destruct (Z.eq_dec r Z_NEED_DICT) as [En | En].
  - apply (it_nd I gv vw vs vosn vdl dictp badp datap srcp G wsel dcont scont Fr _ _ pos lim' opos dset aout
             ibp obp q bs r pos2 made z' L' ow cont); auto.
    intros opos3 dset3 r3 z3 L3 MF2.
    apply (it_win_ok I); auto. eapply itm_L4_ok; eauto.
  - apply (it_else I gv vw vs vosn vdl dictp badp datap srcp G wsel dcont scont Fr _ _ pos lim' opos dset aout
             ibp obp q bs r pos2 made z' L' ow cont); auto.
    intros opos3 dset3 r3 z3 L3 MF2.
    apply (it_win_ok I); auto. eapply itm_L4_ok; eauto.
Qed.

Lemma main_inf {Espec: OracleKind} (I: it_inv) : main_inf_stmt I.
Proof.
  intros IF gv vw vs vosn vdl dictp badp datap srcp G isel wsel dcont scont _.
  unfold enc_done, seg_inf, Delta_m, Gmain_k, POST_m. simplify_func_tycontext. abbreviate_semax.
  Intros.
  match goal with H: it_ok G |- _ => rename H into Hok end.
  match goal with H: g_iw G = _ |- _ => rename H into Hiw end.
  assert (Hok' := Hok). destruct Hok' as (Hwb & Hfl & Hdl & Hnd & Hsl & Hbs & Hsok & Hiwok).
  ifpostv _t'31 (Vint (Int.repr (g_iw G))).
  { assert (EZ: g_zlib G = false) by (destruct (g_zlib G); [apply (f_equal Int.unsigned) in H; vm_compute in H; discriminate | reflexivity]).
    forward.
    { entailer!. change (Int.signed Int.zero) with 0. rep_lia. }
    entailer!. rewrite Hiw, EZ. unfold iw_of. try rewrite Int.neg_repr. reflexivity. }
  { assert (EZ: g_zlib G = true) by (destruct (g_zlib G); [reflexivity | contradiction H; reflexivity]).
    forward_if.
    { forward. forward. entailer!. rewrite Hiw, EZ. unfold iw_of. isel_case. }
    forward_if.
    { forward. forward. forward. entailer!. rewrite Hiw, EZ. unfold iw_of. isel_case. }
    { forward. { entailer!. csig. rep_lia. } forward. forward. entailer!. rewrite Hiw, EZ. unfold iw_of. isel_case. } }
  forward.
  rewrite (it_strm_undef_cs Tsh vs). unfold it_strm_undef.
  forward_call (vs, Tsh, Vundef, Vundef).
  Intros vv. destruct vv as [[[[tin tout] adl] dt] rs]. simpl fst in *. simpl snd in *.
  set (rr := RF nullval (Vint (Int.repr 0)) (Vlong (Int64.repr tin)) nullval (Vint (Int.repr 0))
               (Vlong (Int64.repr tout)) (Vint (Int.repr dt)) (Vlong (Int64.repr adl)) (Vlong (Int64.repr rs))).
  assert_PROP (isptr vs) as Pvs by entailer!.
  match goal with |- context [@data_at ?cs Tsh t_strm ?v vs] =>
    replace (@data_at cs Tsh t_strm v vs)
      with (if eq_dec vs nullval then emp else raw_strm gv Tsh vs rr Vundef Vundef nullval nullval nullval)
      by (destruct (eq_dec vs nullval) as [X|_]; [rewrite X in Pvs; destruct Pvs | reflexivity]) end.
  rewrite itm_hver_lit.
  assert_PROP (isptr (gv Zlib.harness.x_inflate_dict.code.___stringlit_x_inflate_dict_1)) as Pver by entailer!.
  assert (Hiwr: Int.min_signed <= g_iw G <= Int.max_signed)
    by (destruct (g_zlib G); [destruct Hiwok as [E|[E|E]]; rewrite E; rep_lia | rewrite Hiwok; rep_lia]).
  forward_call (gv, Tsh, vs, rr, Vundef, Vundef, nullval, g_iw G,
                gv Zlib.harness.x_inflate_dict.code.___stringlit_x_inflate_dict_1, Ers, itm_hver, 49, 112).
  { repeat match goal with |- _ /\ _ => split end; try exact Pver; change (Zlength itm_hver) with 6; rep_lia. }
  Intros vret. destruct vret as [alloc_ok sp]. simpl fst in *. simpl snd in *.
  rewrite (itm_init_ret vs (g_iw G) alloc_ok Pvs).
  destruct alloc_ok; [destruct (wbits_ok (g_iw G)) eqn:WOK | ].
  2: { forward_if; [ itm_fail | discriminate ]. }
  2: { forward_if; [ itm_fail | discriminate ]. }
  forward_if.
  { discriminate. }
  unfold init_mem. destruct (eq_dec vs nullval) as [X|_]; [rewrite X in Pvs; destruct Pvs | ].
  remember (init_live sp (g_iw G)) as L0 eqn:HL0. subst rr.
  change (Z_OK =? Z_VERSION_ERROR) with false. change (Z_OK =? Z_MEM_ERROR) with false.
  change (Z_OK =? Z_OK) with true. cbv iota zeta.
  rewrite (itm_init_istream gv vs tin tout adl dt rs L0) by auto.
  rewrite <- itm_hver_lit.
  assert_PROP (live_ok L0 /\ zf_ok (itm_z_init adl rs L0)) as LZ by (unfold istream; entailer!).
  destruct LZ as [LOK ZOK].
  forward.
  assert (Hsp: isptr sp) by auto.
  forward_if (EX dset: bool, EX z: zfields, EX L: live,
    PROP (I G 0 0 dset false z L)
    LOCAL (temp _dict_set (Vint (Int.repr (if dset then 1 else 0)));
           temp _zlib (Vint (Int.repr (if g_zlib G then 1 else 0))); temp _wsel (Vint (Int.repr wsel));
           temp _dlen (Vint (Int.repr (Zlength (g_dict G)))); temp _dict dictp;
           temp _bad badp; temp _blen (Vint (Int.repr (Zlength (it_bad G))));
           temp _dictid (Vlong (Int64.repr (it_dictid G)));
           temp _data datap; temp _src srcp;
           temp _n (Vint (Int.repr (Zlength (it_data G))));
           temp _maxd (Vint (Int.repr (2 ^ g_wb G)));
           temp _slen (Vint (Int.repr (Zlength (it_src G))));
           lvar _w (Tstruct _bw noattr) vw; lvar _s (Tstruct _z_stream_s noattr) vs;
           lvar _osnap (tptr tuchar) vosn; lvar _dl tuint vdl; gvars gv)
    SEP (istream gv Tsh vs z (Some L); it_hversion_lit gv; version_lit gv; mem_mgr gv; zfuncs gv;
         tables_rep Ers gv; crc_table_at Ers gv; dref_tabs gv Ers it_tabs;
         malloc_token Ews (tarray tuchar (Zlength (g_dict G))) dictp;
         data_at Ews (tarray tuchar (Zlength (g_dict G))) (bytes_rep (g_dict G)) dictp;
         malloc_token Ews (tarray tuchar (Zlength (it_bad G))) badp;
         data_at Ews (tarray tuchar (Zlength (it_bad G))) (bytes_rep (it_bad G)) badp;
         malloc_token Ews (tarray tuchar (2 ^ 18)) datap; data_at Ews (tarray tuchar (2 ^ 18)) dcont datap;
         malloc_token Ews (tarray tuchar (2 ^ 19)) srcp; data_at Ews (tarray tuchar (2 ^ 19)) scont srcp;
         data_at_ Tsh (Tstruct _bw noattr) vw; data_at_ Tsh (tptr tuchar) vosn; data_at_ Tsh tuint vdl)).
  { (* raw: inflateSetDictionary(&s, dict, dlen) *)
    assert (EZ: g_zlib G = false)
      by (destruct (g_zlib G); [match goal with H: Int.repr 1 = _ |- _ => apply (f_equal Int.unsigned) in H; vm_compute in H; discriminate end | reflexivity]).
    rewrite <- (it_bytes_inflate_cs Ews (Zlength (g_dict G))), <- (it_tok_inflate_cs Ews (Zlength (g_dict G))).
    forward_call (gv, Tsh, vs, itm_z_init adl rs L0, Some L0, Ews, dictp, 0, Zlength (g_dict G),
                  bytes_rep (g_dict G), g_dict G, true).
    { rewrite it_istream_opt by auto. cancel. }
    { repeat match goal with |- _ /\ _ => split end; auto; try rep_lia; try (intros; reflexivity).
      all: unfold bytes_rep; rewrite ?Zlength_map; auto.
      rewrite sublist_same; [reflexivity | lia | rewrite Zlength_map; lia]. }
    Intros vret. destruct vret as [aok winp]. simpl fst; simpl snd.
    rewrite it_on_live by auto.
    pose proof (it_raw I IF G (itm_z_init adl rs L0) sp aok winp Hok EZ WOK Hsp ZOK eq_refl eq_refl
                  ltac:(first [exact LOK | rewrite <- HL0; exact LOK | subst; exact LOK])) as RAW.
    try rewrite <- HL0 in RAW.
    destruct (setdict_f (g_dict G) aok winp (itm_z_init adl rs L0) L0) as [[r z'] L'] eqn:E.
    unfold fst3, snd3, thd3; cbv beta iota. destruct RAW as [Hr HI'].
    rewrite it_istream_opt by auto.
    rewrite (it_bytes_inflate_cs Ews (Zlength (g_dict G))), (it_tok_inflate_cs Ews (Zlength (g_dict G))).
    forward_if.
    { forward. Exists (Int.repr 0). sep_apply it_istream_to_undef. entailer!. }
    assert (r = Z_OK) by (destruct Hr; auto; subst; contradiction). subst r.
    gpa.
    forward.
    Exists true z' L'. entailer!. apply derives_refl. }
  { (* zlib *)
    assert (EZ: g_zlib G = true)
      by (destruct (g_zlib G); [reflexivity | match goal with H: Int.repr _ <> Int.zero |- _ => contradiction H; reflexivity end]).
    forward.
    try subst L0.
    assert (HI0: I G 0 0 false false (itm_z_init adl rs (init_live sp (g_iw G))) (init_live sp (g_iw G)))
      by (apply (it_init I IF); auto).
    Exists false (itm_z_init adl rs (init_live sp (g_iw G))) (init_live sp (g_iw G)). entailer!.
    }
  Intros dset z0 L0'.
  forward. forward. forward.
  gather_SEP (it_hversion_lit gv) (version_lit gv) (dref_tabs gv Ers it_tabs).
  set (Fr := (it_hversion_lit gv * version_lit gv * dref_tabs gv Ers it_tabs)%logic).
  assert (GL: it_glob I G dictp badp datap srcp wsel dcont scont).
  { destruct (it_bytes G Hok) as [B1 B2]. unfold it_glob. split; [exact IF | ]. split; [exact Hok | ].
    repeat split; auto; lia. }
  forward_loop (it_inv_a I gv vw vs vosn vdl dictp badp datap srcp G wsel dcont scont Fr)
    break: (it_brk gv vw vs vosn vdl dictp badp datap srcp G wsel dcont scont Fr).
  { unfold it_inv_a. Exists 0 0 0 dset z0 L0'. entailer!. }
  { unfold it_inv_a at 1. Intros pos lim opos dset1 z L.
    apply (proj1 (semax_seq_skip _ _ _ _)).
    eapply semax_pre; [ | apply (itm_loop_ok I gv vw vs vosn vdl dictp badp datap srcp G wsel dcont scont Fr
                                   pos lim opos dset1 z L); auto ].
    unfold it_at. entailer!. }
  unfold it_brk. Intros pos lim opos dset1 z L. subst pos opos.
  forward_call (Int.repr 1). { entailer!. simpl. rewrite Int.eq_true. reflexivity. }
  forward_call (Int.repr 1). { entailer!. simpl. rewrite Int.eq_true. reflexivity. }
  assert_PROP (isptr vs) as Pvs' by entailer!.
  forward_call (gv, Tsh, vs, z, Some L).
  { rewrite it_istream_opt by auto. cancel. }
  rewrite it_istream_opt by auto.
  forward. Exists (Int.repr 0). sep_apply it_istream_to_undef. entailer!.
Qed.

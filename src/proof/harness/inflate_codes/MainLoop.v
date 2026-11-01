(* Law inflate_codes, main: one iteration of the loop (the body after its leading Sskip): the nondet draws, the
   input/output objects, the branch (seg_setdict_ok / seg_inflate_ok), the three free()s, `if (stop == 0) break`. *)
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
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.harness.inflate_codes.MainSD Zlib.proof.harness.inflate_codes.MainInf
               Zlib.proof.harness.inflate_codes.MainHelp.
Require Import Zlib.proof.adler32.Ptr.

(* the loop invariant *)
Definition loop_inv (I: Z -> list Z -> Z -> Z -> Z -> zfields -> live -> Prop)
    (gv: globals) (vs vo vosn vb vdl: val) (w: Z) (srcp: val) (src: list Z) (Fr: mpred) : environ -> mpred :=
  EX pos: Z, EX final: Z, EX indict: Z, EX z: zfields, EX L: live,
  PROP (I w src pos final indict z L; 0 <= pos <= Zlength src)
  LOCAL (temp _wbits (Vint (Int.repr w)); temp _n (Vint (Int.repr (Zlength src))); temp _src srcp;
         temp _zlib_ok (Vint (Int.repr (if zlib_okb w then 1 else 0)));
         temp _pos (Vint (Int.repr pos)); temp _final (Vint (Int.repr final));
         temp _in_dict (Vint (Int.repr indict));
         lvar _dl tuint vdl; lvar _b (tarray tuchar 1) vb; lvar _osnap (tptr tuchar) vosn;
         lvar _s (Tstruct _z_stream_s noattr) vs; lvar _other (tarray tschar 2) vo; gvars gv)
  SEP (istream gv Tsh vs z (Some L); mem_mgr gv; zfuncs gv; tables_rep Ers gv; crc_table_at Ers gv;
       msg_lits gv; malloc_token Ews (tarray tuchar (Zlength src)) srcp;
       data_at Ews (tarray tuchar (Zlength src)) (bytes_rep src) srcp;
       data_at_ Tsh tuint vdl; data_at_ Tsh (tarray tuchar 1) vb; data_at_ Tsh (tptr tuchar) vosn;
       data_at_ Tsh (tarray tschar 2) vo; Fr).

Lemma ptr_adler_cs_ sh q:
  @data_at_ Zlib.units.Adler32.CS sh (tptr tuchar) q = @data_at_ CS sh (tptr tuchar) q.
Proof. unfold data_at_. apply equal_f; apply (@data_at_change_composite _ _ CC_adler32); [apply JMeq_refl | reflexivity]. Qed.
Lemma ptr_adler_cs sh (v: val) q:
  @data_at Zlib.units.Adler32.CS sh (tptr tuchar) v q = @data_at CS sh (tptr tuchar) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_adler32); [apply JMeq_refl | reflexivity]. Qed.

Ltac ifpostv t v := match goal with |- semax _ (PROPx _ (LOCALx ?Q (SEPx ?R))) _ _ =>
  forward_if (PROPx [] (LOCALx (temp t v :: Q) (SEPx R))) end.
Ltac gpa := forward_call (Int.repr 1); [ solve [entailer!; try reflexivity] .. | ].
Ltac infeas := exfalso; first [ match goal with H: ?a <> ?b |- _ => solve [apply H; reflexivity] end
                              | match goal with H: _ |- _ => solve [discriminate H] end
                              | contradiction
                              | lia ].
Ltac show := match goal with |- semax _ ?P _ _ => fail 100 "PRE" P | |- ?G => fail 100 "GOAL" G end.

Lemma seg_loop_ok {Espec: OracleKind} I gv vs vo vosn vb vdl w srcp src Fr pos final indict z L :
  codes_facts I -> wbits_ok w = true -> Int.min_signed <= w <= Int.max_signed ->
  Zlength src <= 2 ^ 24 -> is_bytes src -> isptr srcp ->
  I w src pos final indict z L -> 0 <= pos <= Zlength src ->
  semax Delta_m
    (PROP ()
     LOCAL (temp _wbits (Vint (Int.repr w)); temp _n (Vint (Int.repr (Zlength src))); temp _src srcp;
            temp _zlib_ok (Vint (Int.repr (if zlib_okb w then 1 else 0)));
            temp _pos (Vint (Int.repr pos)); temp _final (Vint (Int.repr final));
            temp _in_dict (Vint (Int.repr indict));
            lvar _dl tuint vdl; lvar _b (tarray tuchar 1) vb; lvar _osnap (tptr tuchar) vosn;
            lvar _s (Tstruct _z_stream_s noattr) vs; lvar _other (tarray tschar 2) vo; gvars gv)
     SEP (istream gv Tsh vs z (Some L); mem_mgr gv; zfuncs gv; tables_rep Ers gv; crc_table_at Ers gv;
          msg_lits gv; malloc_token Ews (tarray tuchar (Zlength src)) srcp;
          data_at Ews (tarray tuchar (Zlength src)) (bytes_rep src) srcp;
          data_at_ Tsh tuint vdl; data_at_ Tsh (tarray tuchar 1) vb; data_at_ Tsh (tptr tuchar) vosn;
          data_at_ Tsh (tarray tschar 2) vo; Fr))
    seg_loop
    (loop_nocontinue_ret_assert (loop_inv I gv vs vo vosn vb vdl w srcp src Fr)
       (overridePost (loop_inv I gv vs vo vosn vb vdl w srcp src Fr) POST_m)).
Proof.
  intros CF Wok Hw Hn Hsb Psrc HI Hpos.
  unfold seg_loop, Delta_m, Gmain_k, POST_m. simplify_func_tycontext. abbreviate_semax.
  forward_call tt. Intros nlim.
  forward_call tt. Intros aout.
  forward_call tt. Intros flu.
  forward_call tt. Intros op.
  forward_call tt. Intros innull.
  forward_call tt. Intros outnull.
  forward_call tt. Intros stop.
  assert (Ef: Int.repr flu = Int.repr (Int.signed (Int.repr flu))) by (rewrite Int.repr_signed; auto).
  rewrite Ef. clear Ef. set (flush := Int.signed (Int.repr flu)).
  assert (Hfl: Int.min_signed <= flush <= Int.max_signed) by apply Int.signed_range. clearbody flush.
  ifpost _t'26 (Int.repr (if andb (pos <=? nlim) (nlim <=? Zlength src) then 1 else 0)).
  { forward. entailer!. arg_cmp. }
  { forward. entailer!. arg_cmp. }
  forward_call (Int.repr (if andb (pos <=? nlim) (nlim <=? Zlength src) then 1 else 0)).
  assumed. apply andb_prop in E. destruct E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
  forward_call (Int.repr (if aout <=? 2 ^ 20 then 1 else 0)).
  { entailer!. arg_cmp. }
  assumed. apply Z.leb_le in E.
  forward.
  rewrite sub_repr. set (ain := nlim - pos).
  assert (Hain: 0 <= ain /\ pos + ain <= Zlength src) by (subst ain; lia). clearbody ain.
  forward_call (offset_val pos srcp, Ews, srcp, pos, Zlength src, bytes_rep src, ain,
                sublist pos (pos + ain) src, gv).
  { rewrite bytes_adler_cs. cancel. }
  { apply cbuf_ok_slice; auto; lia. }
  Intros ibp.
  forward_call (aout, vosn, Tsh, gv).
  { rewrite ptr_adler_cs_. cancel. }
  Intros vret. destruct vret as [[obp q] bs]. simpl fst in *. simpl snd in *.
  rewrite ptr_adler_cs.
  match goal with Hb: Zlength bs = aout |- _ => rename Hb into Hbs end. subst aout.
  destruct (eq_dec ibp nullval) as [IN|IN].
  { subst ibp.
    ifpost _t'29 (Int.repr 1). { forward. entailer!. } { infeas. }
    forward_if. { forward. Exists (Int.repr 0). sep_apply istream_to_undef. entailer!. }
    { infeas. } }
  Intros.
  destruct (eq_dec obp nullval) as [ON|ON].
  { subst obp.
    ifpost _t'29 (Int.repr 1).
    { apply (@malloc_test_eq Zlib.units.Adler32.CS _ ain); [lia | sep_apply (@data_at_data_at_ Zlib.units.Adler32.CS Ews (tarray tuchar ain)); cancel]. }
    { infeas. }
    { forward. entailer!. }
    forward_if. { forward. Exists (Int.repr 0). sep_apply istream_to_undef. entailer!. }
    { infeas. } }
  Intros.
  rewrite (bytes_adler_cs Ews ain _ ibp), (tok_adler_cs Ews ain ibp), (bytes_adler_cs Ews (Zlength bs) _ obp),
    (tok_adler_cs Ews (Zlength bs) obp), (bytes_adler_cs Ews (Zlength bs) _ q), (tok_adler_cs Ews (Zlength bs) q).
  assert_PROP (isptr obp /\ isptr ibp) as Pob by entailer!. destruct Pob as [Pob Pib].
  ifpost _t'29 (Int.repr 0).
  { infeas. }
  { forward. entailer!. destruct obp; try contradiction; reflexivity. }
  forward_if.
  { infeas. }
  set (Fr' := (data_at Tsh (tptr tuchar) q vosn * malloc_token Ews (tarray tuchar (Zlength bs)) q *
               data_at Ews (tarray tuchar (Zlength bs)) (bytes_rep bs) q * data_at_ Tsh tuint vdl *
               data_at_ Tsh (tarray tuchar 1) vb * data_at_ Tsh (tarray tschar 2) vo * Fr)%logic).
  assert (BF: br_facts I w srcp src pos final indict z L ain (Zlength bs) flush innull outnull stop ibp obp bs).
  { unfold br_facts. pose proof (Zlength_nonneg bs). split; [exact CF | ]. split; [exact HI | ].
    repeat split; auto; try lia; try rep_lia. }
  forward_if (br_post I gv vs vo vosn vb vdl w srcp src pos ain (Zlength bs) stop ibp obp Fr').
  { unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
    eapply semax_pre; [ | apply (seg_setdict_ok I gv vs vo vosn vb vdl w srcp src pos final indict z L ain
                                   (Zlength bs) flush innull outnull stop ibp obp bs Fr' (normal_ret_assert FF));
                          exact BF].
    unfold br_pre, Fr'. entailer!. }
  { unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
    eapply semax_pre; [ | apply (seg_inflate_ok I gv vs vo vosn vb vdl w srcp src pos final indict z L ain
                                   (Zlength bs) flush innull outnull stop ibp obp bs Fr' (normal_ret_assert FF));
                          exact BF].
    unfold br_pre, Fr'. entailer!. }
  unfold br_post. Intros pos' final' indict' z' L' cont. unfold Fr'. Intros.
  forward_call (tarray tuchar ain, ibp, gv).
  { rewrite if_false by auto. sep_apply (data_at_data_at_ Ews (tarray tuchar ain)). cancel. }
  forward_call (tarray tuchar (Zlength bs), obp, gv).
  { rewrite if_false by auto. sep_apply (data_at_data_at_ Ews (tarray tuchar (Zlength bs)) cont obp). cancel. }
  forward.
  assert_PROP (isptr q) as Pq by entailer!.
  forward_call (tarray tuchar (Zlength bs), q, gv).
  { rewrite if_false by (destruct q; try contradiction; discriminate).
    sep_apply (data_at_data_at_ Ews (tarray tuchar (Zlength bs)) (bytes_rep bs) q). cancel. }
  forward_if.
  { forward. unfold loop_inv. Exists pos' final' indict' z' L'. entailer!. }
  { forward. unfold loop_inv. Exists pos' final' indict' z' L'. entailer!. }
Qed.

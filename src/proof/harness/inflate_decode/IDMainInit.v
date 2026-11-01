(* Law inflate_decode, main: iw, stream_defaults, inflateInit2 (return 0 unless Z_OK), pos = lim = opos = 0: the
   head of the decode loop (the decode theory's dinv, by decode_init_stmt). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.HarnessRef
               Zlib.proof.adler32.MainLib.
Require Zlib.proof.crc32.HarnessRef.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.inflate_common.HarnessLib.
Require Import Zlib.proof.harness.inflate_common.DRefSpec.
Require Import Zlib.proof.rfc1951.Decode.
Require Import Zlib.proof.harness.inflate_decode.IDLawCS Zlib.proof.harness.inflate_decode.IDGlobals.
Require Import Zlib.harness.x_inflate_decode.code.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.harness.inflate_decode.IDMainKit.

Local Open Scope logic.

(* the stream s and the version literal at the inflate unit's compspecs (inflate_codes/MainHelp.v) *)
Definition idi_tuple : Type :=
  (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * val)))))))))))))%type.

Lemma idi_strm_cs sh (v: idi_tuple) q:
  @data_at Zlib.units.Inflate.CS sh Rep.t_strm v q = @data_at CS sh (Tstruct _z_stream_s noattr) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_inflate); [apply JMeq_refl | reflexivity]. Qed.

Definition idi_undef : idi_tuple :=
  (Vundef, (Vundef, (Vundef, (Vundef, (Vundef, (Vundef, (Vundef, (Vundef,
   (Vundef, (Vundef, (Vundef, (Vundef, (Vundef, Vundef))))))))))))).

Lemma idi_undef_cs sh q:
  @data_at_ CS sh (Tstruct _z_stream_s noattr) q = @data_at Zlib.units.Inflate.CS sh Rep.t_strm idi_undef q.
Proof. unfold data_at_. rewrite idi_strm_cs. reflexivity. Qed.

Lemma idi_strm_to_undef sh (v: idi_tuple) q:
  @data_at Zlib.units.Inflate.CS sh Rep.t_strm v q |-- @data_at_ CS sh (Tstruct _z_stream_s noattr) q.
Proof. rewrite idi_undef_cs. apply (@data_at_data_at_ Zlib.units.Inflate.CS). Qed.

Lemma idi_tschar_cs sh n (v: list val) q:
  @data_at Zlib.units.Inflate.CS sh (tarray tschar n) v q = @data_at CS sh (tarray tschar n) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_inflate); [apply JMeq_refl | reflexivity]. Qed.

Definition idi_hver : list val := map (fun c => Vint (Int.repr c)) [49; 46; 51; 46; 50; 0].

Lemma idi_hver_lit gv :
  id_hversion_lit gv =
  @data_at Zlib.units.Inflate.CS Ers (tarray tschar (Zlength idi_hver)) idi_hver (gv ___stringlit_x_inflate_decode_1).
Proof. rewrite idi_tschar_cs. reflexivity. Qed.

Lemma idi_wbits wrap wb isel : 8 <= wb <= 15 -> wbits_ok (id_iw wrap wb isel) = true.
Proof.
  intros Hwb. unfold id_iw.
  assert (E: wb = 8 \/ wb = 9 \/ wb = 10 \/ wb = 11 \/ wb = 12 \/ wb = 13 \/ wb = 14 \/ wb = 15) by lia.
  destruct (wrap =? 1), (isel <? 85), (isel <? 170), (wrap =? 2), (isel <? 128);
    destruct E as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; subst wb; reflexivity.
Qed.

Lemma idi_iw_range wrap wb isel : 8 <= wb <= 15 -> -15 <= id_iw wrap wb isel <= 47.
Proof.
  intros Hwb. unfold id_iw.
  destruct (wrap =? 1), (isel <? 85), (isel <? 170), (wrap =? 2), (isel <? 128); lia.
Qed.

Lemma idi_init_ret (vs: val) w a : isptr vs -> wbits_ok w = true ->
  init_ret vs 49 112 w a = if a then Z_OK else Z_MEM_ERROR.
Proof.
  intros P W. unfold init_ret. change sizeof_z_stream with 112. simpl.
  rewrite if_false by (intro X; subst; contradiction). rewrite W. destruct a; reflexivity.
Qed.

(* the return paths: Floyd's forward_return wants main's postcondition in overridePost form *)
Lemma idi_post {Espec: OracleKind} Delta P c Pn Pb Pc:
  semax Delta P c (overridePost Pn POST_id) ->
  semax Delta P c {| RA_normal := Pn; RA_break := Pb; RA_continue := Pc; RA_return := RA_return POST_id |}.
Proof.
  intros H. eapply semax_post; [ | | | | exact H]; intros; unfold overridePost, POST_id; simpl RA_normal;
    simpl RA_break; simpl RA_continue; simpl RA_return.
  - apply andp_left2, derives_refl.
  - apply andp_left2. unfold frame_ret_assert, function_body_ret_assert. simpl.
    intro rho. normalize.
  - apply andp_left2. unfold frame_ret_assert, function_body_ret_assert. simpl.
    intro rho. normalize.
  - apply andp_left2, derives_refl.
Qed.

(* the use of the decode theory's decode_init_stmt (the one place to port to the v2 interface) *)
Lemma id_init_use : decode_init_stmt -> forall G sp, dctx_ok G -> dc_hist G = [] ->
  (forall wb fl did, dc_w G = WZlib wb fl did -> did = None) ->
  dinv G 0 [] (l_s (init_live sp (dc_iw G))) 0.
Proof. intros DI G sp OK H N. exact (DI G sp OK H N). Qed.

(* the decode context of the run *)
Definition idi_G (wrap wb flevel isel: Z) (al: list block) (srcl: list Z) : dctx :=
  DCtx (id_wrapper wrap wb flevel) wb [] al (id_iw wrap wb isel) srcl.

Lemma idi_dctx_ok wrap wb flevel isel datap srcp isbp al ls dcont isbz srcl scont :
  trl_facts wrap wb flevel isel datap srcp isbp al ls dcont isbz srcl scont ->
  dctx_ok (idi_G wrap wb flevel isel al srcl).
Proof.
  intros (PAR & Pd & Ps & Pi & Hal & Hbo & Hdo & Hisb & Hls & Hs1 & Hs2 & Hsb & Hpre & Hsc & Hsl & Hsc2).
  destruct PAR as (Hw & Hwb & Hfl & His).
  assert (WF: wf (2 ^ wb) [] al) by (split; [auto | split; [constructor | auto]]).
  unfold dctx_ok, slen, idi_G; cbn [dc_w dc_wb dc_hist dc_bs dc_iw dc_src].
  split; [ | split; [ | split; [ | split; [ | split; [auto | split; [lia | split; [exact Hsb | exact Hpre]]]]]]].
  - unfold stream_ok, id_wrapper. split; [lia | ].
    destruct (wrap =? 1); [ | destruct (wrap =? 2)]; cbn.
    + split; [ | split; [reflexivity | exact WF]]. split; [lia | ]. split; [ | reflexivity].
      assert (M: Z.land flevel 3 = flevel mod 4) by (apply (Z.land_ones _ 2); lia).
      rewrite M. pose proof (Z.mod_pos_bound flevel 4 ltac:(lia)). lia.
    + split; [ | split; [exact I | exact WF]]. split; [ | reflexivity].
      unfold gz_ok, byte_ok, gz_min; cbn. repeat split; lia.
    + split; [exact I | split; [exact I | exact WF]].
  - unfold accepts, id_wrapper, id_iw. cbn [dc_w dc_wb dc_iw].
    destruct (wrap =? 1); [ | destruct (wrap =? 2)]; cbn.
    + destruct (isel <? 85); [ | destruct (isel <? 170)]; lia.
    + destruct (isel <? 128); lia.
    + reflexivity.
  - intros h E. unfold id_wrapper in E. destruct (wrap =? 1); [discriminate | ].
    destruct (wrap =? 2); [ | discriminate]. injection E as <-. unfold gz_simple, gz_min; cbn. auto.
  - intros wb' fl did E. unfold id_wrapper in E. destruct (wrap =? 1); [ | destruct (wrap =? 2); discriminate].
    injection E as _ _ <-. left; reflexivity.
Qed.

Lemma idi_dec_facts wrap wb flevel isel datap srcp isbp al ls dcont isbz srcl scont :
  trl_facts wrap wb flevel isel datap srcp isbp al ls dcont isbz srcl scont ->
  dec_facts (idi_G wrap wb flevel isel al srcl) datap srcp isbp dcont scont isbz ls.
Proof.
  intros TF. pose proof (idi_dctx_ok _ _ _ _ _ _ _ _ _ _ _ _ _ TF) as OK.
  destruct TF as (PAR & Pd & Ps & Pi & Hal & Hbo & Hdo & Hisb & Hls & Hs1 & Hs2 & Hsb & Hpre & Hsc & Hsl & Hsc2).
  destruct Hisb as (Hi1 & Hi2 & Hi3).
  unfold dec_facts, full, outk, nblk, idi_G; cbn [dc_w dc_wb dc_hist dc_bs dc_iw dc_src].
  split; [exact OK | ]. split; [reflexivity | ]. do 3 (split; [auto | ]).
  split; [exact Hdo | ]. do 3 (split; [auto | ]). split; [auto | ]. split; [auto | ].
  split; [exact Hi3 | ].
  rewrite Hls. rewrite removelast_firstn_len. do 3 f_equal. rewrite Zlength_correct. lia.
Qed.

(* the stream after a successful inflateInit2_ (inflate_codes/MainHelp.v) *)
Definition idi_z (adl rs: Z) (L: live) : zfields :=
  ZF nullval 0 0 nullval 0 0 None 0 (if i_wrap (l_s L) =? 0 then adl else Z.land (i_wrap (l_s L)) 1)
     (Vlong (Int64.repr rs)).

Lemma idi_init_istream gv vs tin tout adl dt rs L:
  0 <= adl <= Int64.max_unsigned ->
  istream_raw gv Tsh vs
    (raw_after_init (RF nullval (Vint (Int.repr 0)) (Vlong (Int64.repr tin)) nullval (Vint (Int.repr 0))
       (Vlong (Int64.repr tout)) (Vint (Int.repr dt)) (Vlong (Int64.repr adl)) (Vlong (Int64.repr rs))) (l_s L)) L
  = istream gv Tsh vs (idi_z adl rs L) (Some L).
Proof.
  intros A. rewrite <- istream_raw_istream.
  - unfold raw_after_init, idi_z; simpl. f_equal. f_equal. destruct (i_wrap (l_s L) =? 0); reflexivity.
  - unfold zf_ok, idi_z; simpl. split; [rep_lia | ]. split; [rep_lia | ]. split; [rep_lia | ].
    split; [rep_lia | ]. split; [rep_lia | ].
    destruct (i_wrap (l_s L) =? 0); [auto | ].
    assert (M: Z.land (i_wrap (l_s L)) 1 = i_wrap (l_s L) mod 2) by (apply (Z.land_ones _ 1); lia).
    rewrite M. pose proof (Z.mod_pos_bound (i_wrap (l_s L)) 2 ltac:(lia)). rep_lia.
  - reflexivity.
Qed.

Lemma idi_init_mem_ok gv (vs: val) r msgv stv opq sp w : isptr vs ->
  init_mem gv Tsh vs r msgv stv opq Z_OK sp w =
  istream_raw gv Tsh vs (raw_after_init r (l_s (init_live sp w))) (init_live sp w).
Proof. intros P. unfold init_mem. rewrite if_false by (intro X; subst; contradiction). reflexivity. Qed.

Ltac ifpostv t v := match goal with |- semax _ (PROPx _ (LOCALx ?Q (SEPx ?R))) _ _ =>
  forward_if (PROPx [] (LOCALx (temp t v :: Q) (SEPx R))) end.

Ltac iwt := unfold id_iw;
  repeat first [ rewrite (proj2 (Z.eqb_eq _ _)) by lia | rewrite (proj2 (Z.eqb_neq _ _)) by lia
               | rewrite (proj2 (Z.ltb_lt _ _)) by lia | rewrite (proj2 (Z.ltb_ge _ _)) by lia ];
  rewrite ?add_repr, ?Int.neg_repr; try reflexivity.

Lemma id_init_ok {Espec: OracleKind} gv vw vll vlc vdc vs vosn wrap wb flevel isel datap srcp isbp Fr
    al ls dcont isbz srcl scont (Post: ret_assert) :
  decode_init_stmt -> RA_return Post = RA_return POST_id ->
  trl_facts wrap wb flevel isel datap srcp isbp al ls dcont isbz srcl scont ->
  (forall G, dec_facts G datap srcp isbp dcont scont isbz ls ->
     semax Delta_id
       (dec_inv gv vw vll vlc vdc vs vosn G datap srcp isbp dcont scont isbz ls
          (dref_tabs gv Ers id_tabs * data_at Ers (tarray tuchar 19) (zvals clorder) (gv _cl_order) *
           version_lit gv * id_hversion_lit gv * Fr)%logic) S_dec Post) ->
  semax Delta_id (trl_mid gv vw vll vlc vdc vs vosn wrap wb flevel isel datap srcp isbp Fr al ls dcont isbz
                    srcl scont) S_mid Post.
Proof.
  intros DI HR TF Kdec. destruct Post as [Pn Pb Pc Pr]; change (Pr = RA_return POST_id) in HR; subst Pr.
  unfold S_mid, trl_mid, Delta_id, Gmain_k. simplify_func_tycontext. abbreviate_semax.
  destruct TF as (PAR & Pd & Ps & Pi & Hal & Hbo & Hdo & Hisb & Hls & Hs1 & Hs2 & Hsb & Hpre & Hsc & Hsl & Hsc2).
  pose proof PAR as (Hw & Hwb & Hfl & His).
  ifpostv _iw (Vint (Int.repr (id_iw wrap wb isel))).
  { ifpostv _t'36 (Vint (Int.repr (id_iw wrap wb isel))).
    { forward. entailer!; iwt. }
    { ifpostv _t'36 (Vint (Int.repr (id_iw wrap wb isel))).
      { forward. forward. entailer!; iwt. }
      { forward. forward. entailer!; iwt. }
      }
    forward. entailer!. }
  { ifpostv _iw (Vint (Int.repr (id_iw wrap wb isel))).
    { ifpostv _t'37 (Vint (Int.repr (id_iw wrap wb isel))).
      { forward. entailer!; iwt. }
      { forward. entailer!; iwt. }
      forward. entailer!. }
    { forward. { entailer!. rewrite Int.signed_zero. rep_lia. } entailer!; iwt. }
    }
  unfold dres. rewrite idi_undef_cs.
  forward_call (vs, Tsh, Vundef, Vundef).
  Intros vv. destruct vv as [[[[tin tout] adl] dt] rs]. simpl fst in *. simpl snd in *.
  set (rr := RF nullval (Vint (Int.repr 0)) (Vlong (Int64.repr tin)) nullval (Vint (Int.repr 0))
               (Vlong (Int64.repr tout)) (Vint (Int.repr dt)) (Vlong (Int64.repr adl)) (Vlong (Int64.repr rs))).
  assert_PROP (isptr vs) as Pvs by entailer!.
  match goal with |- context [@data_at ?cs Tsh t_strm ?v vs] =>
    replace (@data_at cs Tsh t_strm v vs)
      with (if eq_dec vs nullval then emp else raw_strm gv Tsh vs rr Vundef Vundef nullval nullval nullval)
      by (rewrite if_false by (intro X; subst; contradiction); reflexivity) end.
  rewrite idi_hver_lit.
  assert_PROP (isptr (gv ___stringlit_x_inflate_decode_1)) as Pver by entailer!.
  pose proof (idi_iw_range wrap wb isel Hwb) as Hiw.
  forward_call (gv, Tsh, vs, rr, Vundef, Vundef, nullval, id_iw wrap wb isel, gv ___stringlit_x_inflate_decode_1,
                Ers, idi_hver, 49, 112).
  { change (Zlength idi_hver) with 6. repeat split; auto; rep_lia. }
  Intros vret. destruct vret as [alloc_ok sp]. simpl fst in *. simpl snd in *.
  rewrite (idi_init_ret vs (id_iw wrap wb isel) alloc_ok Pvs (idi_wbits wrap wb isel Hwb)).
  destruct alloc_ok.
  2:{ forward_if.
      { unfold abbreviate in POSTCONDITION. subst POSTCONDITION. apply idi_post.
        forward. Exists (Int.repr 0).
        unfold init_mem. rewrite if_false by (intro X; subst; contradiction). simpl.
        unfold raw_strm. sep_apply idi_strm_to_undef. entailer!. }
      { exfalso. discriminate. } }
  forward_if.
  { exfalso. discriminate. }
  rewrite (idi_init_mem_ok gv vs rr Vundef Vundef nullval sp (id_iw wrap wb isel) Pvs).
  subst rr. rewrite idi_init_istream by auto.
  forward. forward. forward.
  set (G := idi_G wrap wb flevel isel al srcl).
  assert (DF: dec_facts G datap srcp isbp dcont scont isbz ls).
  { apply idi_dec_facts. repeat (split; auto). }
  pose proof DF as (OK & Hh & _).
  assert (DV: dinv G 0 [] (l_s (init_live sp (id_iw wrap wb isel))) 0).
  { apply (id_init_use DI G sp OK Hh). intros wb' fl did E. unfold G, idi_G, id_wrapper in E. cbn [dc_w] in E.
    destruct (wrap =? 1); [ | destruct (wrap =? 2); discriminate].
    injection E as _ _ <-. reflexivity. }
  eapply semax_pre; [ | apply (Kdec G DF)].
  unfold dec_inv, dec_at.
  Exists 0 0 0 (idi_z adl rs (init_live sp (id_iw wrap wb isel))) (init_live sp (id_iw wrap wb isel)).
  rewrite <- idi_hver_lit.
  entailer!.
Qed.

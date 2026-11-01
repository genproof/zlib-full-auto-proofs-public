(* Law rt_session: main's body against main_core_spec Rm ([SMainStmt.ses_main_stmt]), for any invariants with the
   facts of SDFacts.v and SIFacts.v.

   main is its parts in sequence (SMKit.body_parts): the draws and the objects (SMSegA1, SMSegA2), deflateInit2_
   with the dictionary or the header (SMSegA3), the deflate loop (SMLoopD), the input object (SMSegB), then, by the
   value of with_head, inflateInit2_ with a raw dictionary or inflateGetHeader (SMSegCW / SMSegC9), the inflate
   loop (SMLoopIW in the context of SpecW's inflate(), SMLoopI9 in that of RTH9Spec's, both moved here by
   [delta_ses_sub]) and the final checks (SMSegEW / SMSegE9). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.harness.rt_session.SCS.
Require Import Zlib.proof.harness.rt_session.SMainStmt.
Require Import Zlib.proof.harness.rt_session.SMKit.
Require Import Zlib.proof.harness.rt_session.SMSegA1.
Require Import Zlib.proof.harness.rt_session.SMSegA2.
Require Import Zlib.proof.harness.rt_session.SMSegA3.
Require Import Zlib.proof.harness.rt_session.SMLoopD.
Require Import Zlib.proof.harness.rt_session.SMSegB.
Require Import Zlib.proof.harness.rt_session.SMSegCW.
Require Import Zlib.proof.harness.rt_session.SMSegC9.
Require Import Zlib.proof.harness.rt_session.SMLoopIW.
Require Import Zlib.proof.harness.rt_session.SMLoopI9.
Require Import Zlib.proof.harness.rt_session.SMSegEW.
Require Import Zlib.proof.harness.rt_session.SMSegE9.
Require Import Zlib.harness.rt_session.code.
#[local] Existing Instance SCS.CS.

(** ** Moving a proof from the context of one of inflate()'s two specifications to main's *)

(* two lists of specifications with the same names, the second's each a subspecification of the first's: the
   second's type context subsumes the first's *)
Lemma mts_subsume : forall G1 G2 : funspecs,
  Forall2 (fun a b => fst a = fst b /\ funspec_sub (snd b) (snd a)) G1 G2 ->
  forall id, subsumespec (Maps.PTree.get id (make_tycontext_s G1)) (Maps.PTree.get id (make_tycontext_s G2)).
Proof.
  induction 1; intro id; simpl.
  - rewrite ?Maps.PTree.gempty; exact I.
  - destruct x as [i f], y as [j g]; simpl in *. destruct H as [<- Hs].
    rewrite !Maps.PTree.gsspec. destruct (peq id i).
    + exists g; split; [reflexivity | apply funspec_sub_sub_si; exact Hs].
    + apply IHForall2.
Qed.

Lemma mtg_same : forall (V : varspecs) (G1 G2 : funspecs),
  Forall2 (fun a b => fst a = fst b /\ funspec_sub (snd b) (snd a)) G1 G2 ->
  forall id, sub_option (Maps.PTree.get id (make_tycontext_g V G1)) (Maps.PTree.get id (make_tycontext_g V G2)).
Proof.
  intros V G1 G2 F. assert (E : make_tycontext_g V G1 = make_tycontext_g V G2).
  { induction F; simpl; auto. rewrite IHF. destruct H as [<- Hs]. f_equal.
    destruct x as [i [sig1 cc1 A1 P1 Q1 N1 M1]], y as [j [sig2 cc2 A2 P2 Q2 N2 M2]]; simpl in *.
    destruct Hs as [[<- <-] _]. reflexivity. }
  rewrite E. intro id. destruct (Maps.PTree.get id (make_tycontext_g V G2)); simpl; auto.
Qed.

(* main's context with [inf] in place of inflate()'s intersection *)
Lemma delta_ses_sub (inf : ident * funspec) :
  fst inf = _inflate -> funspec_sub inflate_fs_ses (snd inf) ->
  tycontext_sub (func_tycontext f_main (QPvarspecs p) (Gmain_of inf) nil) Delta_s.
Proof.
  intros N S.
  assert (F : Forall2 (fun a b => fst a = fst b /\ funspec_sub (snd b) (snd a)) (Gmain_of inf) Gmain).
  { unfold Gmain, Gmain_of, inflate_spec_ses.
    repeat (constructor; [split; [reflexivity | apply funspec_sub_refl] | ]).
    constructor; [split; [exact N | exact S] | ].
    repeat (constructor; [split; [reflexivity | apply funspec_sub_refl] | ]).
    constructor. }
  unfold Delta_s, func_tycontext, make_tycontext, tycontext_sub.
  cbv beta iota delta [temp_types var_types ret_type glob_types glob_specs annotations].
  split; [ | split; [ | split; [ | split; [ | split]]]].
  - intro id. destruct (Maps.PTree.get id (make_tycontext_t _ _)); auto.
  - intro id. reflexivity.
  - reflexivity.
  - apply mtg_same; exact F.
  - apply mts_subsume; exact F.
  - intro id. destruct (Maps.PTree.get id (make_tycontext_a nil)) as [[] | ]; simpl; auto.
Qed.

Lemma delta_W_sub : tycontext_sub Delta_W Delta_s.
Proof. apply delta_ses_sub; [reflexivity | apply inflate_ses_sub]. Qed.

Lemma delta_9_sub : tycontext_sub Delta_9 Delta_s.
Proof. apply delta_ses_sub; [reflexivity | apply inflate_ses_sub]. Qed.

(** ** main *)

Theorem ses_main : ses_main_stmt.
Proof.
  intros J P PN DF IF.
  start_function.
  match goal with |- semax _ _ (Ssequence _ ?r) _ =>
    apply (semax_unfold_Ssequence
             (Ssequence
                (Ssequence segA1 (Ssequence segA2 (Ssequence segA3 (Ssequence loopD (Ssequence segB
                   (Ssequence segC (Ssequence loopI segE))))))) r));
    [reflexivity | ]
  end.
  apply semax_seq with FF.
  2: { eapply semax_pre; [ | apply semax_ff]. apply andp_left2; apply derives_refl. }
  eapply semax_seq; [apply (sm_segA1 Espec gv v_head v_got v_compressor v_at v_decompressor) | ].
  Intros u.
  eapply semax_seq; [apply (sm_segA2 Espec gv v_head v_got v_compressor v_at v_decompressor u) | ].
  clear u. Intros u.
  eapply semax_seq; [apply (sm_segA3 Espec J gv v_head v_got v_compressor v_at v_decompressor u DF) | ].
  Intros l hx Hr.
  eapply semax_seq.
  { eapply semax_pre; [ | apply (sm_loopD Espec J gv v_head v_got v_compressor v_at v_decompressor u hx Hr DF)].
    apply andp_left2; apply (exp_right l); apply derives_refl. }
  Intros O c.
  eapply semax_seq; [apply (sm_segB Espec gv v_head v_got v_compressor v_at v_decompressor u O c) | ].
  Intros src ip.
  destruct (with_head u) eqn:WH.
  - eapply semax_seq;
      [apply (sm_segC_9 Espec P PN gv v_head v_got v_compressor v_at v_decompressor u O c src ip IF WH) | ].
    Intros l'.
    eapply semax_seq.
    { eapply semax_Delta_subsumption; [apply delta_9_sub | ].
      eapply semax_pre;
        [ | apply (sm_loopI_9 Espec P PN gv v_head v_got v_compressor v_at v_decompressor u O c src ip IF)].
      apply andp_left2; apply (exp_right l'); apply derives_refl. }
    Intros z L.
    eapply semax_post; [ | | | | apply (sm_segE_9 Espec gv v_head v_got v_compressor v_at v_decompressor u O c src ip z L)].
    all: intros; unfold POST_s, overridePost; simpl RA_normal; simpl RA_break; simpl RA_continue; simpl RA_return.
    all: try (apply andp_left2; apply derives_refl).
    unfold frame_ret_assert, function_body_ret_assert; simpl. go_lowerx. normalize.
  - eapply semax_seq;
      [apply (sm_segC_W Espec P PN gv v_head v_got v_compressor v_at v_decompressor u O c src ip IF WH) | ].
    Intros l'.
    eapply semax_seq.
    { eapply semax_Delta_subsumption; [apply delta_W_sub | ].
      eapply semax_pre;
        [ | apply (sm_loopI_W Espec P PN gv v_head v_got v_compressor v_at v_decompressor u O c src ip IF)].
      apply andp_left2; apply (exp_right l'); apply derives_refl. }
    Intros z L.
    eapply semax_post; [ | | | | apply (sm_segE_W Espec gv v_head v_got v_compressor v_at v_decompressor u O c src ip z L)].
    all: intros; unfold POST_s, overridePost; simpl RA_normal; simpl RA_break; simpl RA_continue; simpl RA_return.
    all: try (apply andp_left2; apply derives_refl).
    unfold frame_ret_assert, function_body_ret_assert; simpl. go_lowerx. normalize.
Qed.

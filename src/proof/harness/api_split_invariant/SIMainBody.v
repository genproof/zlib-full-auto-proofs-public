(* Law api_split_invariant, main: one iteration of the split's for(;;) (its body): rest_in, rest_out, take =
   upto(rest_in), give = upto(rest_out), any piece_flush, avail_in = take, avail_out = give, code_split =
   inflate(&split, piece_flush) (`return 0` on Z_MEM_ERROR; SIFacts.sf_call), all_offered, no_progress, may_stop,
   and the break when final(code_split) or all was offered with a flush that may stop (sm_inv -> sm_inv, or
   sm_brk at the break). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.EnvBodies.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.SpecW.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.api_split_invariant.SILawCS.
Require Import Zlib.proof.harness.api_split_invariant.SIGlobals.
Require Import Zlib.proof.harness.api_split_invariant.SIFacts.
Require Import Zlib.proof.harness.api_split_invariant.SIMainKit.
Require Import Zlib.harness.api_split_invariant.code.
Local Open Scope logic.

(* rest = len - (size_t)(p + k - p): the bytes after the first k of an object of len bytes *)
Lemma sm_rest b i n k: 0 <= k <= n -> n <= Int.max_unsigned ->
  force_val (sem_binary_operation' Osub tulong tulong (Vlong (Int64.repr n))
    (eval_cast tlong tulong (eval_binop Osub (tptr tuchar) (tptr tuchar) (offset_val k (Vptr b i)) (Vptr b i))))
  = Vlong (Int64.repr (n - k)).
Proof.
  intros Hk Hn. simpl.
  unfold sem_binary_operation', Clight_Cop2.sem_sub; simpl.
  unfold sem_sub_pp, sem_sub_default. simpl. rewrite if_true by auto. simpl.
  rewrite Ptrofs.sub_add_l, Ptrofs.sub_idem, Ptrofs.add_zero_l.
  change (Ptrofs.divs (Ptrofs.repr k) (Ptrofs.repr 1)) with (Ptrofs.divs (Ptrofs.repr k) Ptrofs.one).
  rewrite Ptrofs.divs_one by reflexivity. unfold Ptrofs.to_int64. rewrite Ptrofs.unsigned_repr by rep_lia.
  unfold Int64.sub. rewrite !Int64.unsigned_repr by rep_lia. reflexivity.
Qed.

(* the comparison of two size_t values *)
Lemma sm_cmp64 a b: 0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned ->
  Int64.eq (Int64.repr a) (Int64.repr b) = (a =? b).
Proof.
  intros Ha Hb. unfold Int64.eq. rewrite !Int64.unsigned_repr by lia.
  destruct (zeq a b), (Z.eqb_spec a b); congruence.
Qed.

(* the comparison of two int values *)
Lemma sm_cmp32 a b: Int.min_signed <= a <= Int.max_signed -> Int.min_signed <= b <= Int.max_signed ->
  Int.eq (Int.repr a) (Int.repr b) = (a =? b).
Proof.
  intros Ha Hb. unfold Int.eq. destruct (zeq _ _) as [E|E], (Z.eqb_spec a b) as [F|F]; auto.
  - apply (f_equal Int.repr) in E. rewrite !Int.repr_unsigned in E.
    apply repr_inj_signed in E; [contradiction | rep_lia | rep_lia].
  - subst b. contradiction.
Qed.

(* main's postcondition as a record of its four parts (so that the postconditions built from it reduce) *)
Lemma sm_POST_eta: POST_m = {| RA_normal := RA_normal POST_m; RA_break := RA_break POST_m;
                               RA_continue := RA_continue POST_m; RA_return := RA_return POST_m |}.
Proof. reflexivity. Qed.

(* forward_if whose join adds temp t = v to the current assertion *)
Ltac sm_ifpostv t v := sm_split_call; match goal with |- semax _ (PROPx _ (LOCALx ?Q (SEPx ?R))) _ _ =>
  forward_if (PROPx [] (LOCALx (temp t v :: Q) (SEPx R))) end.

Lemma sm_body_ok {Espec: OracleKind} Inv Max gv vwb vone vsplit w src room inp o1 o2 r1 Fr:
  si_facts Inv Max -> si_window w -> is_bytes src -> Zlength src <= Int.max_unsigned ->
  0 <= room <= Int.max_unsigned -> isptr inp -> isptr o2 ->
  Fr |-- data_at_ Tsh (tarray tint 4) vwb * data_at_ Tsh t_zsl vone * TT ->
  semax Delta_m (sm_inv Inv gv vwb vone vsplit w src room inp o1 o2 r1 Fr) sm_body
    (loop1_ret_assert (sm_inv Inv gv vwb vone vsplit w src room inp o1 o2 r1 Fr)
       (overridePost (sm_brk Max gv vwb vone vsplit w src room inp o1 o2 r1 Fr) POST_B)).
Proof.
  intros SF Hw Bs Hl Hr Pi Po HF.
  unfold sm_body, sm_loop, sm_seg29, Delta_m, Gmain_k, POST_B. simplify_func_tycontext. abbreviate_semax.
  unfold sm_inv. Intros P O z L.
  rewrite (sm_istreamA_unfold gv Tsh vsplit z Vundef L). Intros. unfold sm_tup.
  rewrite H3, H4, H5.
  destruct inp as [ | | | | | bi ii]; try contradiction. destruct o2 as [ | | | | | bo io]; try contradiction.
  forward. forward.
  forward. { entailer!. unfold sameblock. simpl. destruct (peq bi bi); [reflexivity | contradiction]. }
  rewrite sm_rest by rep_lia.
  forward.
  forward. { entailer!. unfold sameblock. simpl. destruct (peq bo bo); [reflexivity | contradiction]. }
  rewrite sm_rest by rep_lia.
  sm_split_call.
  forward_call (Zlength src - P). Intros take.
  forward.
  sm_split_call.
  forward_call (room - Zlength O). Intros give.
  forward.
  sm_split_call.
  forward_call tt. Intros u.
  forward.
  rewrite !Int64.unsigned_repr by rep_lia.
  assert (Eu: Int.repr u = Int.repr (Int.signed (Int.repr u))) by (rewrite Int.repr_signed; auto).
  rewrite Eu. clear Eu. set (flush := Int.signed (Int.repr u)).
  assert (Hfl: Int.min_signed <= flush <= Int.max_signed) by apply Int.signed_range. clearbody flush.
  forward. forward.
  set (inp := Vptr bi ii) in *. set (o2 := Vptr bo io) in *.
  set (z0 := sm_avail z take give).
  assert (Z0: zf_ok z0) by (unfold z0, sm_avail, zf_ok in *; simpl; rep_lia).
  match goal with |- context [data_at Tsh t_zsl ?v vsplit] =>
    replace v with (sm_tup gv z0 (adler_v (raw_live (Some L)) z0 Vundef) (l_sp L))
      by (unfold sm_tup, z0, sm_avail; simpl; rewrite H3, H4, H5; reflexivity) end.
  sep_apply (sm_istreamA_fold gv Tsh vsplit z0 Vundef L); auto.
  (* code_split = inflate(&split, piece_flush) *)
  set (data := sublist P (P + take) src).
  assert (Hdl: Zlength data = take) by (unfold data; rewrite Zlength_sublist; lia).
  assert (INOK: in_ok (sm_ib inp src P) data) by (apply sm_in_ok; auto; rep_lia).
  assert (OUTOK: out_ok (sm_ob o2 O room) give) by (apply sm_out_ok; auto; rep_lia).
  assert_PROP (isptr vsplit) as Pvs by entailer!.
  sep_apply (sm_bufs_pre vsplit L inp src P o2 O room); auto.
  rewrite <- (sm_istreamA_opt_ptr gv Tsh vsplit z0 Vundef (Some L)) by auto.
  replace (head_opt (Some L)) with (head_opt (is_live vsplit (Some L))) by (rewrite sm_is_live_ptr; auto).
  sm_split_call.
  forward_call (gv, Tsh, vsplit, z0, Vundef, Some L, sm_ib inp src P, data, Some (sm_ob o2 O room), flush,
                Ers, Ers, true, true).
  { split; [ | split].
    - unfold z0, sm_avail, sm_ib; simpl. rewrite Z.add_0_r. auto.
    - split; [exact INOK | unfold z0, sm_avail; simpl; lia].
    - unfold z0, sm_avail, sm_ob; simpl. rewrite Z.add_0_r. auto. }
  Intros vret. destruct vret as [[[r z'] st'] ow]. simpl fst in *; simpl snd in *.
  match goal with H: inflate_rel _ _ _ _ _ _ _ _ _ _ _ |- _ => rename H into REL end.
  pose proof (sm_inflate_ret _ _ _ _ _ _ _ _ _ _ _ REL) as Hr5.
  forward.
  forward_if.
  { forward. Exists (Int.repr 0). sep_apply (sm_a_frame_opt gv Tsh vsplit z' Vundef st' Pvs). sep_apply HF.
    entailer!. }
  (* no `return` below: let the postcondition reduce *)
  unfold POSTCONDITION, abbreviate. rewrite sm_POST_eta.
  match goal with |- semax _ _ _ ?R =>
    let R' := eval cbv beta iota delta [loop1_ret_assert overridePost] in R in change R with R' end.
  abbreviate_semax.
  assert (Hm: r <> Z_MEM_ERROR) by (intro E; subst r; contradiction).
  destruct (sf_call _ _ SF w src room P O L flush vsplit z0 (sm_ib inp src P) data (sm_ob o2 O room) r z' st' ow
              H H8 Z0 H5 ltac:(intro E; subst vsplit; contradiction) ltac:(discriminate)
              ltac:(unfold z0, sm_avail; simpl; lia) ltac:(rewrite Hdl; reflexivity) ltac:(lia)
              ltac:(unfold z0, sm_avail; simpl; lia) REL Hm)
    as (L' & Est & Hai & How & HI & Hni & Hno & Hao & Htout & Hfin & Hnf).
  subst st'.
  change (zf_ai z0) with take in *. change (zf_ao z0) with give in *.
  rewrite (sm_istreamA_opt_ptr gv Tsh vsplit z' Vundef (Some L') Pvs).
  rewrite (sm_is_live_ptr vsplit (Some L') Pvs).
  sep_apply (sm_bufs_post vsplit L inp src P o2 O room ow); auto; [lia | ].
  rewrite (sm_istreamA_unfold gv Tsh vsplit z' Vundef L'). Intros. unfold sm_tup.
  (* all_offered *)
  set (ao := andb (take =? Zlength src - P) (give =? room - Zlength O)).
  sm_ifpostv _t'19 (Vint (Int.repr (if ao then 1 else 0))).
  { rewrite Int.unsigned_repr in H17 by rep_lia. rewrite sm_cmp64 in H17 by rep_lia.
    forward. entailer!. unfold ao. rewrite H17. simpl andb.
    destruct (Z.eqb_spec give (room - Zlength O)), (zeq give (room - Zlength O)); try reflexivity; contradiction. }
  { forward. entailer!. unfold ao. destruct (Z.eqb_spec take (Zlength src - P)); [ | reflexivity].
    rewrite Int.unsigned_repr in H17 by rep_lia. rewrite e in H17. contradiction. }
  forward.
  (* no_progress *)
  set (np := andb (zf_ai z' =? take) (zf_ao z' =? give)).
  sm_split_call. forward.
  sm_ifpostv _t'20 (Vint (Int.repr (if np then 1 else 0))).
  { forward. forward. entailer!. unfold np. rewrite H17, Z.eqb_refl. simpl andb.
    destruct (Z.eqb_spec (zf_ao z') give), (zeq (zf_ao z') give); try reflexivity; contradiction. }
  { forward. entailer!. unfold np. destruct (Z.eqb_spec (zf_ai z') take); [contradiction | reflexivity]. }
  forward.
  (* may_stop *)
  set (ms := andb (negb (flush =? Z_BLOCK)) (negb (flush =? Z_TREES))).
  sm_ifpostv _t'21 (Vint (Int.repr (if ms then 1 else 0))).
  { forward. entailer!. unfold ms. rewrite sm_cmp32 by rep_lia. unfold Z_BLOCK, Z_TREES.
    destruct (Z.eqb_spec flush 5); [contradiction | ]. destruct (Z.eqb_spec flush 6); reflexivity. }
  { forward. entailer!. }
  forward.
  (* final(code_split) *)
  sm_split_call.
  forward_call r.
  (* the stream back as an istreamA *)
  match goal with |- context [data_at Tsh t_zsl ?v vsplit] =>
    change v with (sm_tup gv z' (adler_v (raw_live (Some L')) z' Vundef) (l_sp L')) end.
  sep_apply (sm_istreamA_fold gv Tsh vsplit z' Vundef L'); auto.
  (* the break: a final code, or all offered with no progress and a flush that may stop *)
  set (stop := orb (final_code r) (andb (andb ao np) ms)).
  assert (Hstop: stop = true -> Max w src room (O ++ ow) (sm_stop r)).
  { unfold stop, sm_stop. destruct (final_code r) eqn:Ef; simpl; auto.
    intros Hs. unfold ao, ms in Hs. rewrite !andb_true_iff in Hs.
    destruct Hs as [[[E1 E2] _] [E3 E4]]. apply Z.eqb_eq in E1. apply Z.eqb_eq in E2.
    apply negb_true_iff, Z.eqb_neq in E3. apply negb_true_iff, Z.eqb_neq in E4.
    apply Hnf; auto; lia. }
  sm_ifpostv _t'23 (Vint (Int.repr (if stop then 1 else 0))).
  { forward. entailer!. unfold stop. destruct (final_code r); [reflexivity | contradiction H17; reflexivity]. }
  { assert (Ef: final_code r = false) by (destruct (final_code r); [discriminate | reflexivity]).
    sm_ifpostv _t'24 (Vint (Int.repr (if andb ao np then 1 else 0))).
    { forward. entailer!. destruct ao; [ | contradiction H18; reflexivity]. destruct np; reflexivity. }
    { forward. entailer!. destruct ao; [discriminate | reflexivity]. }
    forward_if.
    { forward. forward. entailer!.
      unfold stop. rewrite Ef. simpl orb. destruct (ao && np)%bool; [ | contradiction H18; reflexivity].
      destruct ms; reflexivity. }
    { forward. entailer!. unfold stop. rewrite Ef. simpl orb. destruct (ao && np)%bool; [discriminate | ].
      reflexivity. } }
  assert (Hlo: Zlength (O ++ ow) <= room) by (rewrite Zlength_app; lia).
  assert (Hni': zf_ni z' = offset_val (P + (take - zf_ai z')) inp) by (rewrite Hni; reflexivity).
  assert (Hno': zf_no z' = offset_val (Zlength (O ++ ow)) o2) by (rewrite Hno, Zlength_app; reflexivity).
  forward_if.
  { assert (Es: stop = true) by (destruct stop; [reflexivity | contradiction H17; reflexivity]).
    forward. unfold sm_brk. Exists (O ++ ow) r z' L'. entailer!. }
  forward. unfold sm_inv. Exists (P + (take - zf_ai z')) (O ++ ow) z' L'. entailer!.
Qed.

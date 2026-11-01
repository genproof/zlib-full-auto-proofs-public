(* Law inflate_dict, main, inflate half: the window checks (ITMainInfKit.v it_win_stmt): inflateGetDictionary for the length and for the bytes, malloc(dl), the hist() comparison loop, free(gd); then seg_L4 (given). *)
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

(* the window after opos bytes of output: its length and its bytes, those of dict ++ data[0..opos) *)
Lemma itw_win_facts G opos L:
  it_win G opos L -> it_ok G -> 0 <= opos <= Zlength (it_data G) -> is_bytes (g_dict G) -> is_bytes (it_data G) ->
  i_whave (l_s L) = Z.min (Zlength (g_dict G) + opos) (2 ^ g_wb G) /\
  0 <= i_whave (l_s L) <= 2 ^ 15 /\
  Zlength (dict_bytes (l_s L)) = i_whave (l_s L) /\
  bytes_ok (dict_bytes (l_s L)) /\
  (forall i, 0 <= i < i_whave (l_s L) ->
     Znth i (dict_bytes (l_s L)) =
     Znth (Zlength (g_dict G) + opos - i_whave (l_s L) + i) (g_dict G ++ sublist 0 opos (it_data G))).
Proof.
  intros [Hw Hd] Gok Ho Bd Bdat.
  destruct Gok as (Hwb & _).
  set (h := g_dict G ++ sublist 0 opos (it_data G)) in *.
  assert (Lh: Zlength h = Zlength (g_dict G) + opos)
    by (subst h; rewrite Zlength_app, Zlength_sublist by lia; lia).
  rewrite Lh in Hw.
  assert (P15: 2 ^ g_wb G <= 2 ^ 15) by (apply Z.pow_le_mono_r; lia).
  assert (P0: 0 < 2 ^ g_wb G) by (apply Z.pow_pos_nonneg; lia).
  assert (W: 0 <= i_whave (l_s L) <= Zlength h) by (rewrite Hw, Lh; pose proof (Zlength_nonneg (g_dict G)); lia).
  split; [exact Hw | ].
  split; [rewrite Hw; pose proof (Zlength_nonneg (g_dict G)); lia | ].
  split; [rewrite Hd, Zlength_sublist by lia; lia | ].
  split.
  - rewrite Hd. apply Forall_sublist. subst h. apply Forall_app; split; auto. apply Forall_sublist; auto.
  - intros i Hi. rewrite Hd, Znth_sublist by lia. rewrite Lh. f_equal. lia.
Qed.

Lemma itw_uint_cs_ sh q:
  @data_at_ Zlib.units.Inflate.CS sh tuint q = @data_at_ CS sh tuint q.
Proof. unfold data_at_, field_at_. apply equal_f; apply (@field_at_change_composite _ _ CC_inflate); [apply JMeq_refl | reflexivity]. Qed.

Lemma itw_byte (db: list Z) i: bytes_ok db -> 0 <= i < Zlength db ->
  Znth i (byte_vals db) = Vint (Int.repr (Znth i db)) /\ 0 <= Znth i db <= Byte.max_unsigned.
Proof.
  intros B Hi. split.
  - unfold byte_vals. rewrite Znth_map by lia. reflexivity.
  - apply (proj1 (Forall_Znth db (fun b => 0 <= b <= Byte.max_unsigned)) B i Hi).
Qed.

Ltac itw_gpa := forward_call (Int.repr 1); [ solve [entailer!; try reflexivity] .. | ].

Lemma it_win_ok {Espec: OracleKind} : it_win_stmt.
Proof.
  intros I gv vw vs vosn vdl dictp badp datap srcp G wsel dcont scont Fr Inv Brk pos lim opos dset r z L
    ain aout ibp obp q ic oc qc GL MF K.
  pose proof GL as GL'.
  destruct GL' as (CF & Gok & Hws & Hdc & Hdsub & Hsc & Hssub & Bd & Bdat & Bsrc & Pd & Pb & Pdat & Psrc).
  unfold it_mid2, seg_L3, Delta_m, Gmain_k, it_PL, POST_m. simplify_func_tycontext. abbreviate_semax.
  destruct MF as (Hend & Hnend & Hpos & Hlim & Hopos & Hr & LOK & ZOK & Hain & Haout & Hic & Hoc & Hqc & Pib & Pob & Pq).
  assert_PROP (isptr vs /\ isptr vdl) as PV by entailer!. destruct PV as [Pvs Pvdl].
  set (b := andb dset (orb (negb (r =? Z_STREAM_END)) (negb (g_zlib G)))).
  ifpost _t'54 (Int.repr (if b then 1 else 0)).
  { destruct dset; [ | contradiction H'; reflexivity].
    ifpost _t'54 (Int.repr (if b then 1 else 0)).
    { forward. entailer!. subst b. simpl.
      destruct (Z.eqb_spec r Z_STREAM_END); [subst; contradiction | reflexivity]. }
    { forward. forward. entailer!. subst b. simpl.
      destruct (Z.eqb_spec r Z_STREAM_END) as [E|E].
      2:{ exfalso; apply E. unfold Z_STREAM_END in *. apply repr_inj_signed; try rep_lia. exact H0. }
      destruct (g_zlib G); reflexivity. }
    }
  { forward. entailer!. destruct dset; [discriminate | reflexivity]. }
  match goal with |- semax _ (PROPx _ (LOCALx (_ :: ?Q) (SEPx ?R))) _ _ =>
    forward_if (PROPx [] (LOCALx Q (SEPx R))) end.
  2:{ forward. entailer!. }
  2:{ unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
      eapply semax_pre; [ | exact K]. unfold it_mid2. apply ENTAIL_refl. }
  (* the window checks *)
  assert (Hb: b = true) by (destruct b; [reflexivity | contradiction H; reflexivity]).
  subst b. apply andb_prop in Hb. destruct Hb as [Ed Hb]. subst dset.
  assert (W: it_win G opos L).
  { destruct (Z.eqb_spec r Z_STREAM_END) as [E|E].
    - destruct (Hend E) as (_ & _ & X). apply X; [reflexivity | ].
      subst r; simpl in Hb. destruct (g_zlib G); [discriminate | reflexivity].
    - exact (it_window I CF _ _ _ _ _ _ (Hnend E)). }
  destruct (itw_win_facts G opos L W Gok Hopos Bd Bdat) as (Hwh & Hwh15 & Ldb & Bdb & Edb).
  set (wh := i_whave (l_s L)) in *. set (db := dict_bytes (l_s L)) in *.
  clear H H'.
  forward.
  sep_apply (data_at_data_at_ Tsh tuint (Vint (Int.repr 0)) vdl).
  rewrite <- itw_uint_cs_.
  forward_call (gv, Tsh, vs, z, Some L, DNull, vdl).
  { rewrite it_istream_opt by auto. unfold dict_rep, len_rep.
    rewrite if_false by (intro; subst; contradiction). cancel. }
  { rewrite it_is_live by auto. exact Logic.I. }
  rewrite it_istream_opt, it_is_live by auto. unfold dict_rep, len_rep.
  rewrite if_false by (intro; subst; contradiction).
  rewrite it_uint_inflate_cs. fold wh db.
  itw_gpa.
  forward.
  assert (Hdl: Zlength (g_dict G) <= 2 ^ 16) by (destruct Gok as (_ & _ & X & _); exact X).
  assert (Hdt: Zlength (it_data G) <= 2 ^ 18) by (destruct Gok as (_ & _ & _ & X & _); exact X).
  assert (Hwb: 8 <= g_wb G <= 15) by (destruct Gok as (X & _); exact X).
  assert (P15: 2 ^ g_wb G <= 2 ^ 15) by (apply Z.pow_le_mono_r; lia).
  assert (P0: 0 < 2 ^ g_wb G) by (apply Z.pow_pos_nonneg; lia).
  rewrite !Int.unsigned_repr by rep_lia. rewrite add64_repr.
  match goal with |- semax _ (PROPx _ (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx [] (LOCALx (temp _t'50 (Vlong (Int64.repr wh)) :: Q) (SEPx R))) end.
  { forward. entailer!. rewrite Int.unsigned_repr in H by rep_lia. rewrite Hwh, Z.min_l by lia. reflexivity. }
  { forward. entailer!. rewrite Int.unsigned_repr in H by rep_lia.
    rewrite ?Int.unsigned_repr by rep_lia. rewrite Hwh, Z.min_r by lia. reflexivity. }
  forward.
  forward_call (Int.repr 1).
  { entailer!. rewrite Int64.eq_true. reflexivity. }
  forward.
  forward_call (tarray tuchar wh, gv).
  { simpl. rewrite Z.max_r by lia. rep_lia. }
  Intros gd.
  forward.
  destruct (eq_dec gd nullval) as [GN|GN].
  { subst gd. forward_if.
    { forward. Exists (Int.repr 0). sep_apply it_istream_to_undef.
      sep_apply (data_at_data_at_ Tsh tuint (Vint (Int.repr (i_whave (l_s L)))) vdl). entailer!. }
    { contradiction. } }
  Intros.
  forward_if.
  { contradiction. }
  assert_PROP (isptr gd) as Pgd by entailer!.
  assert (Ed: data_at_ Ews (tarray tuchar wh) gd = data_at Ews (tarray tuchar wh) (Zrepeat Vundef wh) gd)
    by reflexivity.
  rewrite Ed. clear Ed.
  rewrite <- (it_bytes_inflate_cs Ews wh (Zrepeat Vundef wh) gd).
  forward_call (gv, Tsh, vs, z, Some L, DBuf Ews gd 0 wh (Zrepeat Vundef wh), nullval).
  { rewrite it_istream_opt by auto. cancel. }
  { rewrite it_is_live by auto. simpl dict_ok.
    split; [auto with typeclass_instances | ].
    rewrite Zlength_Zrepeat by lia. repeat split; auto; rep_lia. }
  rewrite it_istream_opt, it_is_live by auto. unfold dict_rep, len_rep. rewrite if_true by auto.
  fold db. rewrite sublist_nil, app_nil_l, Z.add_0_l, Ldb.
  rewrite sublist_nil' by (rewrite ?Zlength_Zrepeat; lia). rewrite app_nil_r.
  rewrite it_bytes_inflate_cs.
  itw_gpa.
  forward.
  match goal with |- semax _ (PROPx _ (LOCALx (_ :: ?Q) (SEPx ?R))) _ _ =>
    forward_loop (EX i: Z, PROPx [0 <= i <= wh] (LOCALx (temp _i__1 (Vint (Int.repr i)) :: Q) (SEPx R)))
      continue: (EX i: Z, PROPx [0 <= i < wh] (LOCALx (temp _i__1 (Vint (Int.repr i)) :: Q) (SEPx R)))
      break: (PROPx [] (LOCALx (temp _i__1 (Vint (Int.repr wh)) :: Q) (SEPx R))) end.
  { Exists 0. entailer!. }
  { Intros i. forward. forward_if.
    2:{ assert (Ei: i = wh) by lia. rewrite Ei. forward. entailer!. }
    forward.
    assert (Lpre: Zlength (sublist 0 opos (it_data G)) = opos) by (rewrite Zlength_sublist; lia).
    forward_call (Ews, dictp, g_dict G, Ews, datap, 2 ^ 18, dcont, sublist 0 opos (it_data G),
                  Zlength (g_dict G) + opos - wh + i).
    { entailer!.
      assert (E1: Int64.Z_mod_modulus (Zlength (g_dict G) + opos) = Zlength (g_dict G) + opos)
        by (rewrite Int64.Z_mod_modulus_eq, Z.mod_small; rep_lia).
      assert (E2: Int64.Z_mod_modulus (i_whave (l_s L)) = i_whave (l_s L))
        by (rewrite Int64.Z_mod_modulus_eq, Z.mod_small; rep_lia).
      rewrite E1, E2.
      assert (E3: Int64.Z_mod_modulus (Zlength (g_dict G) + opos - i_whave (l_s L)) =
                  Zlength (g_dict G) + opos - i_whave (l_s L))
        by (rewrite Int64.Z_mod_modulus_eq, Z.mod_small; rep_lia).
      rewrite E3. reflexivity. }
    { rewrite Lpre. repeat split; auto; try rep_lia.
      - rewrite <- sublist_bytes_rep, <- Hdsub, sublist_sublist by lia. f_equal; lia.
      - apply Forall_sublist; auto. }
    destruct (itw_byte db i Bdb) as [Ebi Rbi]; [lia | ].
    forward.
    { entailer!. unfold byte_vals. rewrite Znth_map by lia. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
    forward_call (Int.repr 1).
    { entailer!. unfold byte_vals. rewrite Znth_map by lia. rewrite <- Edb by lia. simpl. rewrite Int.eq_true. reflexivity. }
    Exists i. entailer!. }
  { Intros i. forward. Exists (i + 1). entailer!. f_equal. symmetry. apply (add_repr i 1). }
  forward_call (tarray tuchar (i_whave (l_s L)), gd, gv).
  { rewrite if_false by auto.
    sep_apply (data_at_data_at_ Ews (tarray tuchar (i_whave (l_s L))) (byte_vals db) gd). cancel. }
  sep_apply (data_at_data_at_ Tsh tuint (Vint (Int.repr wh)) vdl). entailer!.
Qed.

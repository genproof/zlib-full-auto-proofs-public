(* Law inflate_header, main: positions 0 .. 23 of b0 (IHMainKit.v): the draws of wbits .. cnul, the two
   gp_assume, hlen, total, the four malloc()s (src, xf, nf, cf) and `if (src == NULL || ...) return 0;`;
   then seg_24 (given). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.crc32.HarnessRef.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.inflate_common.HarnessLib.
Require Import Zlib.proof.harness.inflate_header.IHLawCS Zlib.proof.harness.inflate_header.IHGlobals
               Zlib.proof.harness.inflate_header.IHHelpers Zlib.proof.harness.inflate_header.IHFacts
               Zlib.proof.harness.inflate_header.IHMainStmt.
Require Import Zlib.harness.x_inflate_header.code.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.harness.inflate_header.IHMainKit.
Local Open Scope logic.

Ltac acmp :=
  simpl;
  try change (Int.shl (Int.repr 1) (Int.repr 16)) with (Int.repr (2 ^ 16)) in *;
  rewrite ?Int.unsigned_repr in * by rep_lia;
  unfold Int.ltu, Int64.ltu, Int.eq, Int64.eq;
  rewrite ?Int.unsigned_repr, ?Int64.unsigned_repr by rep_lia;
  repeat match goal with |- context [zlt ?a ?b] => destruct (zlt a b) end;
  repeat match goal with |- context [zeq ?a ?b] => destruct (zeq a b) end;
  repeat match goal with |- context [Z.leb ?a ?b] => destruct (Z.leb_spec a b) end;
  simpl in *;
  try lia;
  try (exfalso; match goal with
                | H: Int.repr 1 = Int.zero |- _ => apply Int.one_not_zero; exact H
                | H: Int.repr 0 <> Int.zero |- _ => apply H; reflexivity end);
  reflexivity.

Ltac assumedn := repeat match goal with H: Int.repr (if ?c then _ else _) <> Int.zero |- _ =>
  let E := fresh "E" in destruct c eqn:E; [ apply Z.leb_le in E | contradiction H; reflexivity] end.

Lemma ih_flb_zero flg bit: 0 <= flg <= 255 -> 0 <= bit <= 255 ->
  (Int.and (Int.repr flg) (Int.repr bit) = Int.zero <-> flb flg bit = false).
Proof.
  intros Hf Hb. unfold flb, Int.and. rewrite !Int.unsigned_repr by rep_lia.
  assert (L0: 0 <= Z.land flg bit) by (apply Z.land_nonneg; lia).
  assert (L1: Z.land flg bit < 2 ^ 8).
  { assert (M: Z.land flg bit = Z.land flg bit mod 2 ^ 8).
    { rewrite <- Z.land_ones by lia. rewrite <- Z.land_assoc. rewrite (Z.land_ones bit 8) by lia.
      rewrite Z.mod_small by lia. reflexivity. }
    rewrite M. apply Z.mod_pos_bound. lia. }
  destruct (Z.eqb_spec (Z.land flg bit) 0) as [E|E]; simpl.
  - rewrite E. split; auto.
  - split; [intros R | discriminate]. exfalso. apply E.
    apply repr_inj_unsigned in R; rep_lia.
Qed.

Ltac flbs := repeat match goal with
  | H: Int.and (Int.repr ?f) (Int.repr ?b) = Int.zero |- _ =>
      apply ih_flb_zero in H; [ | rep_lia | rep_lia]
  | H: Int.and (Int.repr ?f) (Int.repr ?b) <> Int.zero |- _ =>
      let E := fresh "E" in assert (E: flb f b = true) by
        (destruct (flb f b) eqn:E'; [reflexivity | apply ih_flb_zero in E'; [contradiction | rep_lia | rep_lia]]);
      clear H
  end.

Ltac flbclose := flbs;
  repeat match goal with E: flb ?a ?b = ?c |- context [flb ?a ?b] => rewrite E end; try reflexivity.

Ltac nt_infeas := exfalso; first [ match goal with H: ?a <> ?b |- _ => solve [apply H; reflexivity] end
                              | match goal with H: _ |- _ => solve [discriminate H] end
                              | contradiction
                              | lia ].

Ltac ptr0 := match goal with |- _ = force_val (sem_cast_i2bool (force_val (sem_cmp_pp Ceq ?p _))) =>
  match goal with H: field_compatible _ _ p |- _ => destruct p; try (destruct H; contradiction); reflexivity end end.

Lemma pro_ok {Espec: OracleKind} gv V:
  (forall n b P, ih_f24 n b P -> semax Delta_m (ih_s24 gv V n b P) seg_24 POST_b) ->
  semax Delta_m (ih_pre0 gv V) b0 POST_b.
Proof.
  intros K.
  unfold ih_pre0, b0, Delta_m, Gmain, POST_b, POST_m.
  cbn [v_s_ v_h_ v_xs_ v_ns_ v_cs_ v_osn_].
  simplify_func_tycontext. abbreviate_semax.
  forward_call tt. Intros wb.
  forward_call tt. Intros flg.
  apply seq_assoc1. forward_call tt. Intros mtime. forward.
  rewrite Int.unsigned_repr by rep_lia.
  forward_call tt. Intros xfl.
  forward_call tt. Intros os.
  forward_call tt. Intros xlen.
  forward_call tt. Intros nl.
  forward_call tt. Intros cl.
  forward_call tt. Intros delta.
  forward_call tt. Intros xmax.
  forward_call tt. Intros nmax.
  forward_call tt. Intros cmax.
  forward_call tt. Intros xnul.
  forward_call tt. Intros nnul.
  forward_call tt. Intros cnul.
  assert (Ew: Int.repr wb = Int.repr (Int.signed (Int.repr wb))) by (rewrite Int.repr_signed; auto).
  rewrite Ew. clear Ew. set (w := Int.signed (Int.repr wb)).
  assert (Hw: Int.min_signed <= w <= Int.max_signed) by apply Int.signed_range. clearbody w.
  ifpost _t'16 (Int.repr (if xlen <=? 65535 then (if nl <=? 2 ^ 16 then 1 else 0) else 0)).
  { forward. entailer!. acmp. }
  { forward. entailer!. acmp. }
  ifpost _t'17 (Int.repr (if xlen <=? 65535 then (if nl <=? 2 ^ 16 then (if cl <=? 2 ^ 16 then 1 else 0) else 0) else 0)).
  { forward. entailer!. acmp. }
  { forward. entailer!. acmp. }
  forward_call (Int.repr (if xlen <=? 65535 then (if nl <=? 2 ^ 16 then (if cl <=? 2 ^ 16 then 1 else 0) else 0) else 0)).
  assumedn.
  ifpost _t'18 (Int.repr (if xmax <=? 2 ^ 16 then (if nmax <=? 2 ^ 16 then 1 else 0) else 0)).
  { forward. entailer!. acmp. }
  { forward. entailer!. acmp. }
  ifpost _t'19 (Int.repr (if xmax <=? 2 ^ 16 then (if nmax <=? 2 ^ 16 then (if cmax <=? 2 ^ 16 then 1 else 0) else 0) else 0)).
  { forward. entailer!. acmp. }
  { forward. entailer!. acmp. }
  forward_call (Int.repr (if xmax <=? 2 ^ 16 then (if nmax <=? 2 ^ 16 then (if cmax <=? 2 ^ 16 then 1 else 0) else 0) else 0)).
  assumedn.
  ifpost _t'20 (Int.repr (if flb flg 4 then 2 + xlen else 0)).
  { forward. entailer!. flbclose. }
  { forward. entailer!. flbclose. }
  ifpost _t'21 (Int.repr (if flb flg 8 then nl + 1 else 0)).
  { forward. entailer!. flbclose. }
  { forward. entailer!. flbclose. }
  ifpost _t'22 (Int.repr (if flb flg 16 then cl + 1 else 0)).
  { forward. entailer!. flbclose. }
  { forward. entailer!. flbclose. }
  forward.
  ifpost _t'23 (Int.repr (if flb flg 2 then 2 else 0)).
  { forward. entailer!. flbclose. }
  { forward. entailer!. flbclose. }
  forward.
  set (n := IHN flg mtime xfl os xlen nl cl delta).
  match goal with |- context [temp _total (Vint ?x)] =>
    replace x with (Int.repr (n_total n)) by (unfold n_total, n_hlen; simpl; rewrite !add_repr; f_equal; lia) end.
  match goal with |- context [temp _hlen (Vint ?x)] =>
    replace x with (Int.repr (n_hlen n)) by (unfold n_hlen; simpl; rewrite !add_repr; f_equal; lia) end.
  assert (Ht: 0 <= n_total n <= 4 * 2 ^ 16 + 100)
    by (unfold n_total, n_hlen, n; simpl; clear -E E0 E1 H4 H5 H6; simpl in *;
        destruct (flb flg 2), (flb flg 4), (flb flg 8), (flb flg 16); lia).
  assert (Hh: 0 <= n_hlen n <= n_total n) 
    by (unfold n_total, n_hlen, n; simpl; clear -E E0 E1 H4 H5 H6; simpl in *;
        destruct (flb flg 2), (flb flg 4), (flb flg 8), (flb flg 16); lia).
  forward_call (tarray tuchar (n_total n), gv).
  { simpl. rewrite Z.max_r by lia. rep_lia. }
  Intros src.
  forward_call (tarray tuchar xlen, gv).
  { simpl. rewrite Z.max_r by lia. rep_lia. }
  Intros xf.
  forward_call (tarray tuchar (nl + 1), gv).
  { simpl. rewrite Z.max_r by lia. rep_lia. }
  Intros nf.
  forward_call (tarray tuchar (cl + 1), gv).
  { simpl. rewrite Z.max_r by lia. rep_lia. }
  Intros cf.
  destruct (eq_dec src nullval) as [Ns|Ns].
  { subst src.
    ifpost _t'28 (Int.repr 1). { forward. entailer!. } { nt_infeas. }
    ifpost _t'29 (Int.repr 1). { forward. entailer!. } { nt_infeas. }
    ifpost _t'30 (Int.repr 1). { forward. entailer!. } { nt_infeas. }
    forward_if. { forward. Exists (Int.repr 0). entailer!. } { nt_infeas. } }
  Intros.
  destruct (eq_dec xf nullval) as [Nx|Nx].
  { subst xf.
    ifpost _t'28 (Int.repr 1). { nt_infeas. } { forward. entailer!. }
    ifpost _t'29 (Int.repr 1). { forward. entailer!. } { nt_infeas. }
    ifpost _t'30 (Int.repr 1). { forward. entailer!. } { nt_infeas. }
    forward_if. { forward. Exists (Int.repr 0). entailer!. } { nt_infeas. } }
  Intros.
  destruct (eq_dec nf nullval) as [Nn|Nn].
  { subst nf.
    ifpost _t'28 (Int.repr 0). { nt_infeas. } { forward. entailer!. ptr0. }
    ifpost _t'29 (Int.repr 1). { nt_infeas. } { forward. entailer!. }
    ifpost _t'30 (Int.repr 1). { forward. entailer!. } { nt_infeas. }
    forward_if. { forward. Exists (Int.repr 0). entailer!. } { nt_infeas. } }
  Intros.
  destruct (eq_dec cf nullval) as [Nc|Nc].
  { subst cf.
    ifpost _t'28 (Int.repr 0). { nt_infeas. } { forward. entailer!. ptr0. }
    ifpost _t'29 (Int.repr 0). { nt_infeas. } { forward. entailer!. ptr0. }
    ifpost _t'30 (Int.repr 1). { nt_infeas. } { forward. entailer!. }
    forward_if. { forward. Exists (Int.repr 0). entailer!. } { nt_infeas. } }
  Intros.
  ifpost _t'28 (Int.repr 0). { nt_infeas. } { forward. entailer!. ptr0. }
  ifpost _t'29 (Int.repr 0). { nt_infeas. } { forward. entailer!. ptr0. }
  ifpost _t'30 (Int.repr 0). { nt_infeas. } { forward. entailer!. ptr0. }
  forward_if. { nt_infeas. }
  assert_PROP (isptr src /\ isptr xf /\ isptr nf /\ isptr cf) as Pp by entailer!.
  assert (F24: ih_f24 n (IHB w xmax nmax cmax xnul nnul cnul) (IHP src xf nf cf)).
  { unfold ih_f24, n; simpl. destruct Pp as (P1 & P2 & P3 & P4). repeat split; auto; rep_lia. }
  unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
  eapply semax_pre; [ | apply (K n _ _ F24) ].
  unfold ih_s24.
  cbn [n_flg n_mtime n_xfl n_os n_xlen n_nl n_cl n_delta b_w b_xmax b_nmax b_cmax b_xnul b_nnul b_cnul
       p_src p_xf p_nf p_cf].
  entailer!.
Qed.

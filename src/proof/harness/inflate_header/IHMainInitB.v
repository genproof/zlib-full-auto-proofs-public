(* Law inflate_header, main, positions 60 .. 69 (IHMainInitKit.v): h.extra_max/name_max/comm_max = xmax/nmax/cmax,
   the seven pick()s of h.text, h.time, h.xflags, h.os, h.extra_len, h.hcrc, h.done; then seg_70 (given) with
   h holding ihi_h0 of the picked values. *)
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
Require Import Zlib.proof.harness.inflate_header.IHMainInitKit.
Local Open Scope logic.

(* pick(h.f) on a field of struct gz_header: its bytes for nondet_bytes, and back to a value of the field *)
Lemma ihp_bytes sh gfs p n v:
  sizeof (nested_field_type (Tstruct _gz_header_s noattr) gfs) = n -> n < Ptrofs.modulus ->
  field_at sh (Tstruct _gz_header_s noattr) gfs v p |--
  data_at_ sh (tarray tuchar n) (field_address (Tstruct _gz_header_s noattr) gfs p).
Proof.
  intros E L. sep_apply field_at_field_at_.
  rewrite field_at__memory_block. rewrite E.
  apply memory_block_data_at__tarray_tuchar.
  pose proof (sizeof_pos (nested_field_type (Tstruct _gz_header_s noattr) gfs)). lia.
Qed.

Lemma ihp_fa_nonnull gfs p: field_compatible (Tstruct _gz_header_s noattr) gfs p ->
  field_address (Tstruct _gz_header_s noattr) gfs p <> nullval.
Proof.
  intros FC. rewrite field_compatible_field_address by auto.
  destruct FC as [Hp _]. destruct p; try contradiction. discriminate.
Qed.

Definition ihp_bytes_at sh (n: Z) (bs: list Z) (f: ident) (p: val) : mpred :=
  data_at sh (tarray tuchar n) (map (fun b => Vint (Int.repr b)) bs)
    (field_address (Tstruct _gz_header_s noattr) (DOT f) p).

Lemma ihp_text sh p bs:
  field_compatible (Tstruct _gz_header_s noattr) (DOT _text) p -> Zlength bs = 4 ->
  Forall (fun b => 0 <= b <= Byte.max_unsigned) bs ->
  ihp_bytes_at sh 4 bs _text p |--
  EX z : Z, !! srange z && field_at sh (Tstruct _gz_header_s noattr) (DOT _text) (Vint (Int.repr z)) p.
Proof. unfold ihp_bytes_at, srange. intros FC L B.
  pose proof (field_compatible_app [] _ _ _ FC) as FC'; simpl in FC'.
  sep_apply (pick_tint sh bs _ L B FC'); Intros v; Exists (Int.signed v).
  rewrite field_at_data_at; simpl nested_field_type; rewrite Int.repr_signed; entailer!; rep_lia. Qed.
Lemma ihp_xflags sh p bs:
  field_compatible (Tstruct _gz_header_s noattr) (DOT _xflags) p -> Zlength bs = 4 ->
  Forall (fun b => 0 <= b <= Byte.max_unsigned) bs ->
  ihp_bytes_at sh 4 bs _xflags p |--
  EX z : Z, !! srange z && field_at sh (Tstruct _gz_header_s noattr) (DOT _xflags) (Vint (Int.repr z)) p.
Proof. unfold ihp_bytes_at, srange. intros FC L B.
  pose proof (field_compatible_app [] _ _ _ FC) as FC'; simpl in FC'.
  sep_apply (pick_tint sh bs _ L B FC'); Intros v; Exists (Int.signed v).
  rewrite field_at_data_at; simpl nested_field_type; rewrite Int.repr_signed; entailer!; rep_lia. Qed.
Lemma ihp_os sh p bs:
  field_compatible (Tstruct _gz_header_s noattr) (DOT _os) p -> Zlength bs = 4 ->
  Forall (fun b => 0 <= b <= Byte.max_unsigned) bs ->
  ihp_bytes_at sh 4 bs _os p |--
  EX z : Z, !! srange z && field_at sh (Tstruct _gz_header_s noattr) (DOT _os) (Vint (Int.repr z)) p.
Proof. unfold ihp_bytes_at, srange. intros FC L B.
  pose proof (field_compatible_app [] _ _ _ FC) as FC'; simpl in FC'.
  sep_apply (pick_tint sh bs _ L B FC'); Intros v; Exists (Int.signed v).
  rewrite field_at_data_at; simpl nested_field_type; rewrite Int.repr_signed; entailer!; rep_lia. Qed.
Lemma ihp_hcrc sh p bs:
  field_compatible (Tstruct _gz_header_s noattr) (DOT _hcrc) p -> Zlength bs = 4 ->
  Forall (fun b => 0 <= b <= Byte.max_unsigned) bs ->
  ihp_bytes_at sh 4 bs _hcrc p |--
  EX z : Z, !! srange z && field_at sh (Tstruct _gz_header_s noattr) (DOT _hcrc) (Vint (Int.repr z)) p.
Proof. unfold ihp_bytes_at, srange. intros FC L B.
  pose proof (field_compatible_app [] _ _ _ FC) as FC'; simpl in FC'.
  sep_apply (pick_tint sh bs _ L B FC'); Intros v; Exists (Int.signed v).
  rewrite field_at_data_at; simpl nested_field_type; rewrite Int.repr_signed; entailer!; rep_lia. Qed.
Lemma ihp_done sh p bs:
  field_compatible (Tstruct _gz_header_s noattr) (DOT _done) p -> Zlength bs = 4 ->
  Forall (fun b => 0 <= b <= Byte.max_unsigned) bs ->
  ihp_bytes_at sh 4 bs _done p |--
  EX z : Z, !! srange z && field_at sh (Tstruct _gz_header_s noattr) (DOT _done) (Vint (Int.repr z)) p.
Proof. unfold ihp_bytes_at, srange. intros FC L B.
  pose proof (field_compatible_app [] _ _ _ FC) as FC'; simpl in FC'.
  sep_apply (pick_tint sh bs _ L B FC'); Intros v; Exists (Int.signed v).
  rewrite field_at_data_at; simpl nested_field_type; rewrite Int.repr_signed; entailer!; rep_lia. Qed.

Lemma ihp_time sh p bs:
  field_compatible (Tstruct _gz_header_s noattr) (DOT _time) p -> Zlength bs = 8 ->
  Forall (fun b => 0 <= b <= Byte.max_unsigned) bs ->
  ihp_bytes_at sh 8 bs _time p |--
  EX z : Z, !! lrange z && field_at sh (Tstruct _gz_header_s noattr) (DOT _time) (Vlong (Int64.repr z)) p.
Proof.
  unfold ihp_bytes_at, lrange. intros FC L B.
  pose proof (field_compatible_app [] _ _ _ FC) as FC'; simpl in FC'.
  sep_apply (pick_tulong sh bs _ L B FC'); Intros v; Exists (Int64.unsigned v).
  rewrite field_at_data_at; simpl nested_field_type; rewrite Int64.repr_unsigned; entailer!; rep_lia.
Qed.

Lemma ihp_elen sh p bs:
  field_compatible (Tstruct _gz_header_s noattr) (DOT _extra_len) p -> Zlength bs = 4 ->
  Forall (fun b => 0 <= b <= Byte.max_unsigned) bs ->
  ihp_bytes_at sh 4 bs _extra_len p |--
  EX z : Z, !! urange z && field_at sh (Tstruct _gz_header_s noattr) (DOT _extra_len) (Vint (Int.repr z)) p.
Proof.
  unfold ihp_bytes_at, urange. intros FC L B.
  pose proof (field_compatible_app [] _ _ _ FC) as FC'; simpl in FC'.
  sep_apply (pick_tuint sh bs _ L B FC'); Intros v; Exists (Int.unsigned v).
  rewrite field_at_data_at; simpl nested_field_type; rewrite Int.repr_unsigned; entailer!; rep_lia.
Qed.

Ltac ihp_call_side :=
  lazymatch goal with
  | |- ENTAIL _, _ |-- !! _ =>
      apply prop_right; simpl; unfold field_address; rewrite if_true by auto; reflexivity
  | |- semax _ _ _ _ => idtac
  | |- _ => rewrite if_false by (apply ihp_fa_nonnull; auto); cancel
  end.

Lemma picks_ok {Espec: OracleKind} I gv V g b P sp adl rs H xbs nbs cbs:
  ihi_f60 I g b P sp adl rs H xbs nbs cbs ->
  (forall text time xflags os elen hcrc done,
     hwf (ihi_h0 b xbs nbs cbs text time xflags os elen hcrc done) ->
     semax Delta_m (ihi_s70 gv V g b P sp adl rs H (ihi_h0 b xbs nbs cbs text time xflags os elen hcrc done))
       seg_70 POST_b) ->
  semax Delta_m (ihi_s60 gv V g b P sp adl rs H xbs nbs cbs) seg_60 POST_b.
Proof.
  intros F K.
  destruct V as [vs vh vxs vns vcs vosn]. destruct b as [w xmax nmax cmax xnul nnul cnul].
  destruct P as [psrc pxf pnf pcf]. destruct H as [xb nb cb xq nq cq].
  unfold ihi_s60, seg_60, Delta_m, Gmain, POST_b, POST_m. simplify_func_tycontext. abbreviate_semax.
  cbn [v_s_ v_h_ v_xs_ v_ns_ v_cs_ v_osn_ b_w b_xmax b_nmax b_cmax b_xnul b_nnul b_cnul p_src p_xf p_nf p_cf
       h_xb h_nb h_cb h_xq h_nq h_cq].
  freeze [0;1;2;3;4;5;6;8;9;10;11;12;13;14;15;16;17;18;19;20;21;22] FR.
  forward. forward. forward.
  unfold ihi_h60; cbn [fst snd].
  unfold_data_at (data_at _ _ _ vh).
  assert_PROP (field_compatible (Tstruct _gz_header_s noattr) (DOT _text) vh /\
               field_compatible (Tstruct _gz_header_s noattr) (DOT _time) vh /\
               field_compatible (Tstruct _gz_header_s noattr) (DOT _xflags) vh /\
               field_compatible (Tstruct _gz_header_s noattr) (DOT _os) vh /\
               field_compatible (Tstruct _gz_header_s noattr) (DOT _extra_len) vh /\
               field_compatible (Tstruct _gz_header_s noattr) (DOT _hcrc) vh /\
               field_compatible (Tstruct _gz_header_s noattr) (DOT _done) vh) as FF by entailer!.
  destruct FF as (F1 & F2 & F3 & F4 & F5 & F6 & F7).
  sep_apply (ihp_bytes Tsh (DOT _text) vh 4 Vundef eq_refl ltac:(rep_lia)).
  forward_call (field_address (Tstruct _gz_header_s noattr) (DOT _text) vh, 4, Tsh).
  all: ihp_call_side.
  Intros bs. rewrite if_false by (apply ihp_fa_nonnull; auto).
  fold (ihp_bytes_at Tsh 4 bs _text vh).
  sep_apply (ihp_text Tsh vh bs F1 ltac:(assumption) ltac:(assumption)). Intros text.
  match goal with H1: Zlength bs = _, H2: Forall _ bs |- _ => clear H1 H2 end. clear bs.
  sep_apply (ihp_bytes Tsh (DOT _time) vh 8 Vundef eq_refl ltac:(rep_lia)).
  forward_call (field_address (Tstruct _gz_header_s noattr) (DOT _time) vh, 8, Tsh).
  all: ihp_call_side.
  Intros bs. rewrite if_false by (apply ihp_fa_nonnull; auto).
  fold (ihp_bytes_at Tsh 8 bs _time vh).
  sep_apply (ihp_time Tsh vh bs F2 ltac:(assumption) ltac:(assumption)). Intros time.
  match goal with H1: Zlength bs = _, H2: Forall _ bs |- _ => clear H1 H2 end. clear bs.
  sep_apply (ihp_bytes Tsh (DOT _xflags) vh 4 Vundef eq_refl ltac:(rep_lia)).
  forward_call (field_address (Tstruct _gz_header_s noattr) (DOT _xflags) vh, 4, Tsh).
  all: ihp_call_side.
  Intros bs. rewrite if_false by (apply ihp_fa_nonnull; auto).
  fold (ihp_bytes_at Tsh 4 bs _xflags vh).
  sep_apply (ihp_xflags Tsh vh bs F3 ltac:(assumption) ltac:(assumption)). Intros xflags.
  match goal with H1: Zlength bs = _, H2: Forall _ bs |- _ => clear H1 H2 end. clear bs.
  sep_apply (ihp_bytes Tsh (DOT _os) vh 4 Vundef eq_refl ltac:(rep_lia)).
  forward_call (field_address (Tstruct _gz_header_s noattr) (DOT _os) vh, 4, Tsh).
  all: ihp_call_side.
  Intros bs. rewrite if_false by (apply ihp_fa_nonnull; auto).
  fold (ihp_bytes_at Tsh 4 bs _os vh).
  sep_apply (ihp_os Tsh vh bs F4 ltac:(assumption) ltac:(assumption)). Intros os.
  match goal with H1: Zlength bs = _, H2: Forall _ bs |- _ => clear H1 H2 end. clear bs.
  sep_apply (ihp_bytes Tsh (DOT _extra_len) vh 4 Vundef eq_refl ltac:(rep_lia)).
  forward_call (field_address (Tstruct _gz_header_s noattr) (DOT _extra_len) vh, 4, Tsh).
  all: ihp_call_side.
  Intros bs. rewrite if_false by (apply ihp_fa_nonnull; auto).
  fold (ihp_bytes_at Tsh 4 bs _extra_len vh).
  sep_apply (ihp_elen Tsh vh bs F5 ltac:(assumption) ltac:(assumption)). Intros elen.
  match goal with H1: Zlength bs = _, H2: Forall _ bs |- _ => clear H1 H2 end. clear bs.
  sep_apply (ihp_bytes Tsh (DOT _hcrc) vh 4 Vundef eq_refl ltac:(rep_lia)).
  forward_call (field_address (Tstruct _gz_header_s noattr) (DOT _hcrc) vh, 4, Tsh).
  all: ihp_call_side.
  Intros bs. rewrite if_false by (apply ihp_fa_nonnull; auto).
  fold (ihp_bytes_at Tsh 4 bs _hcrc vh).
  sep_apply (ihp_hcrc Tsh vh bs F6 ltac:(assumption) ltac:(assumption)). Intros hcrc.
  match goal with H1: Zlength bs = _, H2: Forall _ bs |- _ => clear H1 H2 end. clear bs.
  sep_apply (ihp_bytes Tsh (DOT _done) vh 4 Vundef eq_refl ltac:(rep_lia)).
  forward_call (field_address (Tstruct _gz_header_s noattr) (DOT _done) vh, 4, Tsh).
  all: ihp_call_side.
  Intros bs. rewrite if_false by (apply ihp_fa_nonnull; auto).
  fold (ihp_bytes_at Tsh 4 bs _done vh).
  sep_apply (ihp_done Tsh vh bs F7 ltac:(assumption) ltac:(assumption)). Intros done.
  match goal with H1: Zlength bs = _, H2: Forall _ bs |- _ => clear H1 H2 end. clear bs.
  assert (HW: hwf (ihi_h0 {| b_w := w; b_xmax := xmax; b_nmax := nmax; b_cmax := cmax; b_xnul := xnul;
                             b_nnul := nnul; b_cnul := cnul |} xbs nbs cbs text time xflags os elen hcrc done)).
  { destruct F as (_ & (_ & _ & X1 & X2 & X3 & _) & _ & _ & _ & _ & L1 & B1 & _ & _ & L2 & B2 & _ & _ & L3 & B3 & _).
    cbn [b_xmax b_nmax b_cmax] in *.
    constructor; cbn [ihi_h0 h_text h_time h_xflags h_os h_extra_len h_extra_max h_name_max h_comm_max h_xbuf h_nbuf
      h_cbuf h_hcrc h_done b_xmax b_nmax b_cmax]; auto; try lia. }
  unfold abbreviate in MORE_COMMANDS, POSTCONDITION; subst MORE_COMMANDS POSTCONDITION.
  eapply semax_pre; [ | apply (K text time xflags os elen hcrc done HW) ].
  clear K. unfold ihi_s70. thaw FR.
  assert (EQS: (if negb (xnul =? 0) then xb else nullval) = xb /\ (if negb (nnul =? 0) then nb else nullval) = nb /\
              (if negb (cnul =? 0) then cb else nullval) = cb).
  { destruct F as (_ & _ & _ & _ & _ & _ & _ & _ & _ & X1 & _ & _ & _ & X2 & _ & _ & _ & X3).
    cbn [b_xnul b_nnul b_cnul h_xb h_nb h_cb] in X1, X2, X3.
    split; [|split]; [destruct (Z.eqb_spec xnul 0) | destruct (Z.eqb_spec nnul 0) | destruct (Z.eqb_spec cnul 0)];
      cbn; try reflexivity; symmetry; tauto. }
  destruct EQS as (EX1 & EX2 & EX3).
  cbn [v_s_ v_h_ v_xs_ v_ns_ v_cs_ v_osn_ b_w b_xmax b_nmax b_cmax b_xnul b_nnul b_cnul p_src p_xf p_nf p_cf
       h_xb h_nb h_cb h_xq h_nq h_cq ihi_h0 h_xbuf h_nbuf h_cbuf].
  unfold ih_htup; cbn [h_text h_time h_xflags h_os h_xp h_extra_len h_extra_max h_np h_name_max h_cp h_comm_max
       h_hcrc h_done ihi_h0 b_xnul b_nnul b_cnul b_xmax b_nmax b_cmax].
  rewrite EX1, EX2, EX3.
  unfold_data_at (data_at _ _ _ vh).
  entailer!.
Qed.

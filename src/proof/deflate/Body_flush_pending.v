(** * The body of deflate.c's flush_pending against its shared specification (DSpec.flush_pending_spec): ob_flush_pending. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Arith.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.trees.TLemmas.
Require Import Zlib.proof.deflate.Obligations.
Require Import Zlib.proof.zutil.Libc.
Require Import Zlib.deflate.code.

#[export] Existing Instance DCS.CS.

Open Scope cmodel_scope.

(** ** Byte arrays: slices *)
Lemma fp_tuchar_offset0 n j p:
  field_compatible (tarray tuchar n) [] p -> 0 <= j <= n ->
  @field_address0 DCS.CS (Tarray tuchar n noattr) [ArraySubsc j] p = offset_val j p.
Proof.
  intros. rewrite field_address0_offset.
  - simpl. f_equal. lia.
  - eapply field_compatible0_cons_Tarray; [reflexivity | auto | lia].
Qed.

Lemma fp_split3 sh n a b (v: list val) p:
  field_compatible (tarray tuchar n) [] p -> 0 <= a <= b -> b <= n -> Zlength v = n ->
  @data_at DCS.CS sh (tarray tuchar n) v p =
  (@data_at DCS.CS sh (tarray tuchar a) (sublist 0 a v) p *
   @data_at DCS.CS sh (tarray tuchar (b - a)) (sublist a b v) (offset_val a p) *
   @data_at DCS.CS sh (tarray tuchar (n - b)) (sublist b n v) (offset_val b p))%logic.
Proof.
  intros FC A B L.
  unfold tarray. rewrite (split3_data_at_Tarray_tuchar sh n a b v p) by (first [exact L | lia]).
  rewrite !fp_tuchar_offset0 by (auto; lia). reflexivity.
Qed.

(** ** The model *)
Lemma mb_definedb_spec b lo hi : mb_definedb b lo hi = true ->
  0 <= lo /\ hi <= Zlength (mb_val b) /\ forall i, lo <= i < hi -> Znth i (mb_def b) = true.
Proof.
  unfold mb_definedb. intros H. apply andb_prop in H. destruct H as [H H2].
  apply andb_prop in H. destruct H as [H0 H1]. apply Z.leb_le in H0. apply Z.leb_le in H1.
  split; [lia | split; [lia |]]. intros i Hi.
  rewrite forallb_forall in H2. apply H2. apply in_map_iff.
  exists (Z.to_nat (i - lo)). split; [lia |]. apply in_seq. lia.
Qed.

(** The defined slice of pending_buf is bytes. *)
Lemma sublist_pb_vals_def b m lo hi :
  Zlength m = Zlength b -> 0 <= lo <= hi -> hi <= Zlength b ->
  (forall i, lo <= i < hi -> Znth i m = true) ->
  sublist lo hi (pb_vals b m) = byte_vals (sublist lo hi b).
Proof.
  intros L H1 H2 D. apply Znth_eq_ext.
  - rewrite Zlength_sublist, Zlength_byte_vals, Zlength_sublist by (rewrite ?Zlength_pb_vals; lia). lia.
  - intros i Hi. rewrite Zlength_sublist in Hi by (rewrite ?Zlength_pb_vals; lia).
    rewrite Znth_sublist by lia. rewrite Znth_byte_vals by (rewrite Zlength_sublist; lia).
    rewrite Znth_sublist by lia. rewrite Znth_pb_vals by lia. rewrite D by lia. reflexivity.
Qed.

Lemma bytes_ok_sublist_mb o m lo hi :
  out_ok o m -> 0 <= lo <= hi -> hi <= Zlength (o_buf o) ->
  (forall i, lo <= i < hi -> Znth i m = true) ->
  bytes_ok (sublist lo hi (o_buf o)).
Proof.
  intros [[L K] _] H1 H2 D. cbn in L, K. unfold bytes_ok. apply Forall_Znth. intros i Hi.
  rewrite Zlength_sublist in Hi by lia. rewrite Znth_sublist by lia.
  specialize (K (i + lo) ltac:(lia) (D (i + lo) ltac:(lia))). rep_lia.
Qed.

(** Projections of the setters. *)
Lemma d_pending_set_d_out s o : d_pending (set_d_out s o) = o_pending (fst o).
Proof. reflexivity. Qed.
Lemma d_po_set_d_out s o : d_po (set_d_out s o) = d_po s.
Proof. reflexivity. Qed.
Lemma d_pbm_set_d_out s o : d_pbm (set_d_out s o) = snd o.
Proof. reflexivity. Qed.
Lemma tr_out_set_d_out s o : tr_out (d_tr (set_d_out s o)) = fst o.
Proof. reflexivity. Qed.
Lemma tr_out_set_d_po s x : tr_out (d_tr (set_d_po s x)) = tr_out (d_tr s).
Proof. reflexivity. Qed.
Lemma d_pbm_set_d_po s x : d_pbm (set_d_po s x) = d_pbm s.
Proof. reflexivity. Qed.
Lemma d_po_set_d_po s x : d_po (set_d_po s x) = x.
Proof. reflexivity. Qed.
Lemma set_d_out_set_d_po s x o : set_d_out (set_d_po s x) o = set_d_po (set_d_out s o) x.
Proof. reflexivity. Qed.
Lemma set_d_po_twice s x y : set_d_po (set_d_po s x) y = set_d_po s y.
Proof. reflexivity. Qed.
Lemma set_d_out_twice s o o' : set_d_out (set_d_out s o) o' = set_d_out s o'.
Proof. reflexivity. Qed.

(** The z_stream fields flush_pending does not touch (kept folded: they mention gv _zcalloc / gv _zcfree). *)
Definition fp_rest (z : strm) (p_strm p_in : val) (msgv : val) (gv : globals) : mpred :=
  (@field_at DCS.CS Ews t_strm (DOT _next_in) (offset_val (z_next_in z) p_in) p_strm *
  @field_at DCS.CS Ews t_strm (DOT _avail_in) (vi (z_avail_in z)) p_strm *
  @field_at DCS.CS Ews t_strm (DOT _total_in) (vl (z_total_in z)) p_strm *
  @field_at DCS.CS Ews t_strm (DOT _msg) msgv p_strm *
  @field_at DCS.CS Ews t_strm (DOT _zalloc) (gv _zcalloc) p_strm *
  @field_at DCS.CS Ews t_strm (DOT _zfree) (gv _zcfree) p_strm *
  @field_at DCS.CS Ews t_strm (DOT _opaque) nullval p_strm *
  @field_at DCS.CS Ews t_strm (DOT _adler) (vl (z_adler z)) p_strm *
  @field_at_ DCS.CS Ews t_strm (DOT _reserved) p_strm)%logic.

Lemma strm_at_fp z sp p_strm p_in p_out msgv gv :
  strm_at z sp p_strm p_in p_out msgv gv =
  (fp_rest z p_strm p_in msgv gv * @field_at DCS.CS Ews t_strm (DOT _state) sp p_strm *
   @field_at DCS.CS Ews t_strm (DOT _next_out) (offset_val (Zlength (z_out z)) p_out) p_strm *
   @field_at DCS.CS Ews t_strm (DOT _avail_out) (vi (z_avail_out z)) p_strm *
   @field_at DCS.CS Ews t_strm (DOT _total_out) (vl (z_total_out z)) p_strm)%logic.
Proof. unfold strm_at, fp_rest. apply pred_ext; cancel. Qed.

Lemma fp_rest_set z a b c p_strm p_in msgv gv :
  fp_rest (set_z_avail_out (set_z_total_out (set_z_out z a) b) c) p_strm p_in msgv gv = fp_rest z p_strm p_in msgv gv.
Proof. reflexivity. Qed.

Lemma fp_add_ptr p k n : isptr p -> 0 <= n <= Int.max_unsigned ->
  force_val (sem_add_ptr_int tuchar Unsigned (offset_val k p) (Vint (Int.repr n))) = offset_val (k + n) p.
Proof.
  intros P N. destruct p; try contradiction. simpl. unfold sem_add_ptr_int. simpl.
  f_equal. rewrite Ptrofs.add_assoc. f_equal.
  unfold Ptrofs.of_intu, Ptrofs.of_int. rewrite Int.unsigned_repr by rep_lia.
  rewrite ptrofs_mul_repr, ptrofs_add_repr. f_equal. lia.
Qed.

Lemma repr_u64 x : Int64.repr (u64 x) = Int64.repr x.
Proof.
  rewrite <- (Int64.repr_unsigned (Int64.repr x)), Int64.unsigned_repr_eq. reflexivity.
Qed.

Lemma out_ok_pending buf p bb bv bu m p' :
  out_ok (mkOut buf p bb bv bu) m -> 0 <= p' <= Int64.max_unsigned -> out_ok (mkOut buf p' bb bv bu) m.
Proof. intros [H1 [H2 [H3 H4]]] ?. split; [exact H1|]. cbn in *. repeat split; lia. Qed.

(** flush_pending's model step, explicitly. *)
Lemma c_flush_pending_inv s z r o m :
  c_tr_flush_bits (d_out s) = Some (o, m) ->
  c_flush_pending s z = Some r ->
  let p := o_pending o in
  let len := if p >? z_avail_out z then z_avail_out z else u32 p in
  (len = 0 /\ r = (set_d_out s (o, m), z)) \/
  (len <> 0 /\ mb_definedb (mkMB (o_buf o) m) (d_po s) (d_po s + len) = true /\
   r = (set_d_po (set_d_out s (mkOut (o_buf o) (p - len) (o_bi_buf o) (o_bi_valid o) (o_bi_used o), m))
           (if p - len =? 0 then 0 else d_po s + len),
        set_z_avail_out (set_z_total_out (set_z_out z (z_out z ++ sublist (d_po s) (d_po s + len) (o_buf o)))
                                         (u64 (z_total_out z + len))) (z_avail_out z - len)) /\
   len <= z_avail_out z).
Proof.
  intros F H. unfold c_flush_pending in H. rewrite F in H. cbn [bind] in H.
  rewrite ?d_pending_set_d_out, ?d_po_set_d_out, ?d_pbm_set_d_out, ?tr_out_set_d_out in H.
  cbn [fst snd] in H. cbv zeta. cbv zeta in H.
  set (len := if o_pending o >? z_avail_out z then z_avail_out z else u32 (o_pending o)) in *.
  destruct (Z.eqb_spec len 0) as [E|E].
  - left. split; [auto|]. congruence.
  - right. split; [auto|].
    unfold mb_read in H.
    destruct ((0 <=? len) && mb_definedb _ _ _)%bool eqn:D; [|discriminate]. cbn [bind] in H.
    apply andb_prop in D. destruct D as [D0 D]. apply Z.leb_le in D0. split; [exact D|].
    apply mb_definedb_spec in D. cbn [mb_val] in D. destruct D as [D1 [D2 _]].
    unfold out_put in H.
    destruct (Zlength _ <=? z_avail_out z) eqn:Lz; [|discriminate]. cbn [bind] in H.
    cbn [mb_val] in Lz, H. apply Z.leb_le in Lz. rewrite Zlength_sublist in Lz by lia.
    split; [| lia].
    rewrite ?tr_out_set_d_po, ?tr_out_set_d_out, ?d_pbm_set_d_po, ?d_pbm_set_d_out in H.
    cbn [fst snd o_pending o_buf o_bi_buf o_bi_valid o_bi_used] in H.
    rewrite ?set_d_out_set_d_po, ?set_d_out_twice, ?set_d_po_twice in H.
    destruct (o_pending o - len =? 0); injection H as <-; reflexivity.
Qed.

Lemma body_flush_pending : ob_flush_pending.
Proof.
  unfold ob_flush_pending. start_function.
  destruct (c_tr_flush_bits (d_out s)) as [[o m]|] eqn:F;
    [| unfold c_flush_pending in H0; rewrite F in H0; discriminate].
  pose proof (c_flush_pending_inv s z r o m F H0) as INV. cbv zeta in INV.
  rewrite strm_at_fp. Intros.
  assert_PROP (isptr sp) as Psp by (unfold out_at; entailer!).
  forward.
  forward_call (sp, pbp, tr_out (d_tr s), d_pbm s, (o, m)).
  cbn [fst snd]. destruct o as [buf p bb bv bu]. open_out_at.
  assert (Hok := H1). destruct H1 as [[HLm _] [HLb [Hp _]]]. cbn [mb_val mb_def o_buf o_pending] in *.
  assert (Hz := H). destruct H as (_ & _ & _ & _ & _ & _ & Hav & HLout & Htot & _ & _ & Hout).
  unfold u32_ok, u64_ok in Hav, Htot.
  set (av := z_avail_out z) in *.
  set (len := if p >? av then av else u32 p) in *.
  assert (Hlen: 0 <= len <= av /\ len <= p /\ (p <= av -> len = p) /\ (p > av -> len = av)).
  { unfold len. destruct (Z.gtb_spec p av).
    - lia.
    - unfold u32. rewrite Z.mod_small by rep_lia. lia. }
  destruct Hlen as (Hl0 & Hlp & Hle & Hgt).
  forward. forward.
  forward_if (temp _t'1 (Vint (Int.repr len))).
  { forward. forward. entailer!. rewrite ?Int.unsigned_repr in H by rep_lia. rewrite Hgt by lia. reflexivity. }
  { forward. forward. entailer!. rewrite ?Int.unsigned_repr in H by rep_lia. rewrite Hle by lia. reflexivity. }
  forward. forward_if.
  - destruct INV as [[_ ->] | [L1 _]]; [| contradiction].
    forward.
    rewrite d_po_set_d_out, tr_out_set_d_out, d_pbm_set_d_out. cbn [fst snd].
    unfold rest_after. rewrite Z.sub_diag. rewrite strm_at_fp.
    sep_apply (out_at_fields buf p bb bv bu m sp pbp Hok).
    unfold out_space. Intros. rewrite sublist_same by auto.
    entailer!.
  - destruct INV as [[L0 _] | (L1 & Def & Er & _)]; [subst; contradiction |].
    apply mb_definedb_spec in Def. cbn [mb_val mb_def] in Def. destruct Def as (Dpo & Dhi & Dm).
    set (po := d_po s) in *.
    set (Lz := Zlength (z_out z)) in *.
    assert (HLz: 0 <= Lz) by (unfold Lz; apply Zlength_nonneg).
    set (data := sublist po (po + len) buf).
    assert (Ldata: Zlength data = len) by (unfold data; rewrite Zlength_sublist by lia; lia).
    unfold out_space. Intros. fold av Lz.
    assert_PROP (field_compatible (tarray tuchar (Lz + av)) [] pout) as FCo by entailer!.
    assert_PROP (field_compatible (tarray tuchar (Zlength buf)) [] pbp) as FCp by entailer!.
    assert (Pout: isptr pout) by (destruct FCo; auto).
    assert (Ppb: isptr pbp) by (destruct FCp; auto).
    forward. forward.
    rewrite (fp_split3 Ews (Lz + av) Lz (Lz + len) (map vi (z_out z) ++ rest) pout)
      by (auto; try lia; rewrite ?Zlength_app, ?Zlength_map; unfold Lz, av in *; lia).
    rewrite (fp_split3 Ews (Zlength buf) po (po + len) (pb_vals buf m) pbp)
      by (auto; try lia; rewrite ?Zlength_pb_vals; lia).
    rewrite (sublist_pb_vals_def buf m po (po + len)) by (auto; lia). fold data.
    assert (E1: sublist 0 Lz (map vi (z_out z) ++ rest) = map vi (z_out z)) by list_solve.
    assert (E2: sublist Lz (Lz + len) (map vi (z_out z) ++ rest) = sublist 0 len rest) by list_solve.
    assert (E3: sublist (Lz + len) (Lz + av) (map vi (z_out z) ++ rest) = sublist len av rest) by list_solve.
    rewrite E1, E2, E3. replace (Lz + len - Lz) with len by lia. replace (po + len - po) with len by lia.
    Intros.
    forward_call (Ews, offset_val Lz pout, Ews, offset_val po pbp, data).
    { entailer!. rewrite Ldata. simpl.
      destruct pout; try contradiction; destruct pbp; try contradiction. simpl.
      rewrite Int.unsigned_repr by rep_lia. reflexivity. }
    { rewrite Ldata. sep_apply (data_at_data_at_ Ews (tarray tuchar len) (sublist 0 len rest) (offset_val Lz pout)).
      cancel. }
    { exact (bytes_ok_sublist_mb _ m po (po + len) Hok ltac:(lia) Dhi Dm). }
    rewrite Ldata.
    forward. forward. forward. forward. forward. forward. forward. forward. forward. forward. forward.
    rewrite !Int.unsigned_repr by rep_lia.
    rewrite !fp_add_ptr by (auto; rep_lia).
    rewrite sub_repr32, add64_repr, sub64_repr.
    forward_if.
    + forward. forward.
      assert (P0: p - len = 0).
      { assert (U: Int64.unsigned (Int64.repr (p - len)) = 0) by (rewrite H2; reflexivity).
        rewrite Int64.unsigned_repr in U by rep_lia. lia. }
      rewrite Er. cbn [fst snd].
      rewrite d_po_set_d_po, tr_out_set_d_po, tr_out_set_d_out, d_pbm_set_d_po, d_pbm_set_d_out. cbn [fst snd].
      rewrite P0. cbn [Z.eqb]. rewrite isptr_offset_val_zero by auto.
      unfold rest_after. rewrite strm_at_fp, fp_rest_set. unfold out_space, out_at.
      cbn [z_out z_avail_out z_total_out set_z_avail_out set_z_total_out set_z_out o_buf o_pending o_bi_buf o_bi_valid o_bi_used].
      fold data. rewrite Zlength_app, Ldata. fold Lz. replace (Lz + len - Lz) with len by lia.
      fold av in H1. rewrite H1.
      replace (Lz + len + (av - len)) with (Lz + av) by lia.
      rewrite (fp_split3 Ews (Lz + av) Lz (Lz + len) (map vi (z_out z ++ data) ++ sublist len av rest) pout)
        by (auto; try lia; rewrite ?Zlength_app, ?Zlength_map, ?Zlength_app, ?Zlength_sublist by lia; change (Zlength (z_out z)) with Lz; lia).
      rewrite (fp_split3 Ews (Zlength buf) po (po + len) (pb_vals buf m) pbp)
        by (auto; try lia; rewrite ?Zlength_pb_vals; lia).
      rewrite (sublist_pb_vals_def buf m po (po + len)) by (auto; lia). fold data.
      assert (F1: sublist 0 Lz (map vi (z_out z ++ data) ++ sublist len av rest) = map vi (z_out z)) by list_solve.
      assert (F2: sublist Lz (Lz + len) (map vi (z_out z ++ data) ++ sublist len av rest) = map vi data) by list_solve.
      assert (F3: sublist (Lz + len) (Lz + av) (map vi (z_out z ++ data) ++ sublist len av rest) = sublist len av rest) by list_solve.
      rewrite F1, F2, F3. change (map vi data) with (byte_vals data).
      replace (Lz + len - Lz) with len by lia. replace (po + len - po) with len by lia.
      unfold vi, vl. rewrite repr_u64.
      entailer!.
      split; [list_solve |]. apply (out_ok_pending _ p); auto; lia.
    + forward.
      assert (P0: p - len <> 0).
      { intro Z0. apply H2. rewrite Z0. reflexivity. }
      rewrite Er. cbn [fst snd].
      rewrite d_po_set_d_po, tr_out_set_d_po, tr_out_set_d_out, d_pbm_set_d_po, d_pbm_set_d_out. cbn [fst snd].
      rewrite (proj2 (Z.eqb_neq _ _) P0).
      unfold rest_after. rewrite strm_at_fp, fp_rest_set. unfold out_space, out_at.
      cbn [z_out z_avail_out z_total_out set_z_avail_out set_z_total_out set_z_out o_buf o_pending o_bi_buf o_bi_valid o_bi_used].
      fold data. rewrite Zlength_app, Ldata. fold Lz. replace (Lz + len - Lz) with len by lia.
      fold av in H1. rewrite H1.
      replace (Lz + len + (av - len)) with (Lz + av) by lia.
      rewrite (fp_split3 Ews (Lz + av) Lz (Lz + len) (map vi (z_out z ++ data) ++ sublist len av rest) pout)
        by (auto; try lia; rewrite ?Zlength_app, ?Zlength_map, ?Zlength_app, ?Zlength_sublist by lia; change (Zlength (z_out z)) with Lz; lia).
      rewrite (fp_split3 Ews (Zlength buf) po (po + len) (pb_vals buf m) pbp)
        by (auto; try lia; rewrite ?Zlength_pb_vals; lia).
      rewrite (sublist_pb_vals_def buf m po (po + len)) by (auto; lia). fold data.
      assert (F1: sublist 0 Lz (map vi (z_out z ++ data) ++ sublist len av rest) = map vi (z_out z)) by list_solve.
      assert (F2: sublist Lz (Lz + len) (map vi (z_out z ++ data) ++ sublist len av rest) = map vi data) by list_solve.
      assert (F3: sublist (Lz + len) (Lz + av) (map vi (z_out z ++ data) ++ sublist len av rest) = sublist len av rest) by list_solve.
      rewrite F1, F2, F3. change (map vi data) with (byte_vals data).
      replace (Lz + len - Lz) with len by lia. replace (po + len - po) with len by lia.
      unfold vi, vl. rewrite repr_u64.
      entailer!.
      split; [list_solve |]. apply (out_ok_pending _ p); auto; lia.
Qed.

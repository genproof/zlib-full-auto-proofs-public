(* Kit of case EXTRA (CaseEXTRA5.v): the pieces of its body as statements (taken from code.v), the
   crc32 over the input (a copy of NCCrc5.v's lemma with EXTRA's temps), the zmemcpy into
   head->extra, and the model facts. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate.ExKit5.
Require Import Zlib.proof.inflate.Steps2.
Require Import Zlib.proof.inflate.MwfLemmas.
Require Import Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* ---------------------------------------------------------------------------------------------- *)
(* the pieces of the body                                                                         *)

Definition ex_then : statement := Eval cbv beta iota zeta delta [case_body inflate_LS find_switch f_inflate fn_body ls_drop] in
  match case_body 5 with Ssequence (Ssequence _ (Sifthenelse _ t _)) _ => t | _ => Sskip end.
Definition ex_cpy : statement := Eval cbv beta iota zeta delta [ex_then] in
  match ex_then with Ssequence _ (Ssequence _ (Ssequence (Sifthenelse _ c _) _)) => c | _ => Sskip end.
Definition ex_mb : statement := Eval cbv beta iota zeta delta [ex_cpy] in
  match ex_cpy with Ssequence mb _ => mb | _ => Sskip end.
Definition ex_crcb : statement := Eval cbv beta iota zeta delta [ex_cpy] in
  match ex_cpy with Ssequence _ (Ssequence c _) => c | _ => Sskip end.
Definition ex_upd : statement := Eval cbv beta iota zeta delta [ex_cpy] in
  match ex_cpy with Ssequence _ (Ssequence _ u) => u | _ => Sskip end.


(* ---------------------------------------------------------------------------------------------- *)
(* the crc32 over the copied input bytes (as in NCCrc5.v, with EXTRA's temps)                      *)

Definition crcv (fl wr ck: Z) (d: list Z) : Z :=
  if andb (negb (Z.land fl 512 =? 0)) (negb (Z.land wr 4 =? 0)) then ref_crc32 ck d else ck.

Lemma crc_val_crcv: forall s d, crc_val s d = crcv (i_flags s) (i_wrap s) (i_check s) d.
Proof. reflexivity. Qed.

Lemma exc_da_cs: forall sh n (v: list val) p,
  @data_at Zlib.units.Inflate.CS sh (tarray tuchar n) v p = @data_at Zlib.units.Crc32.CS sh (tarray tuchar n) v p.
Proof.
  intros.
  assert (E: @data_at Zlib.units.Crc32.CS sh (tarray tuchar n) v = @data_at Zlib.units.Inflate.CS sh (tarray tuchar n) v).
  { apply (@data_at_change_composite _ _ Zlib.proof.inflate.Callees.CCE_crc32); [apply JMeq_refl | reflexivity]. }
  rewrite E. reflexivity.
Qed.

Lemma exc_and_repr: forall a b, Int.and (Int.repr a) (Int.repr b) = Int.repr (Z.land a b).
Proof.
  intros. apply Int.same_bits_eq; intros i Hi.
  rewrite Int.bits_and by auto. rewrite !Int.testbit_repr by auto. rewrite Z.land_spec. reflexivity.
Qed.

Lemma exc_land_range: forall a b, 0 <= b -> 0 <= Z.land a b <= b.
Proof.
  intros a b H. split.
  - apply Z.land_nonneg; auto.
  - apply Zbits.Ztestbit_le; auto. intros i _ T. rewrite Z.land_spec in T. apply andb_prop in T. tauto.
Qed.

Lemma exc_flagbit: forall a b, Int.and (Int.repr a) (Int.repr b) <> Int.zero -> (Z.land a b =? 0) = false.
Proof.
  intros a b H. rewrite exc_and_repr in H. apply Z.eqb_neq. intro E. rewrite E in H. apply H. reflexivity.
Qed.

Lemma exc_flagbit0: forall a b, Int.and (Int.repr a) (Int.repr b) = Int.zero -> 0 <= b <= Int.max_signed ->
  (Z.land a b =? 0) = true.
Proof.
  intros a b H Hb. rewrite exc_and_repr in H. apply Z.eqb_eq.
  pose proof (exc_land_range a b ltac:(lia)).
  apply (f_equal Int.unsigned) in H. rewrite Int.unsigned_repr in H by rep_lia. exact H.
Qed.

Lemma exc_tbool: forall x, 0 <= x <= Int.max_signed ->
  Vint (if Int.eq (Int.repr x) Int.zero then Int.zero else Int.one) = Vint (Int.repr (if x =? 0 then 0 else 1)).
Proof.
  intros x H. destruct (Z.eqb_spec x 0).
  - subst. reflexivity.
  - rewrite Int.eq_false; [reflexivity | ]. intro E. apply (f_equal Int.unsigned) in E.
    rewrite Int.unsigned_repr in E by rep_lia. apply n. exact E.
Qed.

Lemma semax_crc_extra {Espec: OracleKind} sp cpy gv tsh fl wr ck ish ip q inn icont data:
  readable_share tsh -> readable_share ish -> isptr ip ->
  0 <= q -> q + cpy <= inn -> Zlength icont = inn -> 0 < inn ->
  sublist q (q + cpy) icont = byte_vals data -> Zlength data = cpy -> bytes_ok data ->
  0 <= cpy <= Int.max_unsigned -> srange fl -> 0 <= wr <= 15 -> lrange ck ->
  semax Delta_cases5
   (PROP () LOCAL (temp _state sp; temp _next (offset_val q ip); temp _copy (zv cpy); gvars gv)
    SEP (field_at Ews t_state (DOT _flags) (zv fl) sp; field_at Ews t_state (DOT _wrap) (zv wr) sp;
         field_at Ews t_state (DOT _check) (lv ck) sp; crc_table_at tsh gv;
         data_at ish (tarray tuchar inn) icont ip))
   ex_crcb
   (normal_ret_assert
    (PROP () LOCAL (temp _state sp; temp _next (offset_val q ip); temp _copy (zv cpy); gvars gv)
     SEP (field_at Ews t_state (DOT _flags) (zv fl) sp; field_at Ews t_state (DOT _wrap) (zv wr) sp;
          field_at Ews t_state (DOT _check) (lv (crcv fl wr ck data)) sp; crc_table_at tsh gv;
          data_at ish (tarray tuchar inn) icont ip))).
Proof.
  intros RT RI PI Q0 QC LI NP SB LD BD CR FR WR KR.
  unfold ex_crcb, crcv. abbreviate_semax.
  forward.
  match goal with |- semax _ (PROPx ?A (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx A (LOCALx (temp _t'30 (Vint (Int.repr (if andb (negb (Z.land fl 512 =? 0)) (negb (Z.land wr 4 =? 0)) then 1 else 0))) :: Q) (SEPx R))) end.
  - forward. forward. entailer!.
    match goal with H: Int.and _ _ <> Int.zero |- _ => rewrite (exc_flagbit _ _ H) end.
    cbn [negb andb]. unfold srange in FR.
    rewrite exc_tbool by (pose proof (exc_land_range wr 4 ltac:(lia)); rep_lia).
    destruct (Z.land wr 4 =? 0); reflexivity.
  - forward. entailer!.
    match goal with H: Int.and _ _ = Int.zero |- _ => rewrite (exc_flagbit0 _ _ H) by rep_lia end.
    reflexivity.
  - destruct (andb (negb (Z.land fl 512 =? 0)) (negb (Z.land wr 4 =? 0))).
    + forward_if; [ | match goal with H: Int.repr 1 = Int.zero |- _ => discriminate H end].
      forward.
      forward_call (ck, offset_val q ip, cpy, false, ish, ip, q, inn, icont, data, false, Tsh, gv, tsh).
      { rewrite <- exc_da_cs. cancel. }
      { try (split; [ | apply cbuf_valid_pos; lia]).
        unfold cbuf_ok. split; [reflexivity | ]. split; [auto | ]. split; [lia | ]. split; [lia | ].
        split; [exact LD | ]. split; [exact BD | ]. exact SB. }
      try rewrite <- exc_da_cs.
      forward.
      entailer!.
    + forward_if; [ match goal with H: Int.repr 0 <> Int.zero |- _ => exfalso; apply H; reflexivity end | ].
      forward. entailer!.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* zmemcpy(head->extra + len, next, ..)                                                           *)

Lemma ex_arr_slice: forall sh p n (c: list val) a k,
  0 <= a -> 0 <= k -> a + k <= n -> Zlength c = n -> field_compatible (tarray tuchar n) [] p ->
  data_at sh (tarray tuchar n) c p =
  data_at sh (tarray tuchar a) (sublist 0 a c) p *
  data_at sh (tarray tuchar k) (sublist a (a + k) c) (offset_val a p) *
  data_at sh (tarray tuchar (n - (a + k))) (sublist (a + k) n c) (offset_val (a + k) p).
Proof.
  intros sh p n c a k Ha Hk Hn Hc FC.
  unfold tarray. rewrite (split3_data_at_Tarray_tuchar sh n a (a + k) c p) by lia.
  rewrite <- !(offset_val_field_address0_tuchar n) by (auto; lia).
  replace (a + k - a) with k by lia. reflexivity.
Qed.

Lemma ex_in_slice: forall sh p lo n c inp nx k,
  in_ok (InBuf sh p lo n c) inp -> 0 <= nx -> 0 <= k -> nx + k <= Zlength inp ->
  field_compatible (tarray tuchar n) [] p ->
  data_at sh (tarray tuchar n) c p =
  data_at sh (tarray tuchar (lo + nx)) (sublist 0 (lo + nx) c) p *
  data_at sh (tarray tuchar k) (byte_vals (sublist nx (nx + k) inp)) (offset_val (lo + nx) p) *
  data_at sh (tarray tuchar (n - (lo + nx + k))) (sublist (lo + nx + k) n c) (offset_val (lo + nx + k) p).
Proof.
  intros sh p lo n c inp nx k (Hsh & Hp & Hlo & Hn & Hc & Hmax & Hsub & Hb) H1 H2 H3 FC.
  rewrite (ex_arr_slice sh p n c (lo + nx) k) by (auto; lia).
  f_equal; f_equal. f_equal.
  rewrite <- sublist_byte_vals.
  assert (E: byte_vals inp = sublist lo (lo + Zlength inp) c) by (rewrite Hsub; reflexivity).
  rewrite E. rewrite sublist_sublist by lia. f_equal; lia.
Qed.

Lemma ex_put_slice: forall sh p max buf pos d,
  Zlength buf = max -> 0 <= pos -> pos + Zlength d <= max -> field_compatible (tarray tuchar max) [] p ->
  data_at sh (tarray tuchar max) (byte_vals (put_bytes buf pos d)) p =
  data_at sh (tarray tuchar pos) (sublist 0 pos (byte_vals buf)) p *
  data_at sh (tarray tuchar (Zlength d)) (byte_vals d) (offset_val pos p) *
  data_at sh (tarray tuchar (max - (pos + Zlength d))) (sublist (pos + Zlength d) max (byte_vals buf))
    (offset_val (pos + Zlength d) p).
Proof.
  intros sh p max buf pos d L P Q FC.
  pose proof (Zlength_nonneg d).
  assert (LP: Zlength (put_bytes buf pos d) = max) by (rewrite put_bytes_len; lia).
  rewrite (ex_arr_slice sh p max _ pos (Zlength d)) by (auto; try lia; rewrite Zlength_byte_vals; lia).
  unfold put_bytes. rewrite !byte_vals_app, <- !sublist_byte_vals.
  pose proof (Zlength_byte_vals buf). pose proof (Zlength_byte_vals d).
  f_equal; [f_equal | ]; f_equal; list_solve.
Qed.

(* the head after the zmemcpy *)
Definition xb_upd (hd: bool) (h: hstate) (L c: Z) (inp: list Z) (nx: Z) : hstate :=
  let len := u32 (h_extra_len h - L) in
  if andb (andb hd (h_xp h)) (len <? h_extra_max h) then
    set_h_xbuf h (put_bytes (h_xbuf h) len (sublist nx (nx + extra_n len c (h_extra_max h)) inp))
  else h.

Definition hd_part (hd: bool) (hsh: share) (headp xb nb cb: val) (h: hstate) : mpred :=
  if hd then head_rep hsh headp xb nb cb h else emp.
Definition hd_tok (hd: bool) (xb nb cb: val) (h: hstate) : mpred :=
  if hd then btok xb (h_extra_max h) * btok nb (h_name_max h) * btok cb (h_comm_max h) else emp.

Lemma xb_weak_valid: forall xb max (bv: list val) (R: mpred), isptr xb -> 0 <= max ->
  data_at Ews (tarray tuchar max) bv xb * (if zeq max 0 then malloc_token Ews (tarray tuchar 0) xb else emp) * R
  |-- denote_tc_test_eq xb (Vlong (Int64.repr 0)).
Proof.
  intros xb max bv R P M.
  apply denote_tc_test_eq_split; [ | change (Vlong (Int64.repr 0)) with nullval; apply valid_pointer_null].
  destruct (zeq max 0).
  - sep_apply (malloc_token_valid_pointer Ews (tarray tuchar 0) xb). auto with valid_pointer.
  - apply sepcon_valid_pointer1. apply sepcon_valid_pointer1.
    apply data_at_valid_ptr; [auto | simpl; rewrite Z.max_r by lia; lia].
Qed.

Lemma xb_cmp_one: forall xb, isptr xb ->
  Vint Int.one = force_val (sem_cast_i2bool (force_val (sem_cmp_pp Cne xb (Vlong (Int64.repr 0))))).
Proof. intros xb P. destruct xb; try contradiction. reflexivity. Qed.

Lemma ex_ltu_u32: forall x m, 0 <= m <= Int.max_unsigned ->
  bool2val (Int.ltu (Int.repr x) (Int.repr m)) = Vint (Int.repr (if u32 x <? m then 1 else 0)).
Proof.
  intros x m M. unfold Int.ltu. rewrite (Int.unsigned_repr m) by lia. rewrite Int.unsigned_repr_eq.
  change Int.modulus with (2 ^ 32). fold (u32 x).
  destruct (zlt (u32 x) m); destruct (Z.ltb_spec (u32 x) m); try lia; reflexivity.
Qed.

Lemma ex_sub_u32: forall a b, Int.sub (Int.repr a) (Int.repr b) = Int.repr (u32 (a - b)).
Proof. intros. rewrite repr_u32. apply Int.eqm_samerepr. apply Int.eqm_sub; apply Int.eqm_sym, Int.eqm_unsigned_repr. Qed.

Lemma ex_ltu_add: forall m a b, 0 <= m <= Int.max_unsigned ->
  Int.ltu (Int.repr m) (Int.add (Int.repr a) (Int.repr b)) = (m <? u32 (a + b)).
Proof.
  intros m a b M. rewrite add_repr. unfold Int.ltu. rewrite (Int.unsigned_repr m) by lia.
  rewrite Int.unsigned_repr_eq. change Int.modulus with (2 ^ 32). fold (u32 (a + b)).
  destruct (zlt m (u32 (a + b))); destruct (Z.ltb_spec m (u32 (a + b))); try lia; reflexivity.
Qed.

Lemma semax_extra_mb {Espec: OracleKind} sp headp hsh xb nb cb h hd L c ish ip ilo inn icont inp nx:
  writable_share hsh -> hwf h -> (hd = true -> h_xp h = true -> xb <> nullval) ->
  in_ok (InBuf ish ip ilo inn icont) inp -> 0 <= nx -> nx + c <= Zlength inp -> 0 < c <= Int.max_signed ->
  urange L ->
  semax Delta_cases5
   (PROP () LOCAL (temp _state sp; temp _copy (zv c); temp _next (offset_val (ilo + nx) ip))
    SEP (field_at Ews t_state (DOT _head) (if hd then headp else nullval) sp;
         field_at Ews t_state (DOT _length) (zv L) sp;
         hd_part hd hsh headp xb nb cb h;
         data_at ish (tarray tuchar inn) icont ip;
         hd_tok hd xb nb cb h))
   ex_mb
   (normal_ret_assert
    (PROP () LOCAL (temp _state sp; temp _copy (zv c); temp _next (offset_val (ilo + nx) ip))
     SEP (field_at Ews t_state (DOT _head) (if hd then headp else nullval) sp;
          field_at Ews t_state (DOT _length) (zv L) sp;
          hd_part hd hsh headp xb nb cb (xb_upd hd h L c inp nx);
          data_at ish (tarray tuchar inn) icont ip;
          hd_tok hd xb nb cb h))).
Proof.
  intros HS HW HX HIN HNX HNC HC HL.
  unfold ex_mb.
  destruct hd.
  2:{ abbreviate_semax. unfold xb_upd. cbn [andb]. unfold hd_part, hd_tok.
      forward.
      match goal with |- semax _ (PROPx ?A (LOCALx (_ :: ?Q) (SEPx ?R))) _ _ =>
        forward_if (PROPx A (LOCALx (temp _t'26 (Vint Int.zero) :: Q) (SEPx R))) end.
      { discriminate. }
      { forward. entailer!. }
      match goal with |- semax _ (PROPx ?A (LOCALx (_ :: ?Q) (SEPx ?R))) _ _ =>
        forward_if (PROPx A (LOCALx (temp _t'27 (Vint Int.zero) :: Q) (SEPx R))) end.
      { exfalso. auto. }
      { forward. entailer!. }
      forward_if.
      { exfalso. auto. }
      forward. entailer!. }
  unfold hd_part, hd_tok, head_rep.
  destruct (h_xp h) eqn:Hxp.
  2:{ unfold xb_upd. rewrite Hxp. cbn [andb].
      abbreviate_semax. Intros. forward.
      match goal with |- semax _ (PROPx ?A (LOCALx (_ :: ?Q) (SEPx ?R))) _ _ =>
        forward_if (PROPx A (LOCALx (temp _t'26 (Vint Int.zero) :: Q) (SEPx R))) end.
      { forward. forward. forward. entailer!. }
      { assert_PROP (isptr headp) by entailer!. subst. contradiction. }
      match goal with |- semax _ (PROPx ?A (LOCALx (_ :: ?Q) (SEPx ?R))) _ _ =>
        forward_if (PROPx A (LOCALx (temp _t'27 (Vint Int.zero) :: Q) (SEPx R))) end.
      { exfalso. auto. }
      { forward. entailer!. }
      forward_if.
      { exfalso. auto. }
      forward. try rewrite Hxp. entailer!. }
  assert (XB: xb <> nullval) by auto.
  rewrite !(hbuf_rep_pos xb) by exact XB.
  assert (XBT: btok xb (h_extra_max h) = if zeq (h_extra_max h) 0 then malloc_token Ews (tarray tuchar 0) xb else emp).
  { unfold btok. rewrite if_false by exact XB. reflexivity. }
  rewrite !XBT. clear XBT.
  pose proof (u32_range (h_extra_len h - L)) as UL.
  pose proof (hw_extra_max _ HW) as XM.
  pose proof (hw_xbuf _ HW) as [XL XOK].
  assert (XU: xb_upd true h L c inp nx =
              if u32 (h_extra_len h - L) <? h_extra_max h then
                set_h_xbuf h (put_bytes (h_xbuf h) (u32 (h_extra_len h - L))
                  (sublist nx (nx + extra_n (u32 (h_extra_len h - L)) c (h_extra_max h)) inp))
              else h) by (unfold xb_upd; rewrite Hxp; reflexivity).
  rewrite XU. clear XU.
  set (lv0 := u32 (h_extra_len h - L)) in *.
  abbreviate_semax. Intros. forward.
  match goal with |- semax _ (PROPx ?A (LOCALx (_ :: ?Q) (SEPx ?R))) _ _ =>
        forward_if (PROPx A (LOCALx (temp _t'26 (Vint Int.one) :: Q) (SEPx R))) end.
  { forward. forward. forward.
    { entailer!. eapply derives_trans; [ | apply (xb_weak_valid xb (h_extra_max h) (byte_vals (h_xbuf h)) TT)];
        [cancel | auto | lia]. }
    entailer!. apply xb_cmp_one. auto. }
  { assert_PROP (isptr headp) by entailer!. subst. contradiction. }
  match goal with |- semax _ (PROPx ?A (LOCALx (_ :: ?Q) (SEPx ?R))) _ _ =>
        forward_if (PROPx A (LOCALx (temp _t'27 (Vint (Int.repr (if lv0 <? h_extra_max h then 1 else 0))) ::
                                     temp _len (Vint (Int.repr lv0)) :: Q) (SEPx R))) end.
  { forward. forward. forward. forward. forward. forward. forward. forward.
    entailer!. split; [symmetry; apply ex_ltu_u32; rep_lia | unfold lv0; rewrite repr_u32; reflexivity]. }
  { exfalso. apply Int.one_not_zero. exact H. }
  unfold abbreviate in POSTCONDITION. subst POSTCONDITION.
  destruct (lv0 <? h_extra_max h) eqn:Hlt.
  - apply Z.ltb_lt in Hlt.
    pose proof (extra_n_range lv0 c (h_extra_max h) ltac:(unfold urange in UL; lia) ltac:(lia) ltac:(rep_lia)) as [N1 N2].
    set (n := extra_n lv0 c (h_extra_max h)) in *.
    cbn [set_h_xbuf h_text h_time h_xflags h_os h_xp h_extra_len h_extra_max h_np h_name_max h_cp h_comm_max h_hcrc h_done h_xbuf h_nbuf h_cbuf].
    abbreviate_semax.
    forward_if.
    2:{ exfalso. apply Int.one_not_zero. exact H. }
    forward. forward.
    destruct (zeq (h_extra_max h) 0); [unfold urange in UL; lia | ].
    match goal with |- semax _ (PROPx ?A (LOCALx (_ :: _ :: ?Q) (SEPx ?R))) _ _ =>
        forward_if (PROPx A (LOCALx (temp _t'25 (Vint (Int.repr n)) :: Q) (SEPx R))) end.
    { rewrite Int.unsigned_repr_eq in H0. change Int.modulus with (2 ^ 32) in H0. fold (u32 (lv0 + c)) in H0.
      forward. forward. forward. entailer!.
      unfold n, extra_n. rewrite (proj2 (Z.ltb_lt _ _) H0). reflexivity. }
    { rewrite Int.unsigned_repr_eq in H0. change Int.modulus with (2 ^ 32) in H0. fold (u32 (lv0 + c)) in H0.
      forward. entailer!.
      unfold n, extra_n. rewrite (proj2 (Z.ltb_ge (h_extra_max h) (u32 (lv0 + c))) ltac:(lia)). reflexivity. }
    forward. forward.
    pose proof HIN as HIN'.
    destruct HIN' as (HIS & HIP & HILO & HINN & HIC & HIMAX & HISUB & HIB).
    assert_PROP (field_compatible (tarray tuchar inn) [] ip) as FCI by entailer!.
    assert_PROP (field_compatible (tarray tuchar (h_extra_max h)) [] xb) as FCX by entailer!.
    remember (sublist nx (nx + n) inp) as data eqn:Hd.
    assert (HZ: Zlength data = n) by (subst data; rewrite Zlength_sublist by lia; lia).
    rewrite (ex_in_slice ish ip ilo inn icont inp nx n) by (auto; lia).
    rewrite (ex_arr_slice Ews xb (h_extra_max h) (byte_vals (h_xbuf h)) lv0 n)
      by (auto; try (unfold urange in UL; lia); rewrite Zlength_byte_vals; lia).
    rewrite <- Hd. clearbody n. rewrite <- HZ in *.
    sep_apply (data_at_data_at_ Ews (tarray tuchar (Zlength data)) (sublist lv0 (lv0 + Zlength data) (byte_vals (h_xbuf h))) (offset_val lv0 xb)).
    forward_call (Ews, offset_val lv0 xb, ish, offset_val (ilo + nx) ip, data).
    { rewrite Hd. unfold bytes_ok in *. apply Forall_sublist. exact HIB. }
    rewrite Hxp.
    rewrite (ex_in_slice ish ip ilo inn icont inp nx (Zlength data)) by (auto; lia).
    rewrite (ex_put_slice Ews xb (h_extra_max h) (h_xbuf h) lv0 data) by (auto; unfold urange in UL; lia).
    rewrite <- Hd.
    entailer!.
  - abbreviate_semax. forward_if.
    { exfalso. auto. }
    forward. try rewrite Hxp. entailer!.
Unshelve. all: exact 0.
Qed.

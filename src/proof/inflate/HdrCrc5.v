(* CRC2 / CRC4 of inflate.c (the gzip header cases): do { hbuf[0..] = hold bytes; check = crc32(check, hbuf, n); }
   while (0), in a minimal context (the temps state and hold, the local hbuf, the check field, the crc table),
   to be framed into a case with semax_frame_PQR.  One lemma per site (the temps differ). *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate.HdrKit5.
Require Import Zlib.proof.inflate.CaseHyps5.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.inflate.MwfLemmas.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Definition crc2_stmt (t1 t2: ident) : statement :=
  (Ssequence (Sassign (Ederef (Ebinop Oadd (Evar _hbuf (tarray tuchar 4)) (Econst_int (Int.repr 0) tint) (tptr tuchar)) tuchar) (Ecast (Etempvar _hold tulong) tuchar)) (Ssequence (Sassign (Ederef (Ebinop Oadd (Evar _hbuf (tarray tuchar 4)) (Econst_int (Int.repr 1) tint) (tptr tuchar)) tuchar) (Ecast (Ebinop Oshr (Etempvar _hold tulong) (Econst_int (Int.repr 8) tint) tulong) tuchar)) (Ssequence (Ssequence (Sset t1 (Efield (Ederef (Etempvar _state (tptr (Tstruct _inflate_state noattr))) (Tstruct _inflate_state noattr)) _check tulong)) (Scall (Some t2) (Evar _crc32 (Tfunction (tulong :: (tptr tuchar) :: tuint :: nil) tulong cc_default)) ((Etempvar t1 tulong) :: (Evar _hbuf (tarray tuchar 4)) :: (Econst_int (Int.repr 2) tint) :: nil))) (Sassign (Efield (Ederef (Etempvar _state (tptr (Tstruct _inflate_state noattr))) (Tstruct _inflate_state noattr)) _check tulong) (Etempvar t2 tulong))))).

Definition crc4_stmt (t1 t2: ident) : statement :=
  (Ssequence (Sassign (Ederef (Ebinop Oadd (Evar _hbuf (tarray tuchar 4)) (Econst_int (Int.repr 0) tint) (tptr tuchar)) tuchar) (Ecast (Etempvar _hold tulong) tuchar)) (Ssequence (Sassign (Ederef (Ebinop Oadd (Evar _hbuf (tarray tuchar 4)) (Econst_int (Int.repr 1) tint) (tptr tuchar)) tuchar) (Ecast (Ebinop Oshr (Etempvar _hold tulong) (Econst_int (Int.repr 8) tint) tulong) tuchar)) (Ssequence (Sassign (Ederef (Ebinop Oadd (Evar _hbuf (tarray tuchar 4)) (Econst_int (Int.repr 2) tint) (tptr tuchar)) tuchar) (Ecast (Ebinop Oshr (Etempvar _hold tulong) (Econst_int (Int.repr 16) tint) tulong) tuchar)) (Ssequence (Sassign (Ederef (Ebinop Oadd (Evar _hbuf (tarray tuchar 4)) (Econst_int (Int.repr 3) tint) (tptr tuchar)) tuchar) (Ecast (Ebinop Oshr (Etempvar _hold tulong) (Econst_int (Int.repr 24) tint) tulong) tuchar)) (Ssequence (Ssequence (Sset t1 (Efield (Ederef (Etempvar _state (tptr (Tstruct _inflate_state noattr))) (Tstruct _inflate_state noattr)) _check tulong)) (Scall (Some t2) (Evar _crc32 (Tfunction (tulong :: (tptr tuchar) :: tuint :: nil) tulong cc_default)) ((Etempvar t1 tulong) :: (Evar _hbuf (tarray tuchar 4)) :: (Econst_int (Int.repr 4) tint) :: nil))) (Sassign (Efield (Ederef (Etempvar _state (tptr (Tstruct _inflate_state noattr))) (Tstruct _inflate_state noattr)) _check tulong) (Etempvar t2 tulong))))))).

Ltac rl := match goal with |- context [data_at Tsh (tarray tuchar 4) ?l _] =>
  let L := fresh "L" in let EL := fresh "EL" in remember l as L eqn:EL end.

Lemma hk_zext_mod: forall x, Int.zero_ext 8 (Int.zero_ext 8 (Int.repr x)) = Int.repr (x mod 256).
Proof.
  intros x. rewrite Int.zero_ext_idem by lia.
  apply Int.same_bits_eq; intros i Hi. rewrite Int.bits_zero_ext by lia. rewrite !Int.testbit_repr by auto.
  change 256 with (2 ^ 8). destruct (zlt i 8).
  - rewrite Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma hk_byte_shr: forall h n, lrange h -> 0 <= n ->
  Vint (Int.zero_ext 8 (Int.zero_ext 8 (Int.repr (Int64.Z_mod_modulus (Z.shiftr (Int64.unsigned (Int64.repr h)) n))))) =
  Vint (Int.repr (Z.shiftr h n mod 256)).
Proof.
  intros h n R Hn. unfold lrange in R. rewrite Int64.unsigned_repr by rep_lia.
  rewrite Int64.Z_mod_modulus_eq. rewrite Z.mod_small.
  - rewrite hk_zext_mod. reflexivity.
  - pose proof (Zshiftr_range h n ltac:(rep_lia) Hn). unfold Int64.modulus, Int64.wordsize, Wordsize_64.wordsize.
    change (two_power_nat 64) with (Int64.max_unsigned + 1). lia.
Qed.

Lemma hk_byte0: forall h, lrange h ->
  Vint (Int.zero_ext 8 (Int.zero_ext 8 (Int.repr (Int64.unsigned (Int64.repr h))))) = Vint (Int.repr (h mod 256)).
Proof. intros h R. unfold lrange in R. rewrite Int64.unsigned_repr by rep_lia. rewrite hk_zext_mod. reflexivity. Qed.

Lemma hk_upd4: forall v0 v1 v2 v3,
  upd_Znth 3 (upd_Znth 2 (upd_Znth 1 (upd_Znth 0 (default_val (tarray tuchar 4)) v0) v1) v2) v3 = [v0; v1; v2; v3].
Proof. intros. reflexivity. Qed.

Lemma hk_upd2: forall v0 v1,
  upd_Znth 1 (upd_Znth 0 (default_val (tarray tuchar 4)) v0) v1 = [v0; v1; Vundef; Vundef].
Proof. intros. reflexivity. Qed.

(* the crc32 spec's buffer is stated in the crc32 unit's compspecs *)
Lemma hk_da_cs: forall sh (v: list val) p,
  @data_at Zlib.units.Inflate.CS sh (tarray tuchar 4) v p = @data_at Zlib.units.Crc32.CS sh (tarray tuchar 4) v p.
Proof.
  intros.
  assert (E: @data_at Zlib.units.Crc32.CS sh (tarray tuchar 4) v = @data_at Zlib.units.Inflate.CS sh (tarray tuchar 4) v).
  { apply (@data_at_change_composite _ _ CCE_crc32); [apply JMeq_refl | reflexivity]. }
  rewrite E. reflexivity.
Qed.

Definition crc_pre (sp vhbuf: val) (gv: globals) (tsh: share) (h c: Z) : environ -> mpred :=
  PROP () LOCAL (temp _state sp; temp _hold (lv h); lvar _hbuf (tarray tuchar 4) vhbuf; gvars gv)
  SEP (field_at Ews t_state (DOT _check) (lv c) sp; crc_table_at tsh gv; data_at_ Tsh (tarray tuchar 4) vhbuf).

Lemma semax_crc4_TIME {Espec: OracleKind} sp vhbuf gv tsh h c:
  readable_share tsh -> lrange h -> lrange c ->
  semax Delta_cases5 (crc_pre sp vhbuf gv tsh h c) (crc4_stmt _t'419 _t'17)
    (normal_ret_assert (crc_pre sp vhbuf gv tsh h (ref_crc32 c (hbytes4 h)))).
Proof.
  intros HT RH RC. unfold crc_pre, crc4_stmt.
  remember 24 as k24 eqn:Hk.
  remember (Int64.repr h) as H64 eqn:EH. abbreviate_semax.
  forward. forward. forward. forward.
  forward.
  subst H64 k24. change (Int64.Z_mod_modulus (Int.unsigned (Int.repr 24))) with 24.
  rewrite hk_upd4, hk_byte0, !hk_byte_shr by (auto; lia).
  change [Vint (Int.repr (h mod 256)); Vint (Int.repr (Z.shiftr h 8 mod 256));
          Vint (Int.repr (Z.shiftr h 16 mod 256)); Vint (Int.repr (Z.shiftr h 24 mod 256))]
    with (bytes_rep (hbytes4 h)).
  assert_PROP (isptr vhbuf) by entailer!.
  forward_call (c, vhbuf, 4, false, Tsh, vhbuf, 0, 4, bytes_rep (hbytes4 h), hbytes4 h, false, Tsh, gv, tsh).
  { rewrite <- hk_da_cs. cancel. }
  { split; [ | apply cbuf_valid_pos; lia].
    unfold cbuf_ok. rewrite isptr_offset_val_zero by auto.
    split; [reflexivity | ]. split; [auto | ]. split; [lia | ]. split; [lia | ]. split; [reflexivity | ].
    split; [apply hk_hbytes4_bytes | ]. rewrite sublist_same by reflexivity. reflexivity. }
  forward.
  entailer!.
Qed.

Ltac crc2_tac :=
  let HT := fresh "HT" in let RH := fresh "RH" in let RC := fresh "RC" in let EH := fresh "EH" in
  let H64 := fresh "H64" in
  intros HT RH RC; unfold crc_pre, crc2_stmt;
  match goal with |- context [temp _hold (Vlong (Int64.repr ?h))] =>
  match goal with |- context [field_at _ _ _ (Vlong (Int64.repr ?c)) ?sp] =>
  match goal with |- context [lvar _hbuf _ ?vhbuf] =>
  match goal with |- context [crc_table_at ?tsh ?gv] =>
  remember (Int64.repr h) as H64 eqn:EH; abbreviate_semax;
  forward; forward; forward;
  subst H64; rewrite hk_upd2, hk_byte0, hk_byte_shr by (auto; lia);
  assert_PROP (isptr vhbuf) by entailer!;
  forward_call (c, vhbuf, 2, false, Tsh, vhbuf, 0, 4,
                [Vint (Int.repr (h mod 256)); Vint (Int.repr (Z.shiftr h 8 mod 256)); Vundef; Vundef],
                hbytes2 h, false, Tsh, gv, tsh);
  [ rewrite <- hk_da_cs; cancel
  | split; [ | apply cbuf_valid_pos; lia];
    unfold cbuf_ok; rewrite isptr_offset_val_zero by auto;
    split; [reflexivity | ]; split; [auto | ]; split; [lia | ]; split; [lia | ]; split; [reflexivity | ];
    split; [apply hk_hbytes2_bytes | reflexivity]
  | forward; entailer! ]
  end end end end.

Lemma semax_crc2_FLAGS {Espec: OracleKind} sp vhbuf gv tsh h c:
  readable_share tsh -> lrange h -> lrange c ->
  semax Delta_cases5 (crc_pre sp vhbuf gv tsh h c) (crc2_stmt _t'425 _t'14)
    (normal_ret_assert (crc_pre sp vhbuf gv tsh h (ref_crc32 c (hbytes2 h)))).
Proof. crc2_tac. Qed.

Lemma semax_crc2_OS {Espec: OracleKind} sp vhbuf gv tsh h c:
  readable_share tsh -> lrange h -> lrange c ->
  semax Delta_cases5 (crc_pre sp vhbuf gv tsh h c) (crc2_stmt _t'412 _t'20)
    (normal_ret_assert (crc_pre sp vhbuf gv tsh h (ref_crc32 c (hbytes2 h)))).
Proof. crc2_tac. Qed.

(* if ((state->flags & 0x0200) && (state->wrap & 4)) CRCn(state->check, hold); (temps ta, tb, tf) *)
Definition crcblock (ta tb tf: ident) (body: statement) : statement :=
  (Ssequence (Ssequence (Sset ta (Efield (Ederef (Etempvar _state (tptr (Tstruct _inflate_state noattr))) (Tstruct _inflate_state noattr)) _flags tint)) (Sifthenelse (Ebinop Oand (Etempvar ta tint) (Econst_int (Int.repr 512) tint) tint) (Ssequence (Sset tb (Efield (Ederef (Etempvar _state (tptr (Tstruct _inflate_state noattr))) (Tstruct _inflate_state noattr)) _wrap tint)) (Sset tf (Ecast (Ebinop Oand (Etempvar tb tint) (Econst_int (Int.repr 4) tint) tint) tbool))) (Sset tf (Econst_int (Int.repr 0) tint)))) (Sifthenelse (Etempvar tf tint) (Sloop body Sbreak) Sskip)).

Ltac rm_loc L := lazymatch L with
  | nil => constr:(@nil localdef)
  | temp _state _ :: ?r => rm_loc r
  | temp _hold _ :: ?r => rm_loc r
  | lvar _hbuf _ _ :: ?r => rm_loc r
  | gvars _ :: ?r => rm_loc r
  | ?a :: ?r => let r' := rm_loc r in constr:(a :: r')
  end.
Ltac rm_sep S := lazymatch S with
  | nil => constr:(@nil mpred)
  | field_at _ _ (DOT _check) _ _ :: ?r => rm_sep r
  | crc_table_at _ _ :: ?r => rm_sep r
  | data_at_ _ (tarray tuchar 4) _ :: ?r => rm_sep r
  | ?a :: ?r => let r' := rm_sep r in constr:(a :: r')
  end.

(* frame the crc lemma LEM (its arguments given) into the current goal *)
Ltac frame_crc LEM :=
  eapply semax_post_flipped';
  [ match goal with |- semax _ (PROPx _ (LOCALx ?L (SEPx ?S))) _ _ =>
      let Q2 := rm_loc L in let R2 := rm_sep S in
      eapply semax_pre; [ | apply (semax_frame_PQR Q2 R2); [ unfold closed_wrt_modvars; auto 50 with closed | exact LEM ] ];
      cbv [app]; entailer!
    end
  | cbv [app]; entailer! ].

Ltac if_absurd := exfalso; first
  [ match goal with H: Int.repr _ <> Int.zero |- _ => apply H; reflexivity end
  | match goal with H: Int.repr _ = Int.zero |- _ =>
      apply (f_equal Int.unsigned) in H; vm_compute in H; discriminate H end
  | match goal with H: Int.repr ?a = Int.repr ?b |- _ =>
      apply (f_equal Int.unsigned) in H; vm_compute in H; discriminate H end
  | discriminate | lia | contradiction ].

Ltac crcblock_tac tf LEM :=
  match goal with W: mwf _ |- _ =>
  pose proof (sw_flags _ (mw_s _ W)) as RF; pose proof (sw_wrap_range _ (mw_s _ W)) as RW end;
  unfold crcblock, crc_if; cbv zeta;
  destruct (negb (Z.land (i_flags (m_s _)) 512 =? 0) && negb (Z.land (i_wrap (m_s _)) 4 =? 0))%bool eqn:Ec;
  [ apply andb_prop in Ec; destruct Ec as [Ec1 Ec2]; apply negb_true_iff in Ec1; apply negb_true_iff in Ec2;
    rewrite !loop_state_hsplit; unfold loop_state_h;
    rewrite mem_rep_h_check, head_part_check, strm_part_check; cbn [upd_s set_m_s m_s set_i_check i_check i_mode i_wrap i_flags i_head];
    abbreviate_semax;
    forward;
    forward_if (temp tf (Vint (Int.repr 1)));
    [ forward; forward; entailer!;
      rewrite hk_tbool by (apply hk_land_small; rep_lia); rewrite Ec2; reflexivity
    | match goal with H: Int.and _ _ = Int.zero |- _ =>
        rewrite (hk_flagbit0 _ _ H) in Ec1 by rep_lia; discriminate end
    | forward_if; [ apply semax_dowhile0; frame_crc LEM | if_absurd ] ]
  | rewrite !loop_state_hsplit; unfold loop_state_h;
    abbreviate_semax;
    forward;
    forward_if (temp tf (Vint (Int.repr 0)));
    [ forward; forward; entailer!;
      match goal with H: Int.and _ _ <> Int.zero |- _ => rewrite (hk_flagbit _ _ H) in Ec end;
      cbn [negb andb] in Ec;
      rewrite hk_tbool by (apply hk_land_small; rep_lia);
      destruct (Z.land (i_wrap (m_s _)) 4 =? 0); [reflexivity | discriminate]
    | forward; entailer!
    | forward_if; [ if_absurd | forward; entailer! ] ] ].

Lemma semax_crcblock_TIME {Espec: OracleKind} (F: frame) (m: mst):
  frame_ok F -> mwf m ->
  semax Delta_cases5 (loop_state F m) (crcblock _t'420 _t'421 _t'18 (crc4_stmt _t'419 _t'17))
    (normal_ret_assert (loop_state F (crc_if m (hbytes4 (m_hold m))))).
Proof.
  intros FOK W. pose proof FOK as (_ & _ & _ & HRT).
  pose proof (sw_check _ (mw_s _ W)) as RC. pose proof (mw_hold _ W) as RH.
  crcblock_tac _t'18 (semax_crc4_TIME (f_sp F) (f_vhbuf F) (f_gv F) (f_tsh F) (m_hold m) (i_check (m_s m)) HRT RH RC).
Qed.

Lemma semax_crcblock_FLAGS {Espec: OracleKind} (F: frame) (m: mst):
  frame_ok F -> mwf m ->
  semax Delta_cases5 (loop_state F m) (crcblock _t'426 _t'427 _t'15 (crc2_stmt _t'425 _t'14))
    (normal_ret_assert (loop_state F (crc_if m (hbytes2 (m_hold m))))).
Proof.
  intros FOK W. pose proof FOK as (_ & _ & _ & HRT).
  pose proof (sw_check _ (mw_s _ W)) as RC. pose proof (mw_hold _ W) as RH.
  crcblock_tac _t'15 (semax_crc2_FLAGS (f_sp F) (f_vhbuf F) (f_gv F) (f_tsh F) (m_hold m) (i_check (m_s m)) HRT RH RC).
Qed.

Lemma semax_crcblock_OS {Espec: OracleKind} (F: frame) (m: mst):
  frame_ok F -> mwf m ->
  semax Delta_cases5 (loop_state F m) (crcblock _t'413 _t'414 _t'21 (crc2_stmt _t'412 _t'20))
    (normal_ret_assert (loop_state F (crc_if m (hbytes2 (m_hold m))))).
Proof.
  intros FOK W. pose proof FOK as (_ & _ & _ & HRT).
  pose proof (sw_check _ (mw_s _ W)) as RC. pose proof (mw_hold _ W) as RH.
  crcblock_tac _t'21 (semax_crc2_OS (f_sp F) (f_vhbuf F) (f_gv F) (f_tsh F) (m_hold m) (i_check (m_s m)) HRT RH RC).
Qed.

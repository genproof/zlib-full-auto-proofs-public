(* RT-H: the do-while of NAME (and COMMENT, below) in a minimal context, for the partial header:
   the gz_header struct holds ANY values in its fields (only name/name_max are read), the name buffer is a
   list val whose first L bytes are the model's (NCLoop5.v's lemmas with hstruct / byte_vals generalized). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.roundtrip.RTHNC6Kit.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* the buffer after one byte of the do-while *)
Definition zst_lb (L max: Z) (lb: list val) (b: Z) : list val :=
  if L <? max then upd_Znth L lb (Vint (Int.repr b)) else lb.

Lemma vrel_upd: forall L (lb: list val) (buf: list Z) x,
  0 <= L < Zlength lb -> Zlength lb = Zlength buf ->
  sublist 0 L lb = byte_vals (sublist 0 L buf) ->
  sublist 0 (L + 1) (upd_Znth L lb (Vint (Int.repr x))) = byte_vals (sublist 0 (L + 1) (upd_Znth L buf x)).
Proof.
  intros L lb buf x H E S. unfold byte_vals in *.
  rewrite !(sublist_split 0 L (L + 1)) by (rewrite ?upd_Znth_Zlength; lia).
  rewrite !sublist_upd_Znth_l by lia. rewrite S.
  rewrite !sublist_len_1 by (rewrite ?upd_Znth_Zlength; lia). rewrite !upd_Znth_same by lia.
  rewrite map_app. rewrite (sublist_upd_Znth_l buf L 0 L) by lia. reflexivity.
Qed.

Lemma vrel_zst: forall L max (lb: list val) (buf: list Z) x,
  0 <= L <= max -> Zlength lb = max -> Zlength buf = max ->
  sublist 0 L lb = byte_vals (sublist 0 L buf) ->
  Zlength (zst_lb L max lb x) = max /\ Zlength (zst_buf true L max buf x) = max /\
  sublist 0 (zst_L true L max) (zst_lb L max lb x) = byte_vals (sublist 0 (zst_L true L max) (zst_buf true L max buf x)).
Proof.
  intros L max lb buf x H E1 E2 S. unfold zst_lb, zst_L, zst_buf. cbn [andb].
  destruct (Z.ltb_spec L max).
  - split; [rewrite upd_Znth_Zlength; lia | ]. split; [rewrite upd_Znth_Zlength; lia | ].
    apply vrel_upd; auto; lia.
  - auto.
Qed.

Local Transparent denote_tc_test_eq.
Lemma ncl_test_eq6: forall P nb max (lb: list val),
  nb <> nullval -> 0 <= max ->
  P |-- data_at Ews (tarray tuchar max) lb nb * (if zeq max 0 then malloc_token Ews (tarray tuchar 0) nb else emp) * TT ->
  P |-- denote_tc_test_eq nb (Vlong (Int64.repr 0)).
Proof.
  intros P nb max lb NN Hm H. eapply derives_trans; [exact H | ].
  destruct (zeq max 0) as [E | E].
  - subst max.
    assert_PROP (isptr nb) as Hq by (saturate_local; entailer!).
    destruct nb; try contradiction.
    unfold denote_tc_test_eq. cbv [Archi.ptr64].
    apply andp_right; [apply prop_right; reflexivity | ].
    apply sepcon_weak_valid_pointer1. apply sepcon_weak_valid_pointer2.
    eapply derives_trans; [apply malloc_token_valid_pointer; simpl; lia | ].
    apply valid_pointer_weak.
  - assert_PROP (isptr nb) as Hq by entailer!.
    destruct nb; try contradiction.
    unfold denote_tc_test_eq. cbv [Archi.ptr64].
    apply andp_right; [apply prop_right; reflexivity | ].
    apply sepcon_weak_valid_pointer1. apply sepcon_weak_valid_pointer1.
    eapply derives_trans; [ | apply valid_pointer_weak]. apply data_at_valid_ptr.
    + apply readable_nonidentity. auto.
    + simpl. rep_lia.
Qed.
Local Opaque denote_tc_test_eq.

(* the loop when nothing is stored (the header's name field is NULL) *)
Lemma semax_name_loop_nowr6 {Espec: OracleKind} (sp headp: val) (hsh: share)
    (vt vtm vxf vos vx vxl vxm vnm vc vcm vhc vd: val)
    (max: Z) (buf: list Z) (L0 have: Z) (bytes: list Z) (ish: share) (ip: val) (q inn: Z) (icont: list val)
    (c b ln: Z) (bf: list Z):
  readable_share hsh -> readable_share ish -> isptr ip ->
  0 <= q -> q + have <= inn -> Zlength icont = inn -> inn <= Ptrofs.max_unsigned ->
  sublist q (q + have) icont = byte_vals bytes -> Zlength bytes = have -> bytes_ok bytes ->
  0 < have <= Int.max_unsigned -> urange L0 ->
  zstr_f (Z.to_nat have) bytes have L0 max false buf 0 = (c, b, ln, bf) ->
  semax Delta_cases5
    (PROP () LOCAL (temp _state sp; temp _next (offset_val q ip); temp _have (zv have); temp _copy (zv 0))
     SEP (field_at Ews t_state (DOT _length) (zv L0) sp;
          field_at Ews t_state (DOT _head) headp sp;
          data_at hsh t_head (vt, (vtm, (vxf, (vos, (vx, (vxl, (vxm, (nullval, (vnm, (vc, (vcm, (vhc, vd))))))))))))
            headp;
          data_at ish (tarray tuchar inn) icont ip))
    name_loop
    (normal_ret_assert
     (PROP () LOCAL (temp _state sp; temp _next (offset_val q ip); temp _have (zv have); temp _copy (zv c);
                     temp _len (zv b))
      SEP (field_at Ews t_state (DOT _length) (zv L0) sp;
           field_at Ews t_state (DOT _head) headp sp;
           data_at hsh t_head (vt, (vtm, (vxf, (vos, (vx, (vxl, (vxm, (nullval, (vnm, (vc, (vcm, (vhc, vd))))))))))))
             headp;
           data_at ish (tarray tuchar inn) icont ip))).
Proof.
  intros RH RI PI Q0 QH LI LM SB LB BB HV RL ZS.
  assert_PROP (field_compatible (tarray tuchar inn) [] ip) as FC by entailer!.
  rewrite (in_split ish inn icont ip q) by (auto; lia).
  unfold name_loop. abbreviate_semax.
  forward_loop
    (@exp (environ -> mpred) _ Z (fun j: Z =>
     PROP (0 <= j < have; zstr_f (Z.to_nat (have - j)) bytes have L0 max false buf j = (c, b, ln, bf))
     LOCAL (temp _state sp; temp _next (offset_val q ip); temp _have (zv have); temp _copy (zv j))
     SEP (field_at Ews t_state (DOT _length) (zv L0) sp;
          field_at Ews t_state (DOT _head) headp sp;
          data_at hsh t_head (vt, (vtm, (vxf, (vos, (vx, (vxl, (vxm, (nullval, (vnm, (vc, (vcm, (vhc, vd))))))))))))
            headp;
          data_at ish (tarray tuchar q) (sublist 0 q icont) ip;
          data_at ish (tarray tuchar (inn - q)) (sublist q inn icont) (offset_val q ip))))
  continue:
    (@exp (environ -> mpred) _ Z (fun j: Z =>
     PROP (0 <= j < have; zstr_f (Z.to_nat (have - j)) bytes have L0 max false buf j = (c, b, ln, bf))
     LOCAL (temp _state sp; temp _next (offset_val q ip); temp _have (zv have); temp _copy (zv (j + 1));
            temp _len (zv (Znth j bytes)))
     SEP (field_at Ews t_state (DOT _length) (zv L0) sp;
          field_at Ews t_state (DOT _head) headp sp;
          data_at hsh t_head (vt, (vtm, (vxf, (vos, (vx, (vxl, (vxm, (nullval, (vnm, (vc, (vcm, (vhc, vd))))))))))))
            headp;
          data_at ish (tarray tuchar q) (sublist 0 q icont) ip;
          data_at ish (tarray tuchar (inn - q)) (sublist q inn icont) (offset_val q ip))))
  break:
    (PROP () LOCAL (temp _state sp; temp _next (offset_val q ip); temp _have (zv have); temp _copy (zv c);
                    temp _len (zv b))
     SEP (field_at Ews t_state (DOT _length) (zv L0) sp;
          field_at Ews t_state (DOT _head) headp sp;
          data_at hsh t_head (vt, (vtm, (vxf, (vos, (vx, (vxl, (vxm, (nullval, (vnm, (vc, (vcm, (vhc, vd))))))))))))
            headp;
          data_at ish (tarray tuchar q) (sublist 0 q icont) ip;
          data_at ish (tarray tuchar (inn - q)) (sublist q inn icont) (offset_val q ip))).
  { Exists 0. rewrite Z.sub_0_r. entailer!. }
  { Intros j.
    forward. forward.
    pose proof (ncl_byte_j q have inn icont bytes j Q0 QH LI SB LB H) as BJ.
    assert (BYJ: 0 <= Znth j bytes <= Byte.max_unsigned).
    { apply (Forall_Znth bytes (fun b => 0 <= b <= Byte.max_unsigned)); [exact BB | rewrite LB; lia]. }
    assert (BJd: forall d, @Znth val d j (sublist q inn icont) = Vint (Int.repr (Znth j bytes))).
    { intros d. rewrite <- BJ. unfold Znth. destruct (Z_lt_dec j 0); [lia | ]. apply nth_indep.
      rewrite <- ZtoNat_Zlength. rewrite Zlength_sublist by lia. lia. }
    forward.
    { rewrite BJd. entailer!; lia. }
    rewrite BJd.
    forward.
    forward.
    fif_temp _t'34 (Vint Int.zero).
    + forward. forward. forward. entailer!.
    + assert_PROP (isptr headp) by entailer!.
      match goal with X: headp = nullval |- _ => rewrite X in *; contradiction end.
    + fif_temp _t'35 (Vint Int.zero).
      * contra_tac.
      * forward. entailer!.
      * forward_if.
        { contra_tac. }
        { forward. Exists j. entailer!. } }
  Intros j.
  rewrite (zstr_f_step bytes have L0 max false buf j) in H0 by lia.
  unfold zst_L, zst_buf in H0. cbn [andb] in H0. cbv zeta in H0.
  assert (BYJ: 0 <= Znth j bytes <= Byte.max_unsigned).
  { apply (Forall_Znth bytes (fun b => 0 <= b <= Byte.max_unsigned)); [exact BB | rewrite LB; lia]. }
  fif_temp _t'31 (Vint (if andb (negb (Znth j bytes =? 0)) (j + 1 <? have) then Int.one else Int.zero)).
  { forward. entailer!.
    match goal with X: Znth j bytes <> 0 |- _ => rewrite (proj2 (Z.eqb_neq _ _) X) end.
    cbn [negb andb]. destruct (Z.ltb_spec (j + 1) (Zlength bytes)), (zlt (j + 1) (Zlength bytes));
      try reflexivity; lia. }
  { forward. entailer!.
    match goal with X: Int.repr (Znth j bytes) = Int.zero |- _ =>
      apply (f_equal Int.unsigned) in X; rewrite Int.unsigned_repr in X by rep_lia; rewrite X end.
    reflexivity. }
  forward_if.
  { destruct ((negb (Znth j bytes =? 0) && (j + 1 <? have))%bool) eqn:EC;
      [ | exfalso; apply H1; reflexivity].
    forward. Exists (j + 1). apply andb_prop in EC. destruct EC as [_ EC]. apply Z.ltb_lt in EC.
    entailer!. }
  { destruct ((negb (Znth j bytes =? 0) && (j + 1 <? have))%bool) eqn:EC; [contra_tac | ].
    forward. inversion H0; subst. entailer!. }
  unfold abbreviate in POSTCONDITION; subst POSTCONDITION. unfold normal_ret_assert; cbn [RA_normal]. entailer!.
  Unshelve. all: exact 0.
Qed.

(* the loop storing into the name buffer *)
Lemma semax_name_loop_wr6 {Espec: OracleKind} (sp headp: val) (hsh: share)
    (vt vtm vxf vos vx vxl vxm nb vc vcm vhc vd: val)
    (max: Z) (buf0: list Z) (lb0: list val) (L0 have: Z) (bytes: list Z) (ish: share) (ip: val) (q inn: Z)
    (icont: list val) (c b ln: Z) (bf: list Z):
  readable_share hsh -> readable_share ish -> isptr ip ->
  0 <= q -> q + have <= inn -> Zlength icont = inn -> inn <= Ptrofs.max_unsigned ->
  sublist q (q + have) icont = byte_vals bytes -> Zlength bytes = have -> bytes_ok bytes ->
  0 < have <= Int.max_unsigned -> 0 <= L0 <= max -> max <= 65536 ->
  Zlength buf0 = max -> Zlength lb0 = max -> sublist 0 L0 lb0 = byte_vals (sublist 0 L0 buf0) ->
  nb <> nullval ->
  zstr_f (Z.to_nat have) bytes have L0 max true buf0 0 = (c, b, ln, bf) ->
  semax Delta_cases5
    (PROP () LOCAL (temp _state sp; temp _next (offset_val q ip); temp _have (zv have); temp _copy (zv 0))
     SEP (field_at Ews t_state (DOT _length) (zv L0) sp;
          field_at Ews t_state (DOT _head) headp sp;
          data_at hsh t_head (vt, (vtm, (vxf, (vos, (vx, (vxl, (vxm, (nb, (zv max, (vc, (vcm, (vhc, vd))))))))))))
            headp;
          data_at Ews (tarray tuchar max) lb0 nb;
          (if zeq max 0 then malloc_token Ews (tarray tuchar 0) nb else emp);
          data_at ish (tarray tuchar inn) icont ip))
    name_loop
    (normal_ret_assert
     (@exp (environ -> mpred) _ (list val) (fun lb: list val =>
      PROP (Zlength lb = max; sublist 0 ln lb = byte_vals (sublist 0 ln bf))
      LOCAL (temp _state sp; temp _next (offset_val q ip); temp _have (zv have); temp _copy (zv c);
             temp _len (zv b))
      SEP (field_at Ews t_state (DOT _length) (zv ln) sp;
           field_at Ews t_state (DOT _head) headp sp;
           data_at hsh t_head (vt, (vtm, (vxf, (vos, (vx, (vxl, (vxm, (nb, (zv max, (vc, (vcm, (vhc, vd))))))))))))
             headp;
           data_at Ews (tarray tuchar max) lb nb;
           (if zeq max 0 then malloc_token Ews (tarray tuchar 0) nb else emp);
           data_at ish (tarray tuchar inn) icont ip)))).
Proof.
  intros RH RI PI Q0 QH LI LM SB LB BB HV RL MX LB0 LL0 S0 NN ZS.
  assert_PROP (field_compatible (tarray tuchar inn) [] ip) as FC by entailer!.
  assert_PROP (isptr nb) as PN.
  { destruct (zeq max 0); [ | entailer!].
    sep_apply (malloc_token_local_facts Ews (tarray tuchar 0) nb). entailer!.
    }
  rewrite (in_split ish inn icont ip q) by (auto; lia).
  unfold name_loop. abbreviate_semax.
  forward_loop
    (@exp (environ -> mpred) _ Z (fun j: Z => @exp (environ -> mpred) _ Z (fun L: Z =>
     @exp (environ -> mpred) _ (list Z) (fun buf: list Z => @exp (environ -> mpred) _ (list val) (fun lb: list val =>
     PROP (0 <= j < have; L0 <= L <= max; Zlength buf = max; Zlength lb = max;
           sublist 0 L lb = byte_vals (sublist 0 L buf);
           zstr_f (Z.to_nat (have - j)) bytes have L max true buf j = (c, b, ln, bf))
     LOCAL (temp _state sp; temp _next (offset_val q ip); temp _have (zv have); temp _copy (zv j))
     SEP (field_at Ews t_state (DOT _length) (zv L) sp;
          field_at Ews t_state (DOT _head) headp sp;
          data_at hsh t_head (vt, (vtm, (vxf, (vos, (vx, (vxl, (vxm, (nb, (zv max, (vc, (vcm, (vhc, vd))))))))))))
            headp;
          data_at Ews (tarray tuchar max) lb nb;
          (if zeq max 0 then malloc_token Ews (tarray tuchar 0) nb else emp);
          data_at ish (tarray tuchar q) (sublist 0 q icont) ip;
          data_at ish (tarray tuchar (inn - q)) (sublist q inn icont) (offset_val q ip)))))))
  continue:
    (@exp (environ -> mpred) _ Z (fun j: Z => @exp (environ -> mpred) _ Z (fun L: Z =>
     @exp (environ -> mpred) _ (list Z) (fun buf: list Z => @exp (environ -> mpred) _ (list val) (fun lb: list val =>
     PROP (0 <= j < have; L0 <= L <= max; Zlength buf = max; Zlength lb = max;
           sublist 0 L lb = byte_vals (sublist 0 L buf);
           zstr_f (Z.to_nat (have - j)) bytes have L max true buf j = (c, b, ln, bf))
     LOCAL (temp _state sp; temp _next (offset_val q ip); temp _have (zv have); temp _copy (zv (j + 1));
            temp _len (zv (Znth j bytes)))
     SEP (field_at Ews t_state (DOT _length) (zv (zst_L true L max)) sp;
          field_at Ews t_state (DOT _head) headp sp;
          data_at hsh t_head (vt, (vtm, (vxf, (vos, (vx, (vxl, (vxm, (nb, (zv max, (vc, (vcm, (vhc, vd))))))))))))
            headp;
          data_at Ews (tarray tuchar max) (zst_lb L max lb (Znth j bytes)) nb;
          (if zeq max 0 then malloc_token Ews (tarray tuchar 0) nb else emp);
          data_at ish (tarray tuchar q) (sublist 0 q icont) ip;
          data_at ish (tarray tuchar (inn - q)) (sublist q inn icont) (offset_val q ip)))))))
  break:
    (@exp (environ -> mpred) _ (list val) (fun lb: list val =>
     PROP (Zlength lb = max; sublist 0 ln lb = byte_vals (sublist 0 ln bf))
     LOCAL (temp _state sp; temp _next (offset_val q ip); temp _have (zv have); temp _copy (zv c);
                    temp _len (zv b))
     SEP (field_at Ews t_state (DOT _length) (zv ln) sp;
          field_at Ews t_state (DOT _head) headp sp;
          data_at hsh t_head (vt, (vtm, (vxf, (vos, (vx, (vxl, (vxm, (nb, (zv max, (vc, (vcm, (vhc, vd))))))))))))
            headp;
          data_at Ews (tarray tuchar max) lb nb;
          (if zeq max 0 then malloc_token Ews (tarray tuchar 0) nb else emp);
          data_at ish (tarray tuchar q) (sublist 0 q icont) ip;
          data_at ish (tarray tuchar (inn - q)) (sublist q inn icont) (offset_val q ip)))).
  { Exists 0 L0 buf0 lb0. rewrite Z.sub_0_r. entailer!. }
  { Intros j L buf lb. subst max.
    forward. forward.
    pose proof (ncl_byte_j q have inn icont bytes j Q0 QH LI SB LB H) as BJ.
    assert (BYJ: 0 <= Znth j bytes <= Byte.max_unsigned).
    { apply (Forall_Znth bytes (fun b => 0 <= b <= Byte.max_unsigned)); [exact BB | rewrite LB; lia]. }
    assert (BJd: forall d, @Znth val d j (sublist q inn icont) = Vint (Int.repr (Znth j bytes))).
    { intros d. rewrite <- BJ. unfold Znth. destruct (Z_lt_dec j 0); [lia | ]. apply nth_indep.
      rewrite <- ZtoNat_Zlength. rewrite Zlength_sublist by lia. lia. }
    forward.
    { rewrite BJd. entailer!; lia. }
    rewrite BJd.
    forward.
    forward.
    fif_temp _t'34 (Vint Int.one).
    { forward. forward.
      forward.
      { entailer!. eapply ncl_test_eq6; [exact NN | | cancel]. lia. }
      entailer!. destruct nb; try contradiction. reflexivity. }
    { assert_PROP (isptr headp) by entailer!.
      match goal with X: headp = nullval |- _ => rewrite X in *; contradiction end. }
    assert (LR: 0 <= L <= Int.max_unsigned) by rep_lia.
    fif_temp _t'35 (Vint (if L <? (Zlength buf0) then Int.one else Int.zero)).
    { forward. forward. forward. forward. entailer!.
      destruct (Z.ltb_spec L (Zlength buf0)), (zlt L (Zlength buf0)); try reflexivity; lia. }
    { contra_tac. }
    forward_if.
    { (* store the byte *)
      assert (LT: L < (Zlength buf0)) by (destruct (Z.ltb_spec L (Zlength buf0)); [lia | contra_tac]).
      forward. forward. forward. forward. forward.
      Exists j L buf lb.
      unfold zst_L, zst_lb. cbn [andb]. rewrite (proj2 (Z.ltb_lt _ _) LT).
      rewrite ncl_zext_byte by lia.
      entailer!. apply derives_refl. }
    { assert (LT: (Zlength buf0) <= L) by (destruct (Z.ltb_spec L (Zlength buf0)); [contra_tac | lia]).
      forward.
      Exists j L buf lb.
      unfold zst_L, zst_lb. cbn [andb]. rewrite (proj2 (Z.ltb_ge _ _) LT).
      entailer!. } }
  Intros j L buf lb.
  rewrite (zstr_f_step bytes have L max true buf j) in H4 by lia. cbv zeta in H4.
  assert (BYJ: 0 <= Znth j bytes <= Byte.max_unsigned).
  { apply (Forall_Znth bytes (fun b => 0 <= b <= Byte.max_unsigned)); [exact BB | rewrite LB; lia]. }
  fif_temp _t'31 (Vint (if andb (negb (Znth j bytes =? 0)) (j + 1 <? have) then Int.one else Int.zero)).
  { forward. entailer!.
    match goal with X: Znth j bytes <> 0 |- _ => rewrite (proj2 (Z.eqb_neq _ _) X) end.
    cbn [negb andb]. destruct (Z.ltb_spec (j + 1) (Zlength bytes)), (zlt (j + 1) (Zlength bytes));
      try reflexivity; lia. }
  { forward. entailer!.
    match goal with X: Int.repr (Znth j bytes) = Int.zero |- _ =>
      apply (f_equal Int.unsigned) in X; rewrite Int.unsigned_repr in X by rep_lia; rewrite X end.
    reflexivity. }
  assert (ZL: L0 <= zst_L true L max <= max) by (unfold zst_L; cbn [andb]; destruct (Z.ltb_spec L max); lia).
  destruct (vrel_zst L max lb buf (Znth j bytes) ltac:(lia) H2 H1 H3) as (V1 & V2 & V3).
  forward_if.
  { destruct ((negb (Znth j bytes =? 0) && (j + 1 <? have))%bool) eqn:EC;
      [ | exfalso; match goal with X: _ <> Int.zero |- _ => apply X; reflexivity end].
    forward. Exists (j + 1) (zst_L true L max) (zst_buf true L max buf (Znth j bytes)) (zst_lb L max lb (Znth j bytes)).
    apply andb_prop in EC. destruct EC as [_ EC]. apply Z.ltb_lt in EC.
    entailer!. }
  { destruct ((negb (Znth j bytes =? 0) && (j + 1 <? have))%bool) eqn:EC; [contra_tac | ].
    forward. cbv zeta in H4. inversion H4; subst. Exists (zst_lb L (Zlength buf0) lb (Znth j bytes)). entailer!. }
  unfold abbreviate in POSTCONDITION; subst POSTCONDITION. unfold normal_ret_assert; cbn [RA_normal].
  Intros lb. Exists lb. entailer!.
  Unshelve. all: exact 0.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* COMMENT: the same loops over head->comment *)

(* the loop when nothing is stored (the header's comment field is NULL) *)
Lemma semax_comm_loop_nowr6 {Espec: OracleKind} (sp headp: val) (hsh: share)
    (vt vtm vxf vos vx vxl vxm vn vnm vcm vhc vd: val)
    (max: Z) (buf: list Z) (L0 have: Z) (bytes: list Z) (ish: share) (ip: val) (q inn: Z) (icont: list val)
    (c b ln: Z) (bf: list Z):
  readable_share hsh -> readable_share ish -> isptr ip ->
  0 <= q -> q + have <= inn -> Zlength icont = inn -> inn <= Ptrofs.max_unsigned ->
  sublist q (q + have) icont = byte_vals bytes -> Zlength bytes = have -> bytes_ok bytes ->
  0 < have <= Int.max_unsigned -> urange L0 ->
  zstr_f (Z.to_nat have) bytes have L0 max false buf 0 = (c, b, ln, bf) ->
  semax Delta_cases5
    (PROP () LOCAL (temp _state sp; temp _next (offset_val q ip); temp _have (zv have); temp _copy (zv 0))
     SEP (field_at Ews t_state (DOT _length) (zv L0) sp;
          field_at Ews t_state (DOT _head) headp sp;
          data_at hsh t_head (vt, (vtm, (vxf, (vos, (vx, (vxl, (vxm, (vn, (vnm, (nullval, (vcm, (vhc, vd))))))))))))
            headp;
          data_at ish (tarray tuchar inn) icont ip))
    comm_loop
    (normal_ret_assert
     (PROP () LOCAL (temp _state sp; temp _next (offset_val q ip); temp _have (zv have); temp _copy (zv c);
                     temp _len (zv b))
      SEP (field_at Ews t_state (DOT _length) (zv L0) sp;
           field_at Ews t_state (DOT _head) headp sp;
           data_at hsh t_head (vt, (vtm, (vxf, (vos, (vx, (vxl, (vxm, (vn, (vnm, (nullval, (vcm, (vhc, vd))))))))))))
             headp;
           data_at ish (tarray tuchar inn) icont ip))).
Proof.
  intros RH RI PI Q0 QH LI LM SB LB BB HV RL ZS.
  assert_PROP (field_compatible (tarray tuchar inn) [] ip) as FC by entailer!.
  rewrite (in_split ish inn icont ip q) by (auto; lia).
  unfold comm_loop. abbreviate_semax.
  forward_loop
    (@exp (environ -> mpred) _ Z (fun j: Z =>
     PROP (0 <= j < have; zstr_f (Z.to_nat (have - j)) bytes have L0 max false buf j = (c, b, ln, bf))
     LOCAL (temp _state sp; temp _next (offset_val q ip); temp _have (zv have); temp _copy (zv j))
     SEP (field_at Ews t_state (DOT _length) (zv L0) sp;
          field_at Ews t_state (DOT _head) headp sp;
          data_at hsh t_head (vt, (vtm, (vxf, (vos, (vx, (vxl, (vxm, (vn, (vnm, (nullval, (vcm, (vhc, vd))))))))))))
            headp;
          data_at ish (tarray tuchar q) (sublist 0 q icont) ip;
          data_at ish (tarray tuchar (inn - q)) (sublist q inn icont) (offset_val q ip))))
  continue:
    (@exp (environ -> mpred) _ Z (fun j: Z =>
     PROP (0 <= j < have; zstr_f (Z.to_nat (have - j)) bytes have L0 max false buf j = (c, b, ln, bf))
     LOCAL (temp _state sp; temp _next (offset_val q ip); temp _have (zv have); temp _copy (zv (j + 1));
            temp _len (zv (Znth j bytes)))
     SEP (field_at Ews t_state (DOT _length) (zv L0) sp;
          field_at Ews t_state (DOT _head) headp sp;
          data_at hsh t_head (vt, (vtm, (vxf, (vos, (vx, (vxl, (vxm, (vn, (vnm, (nullval, (vcm, (vhc, vd))))))))))))
            headp;
          data_at ish (tarray tuchar q) (sublist 0 q icont) ip;
          data_at ish (tarray tuchar (inn - q)) (sublist q inn icont) (offset_val q ip))))
  break:
    (PROP () LOCAL (temp _state sp; temp _next (offset_val q ip); temp _have (zv have); temp _copy (zv c);
                    temp _len (zv b))
     SEP (field_at Ews t_state (DOT _length) (zv L0) sp;
          field_at Ews t_state (DOT _head) headp sp;
          data_at hsh t_head (vt, (vtm, (vxf, (vos, (vx, (vxl, (vxm, (vn, (vnm, (nullval, (vcm, (vhc, vd))))))))))))
            headp;
          data_at ish (tarray tuchar q) (sublist 0 q icont) ip;
          data_at ish (tarray tuchar (inn - q)) (sublist q inn icont) (offset_val q ip))).
  { Exists 0. rewrite Z.sub_0_r. entailer!. }
  { Intros j.
    forward. forward.
    pose proof (ncl_byte_j q have inn icont bytes j Q0 QH LI SB LB H) as BJ.
    assert (BYJ: 0 <= Znth j bytes <= Byte.max_unsigned).
    { apply (Forall_Znth bytes (fun b => 0 <= b <= Byte.max_unsigned)); [exact BB | rewrite LB; lia]. }
    assert (BJd: forall d, @Znth val d j (sublist q inn icont) = Vint (Int.repr (Znth j bytes))).
    { intros d. rewrite <- BJ. unfold Znth. destruct (Z_lt_dec j 0); [lia | ]. apply nth_indep.
      rewrite <- ZtoNat_Zlength. rewrite Zlength_sublist by lia. lia. }
    forward.
    { rewrite BJd. entailer!; lia. }
    rewrite BJd.
    forward.
    forward.
    fif_temp _t'41 (Vint Int.zero).
    + forward. forward. forward. entailer!.
    + assert_PROP (isptr headp) by entailer!.
      match goal with X: headp = nullval |- _ => rewrite X in *; contradiction end.
    + fif_temp _t'42 (Vint Int.zero).
      * contra_tac.
      * forward. entailer!.
      * forward_if.
        { contra_tac. }
        { forward. Exists j. entailer!. } }
  Intros j.
  rewrite (zstr_f_step bytes have L0 max false buf j) in H0 by lia.
  unfold zst_L, zst_buf in H0. cbn [andb] in H0. cbv zeta in H0.
  assert (BYJ: 0 <= Znth j bytes <= Byte.max_unsigned).
  { apply (Forall_Znth bytes (fun b => 0 <= b <= Byte.max_unsigned)); [exact BB | rewrite LB; lia]. }
  fif_temp _t'38 (Vint (if andb (negb (Znth j bytes =? 0)) (j + 1 <? have) then Int.one else Int.zero)).
  { forward. entailer!.
    match goal with X: Znth j bytes <> 0 |- _ => rewrite (proj2 (Z.eqb_neq _ _) X) end.
    cbn [negb andb]. destruct (Z.ltb_spec (j + 1) (Zlength bytes)), (zlt (j + 1) (Zlength bytes));
      try reflexivity; lia. }
  { forward. entailer!.
    match goal with X: Int.repr (Znth j bytes) = Int.zero |- _ =>
      apply (f_equal Int.unsigned) in X; rewrite Int.unsigned_repr in X by rep_lia; rewrite X end.
    reflexivity. }
  forward_if.
  { destruct ((negb (Znth j bytes =? 0) && (j + 1 <? have))%bool) eqn:EC;
      [ | exfalso; apply H1; reflexivity].
    forward. Exists (j + 1). apply andb_prop in EC. destruct EC as [_ EC]. apply Z.ltb_lt in EC.
    entailer!. }
  { destruct ((negb (Znth j bytes =? 0) && (j + 1 <? have))%bool) eqn:EC; [contra_tac | ].
    forward. inversion H0; subst. entailer!. }
  unfold abbreviate in POSTCONDITION; subst POSTCONDITION. unfold normal_ret_assert; cbn [RA_normal]. entailer!.
  Unshelve. all: exact 0.
Qed.

(* the loop storing into the comment buffer *)
Lemma semax_comm_loop_wr6 {Espec: OracleKind} (sp headp: val) (hsh: share)
    (vt vtm vxf vos vx vxl vxm vn vnm nb vhc vd: val)
    (max: Z) (buf0: list Z) (lb0: list val) (L0 have: Z) (bytes: list Z) (ish: share) (ip: val) (q inn: Z)
    (icont: list val) (c b ln: Z) (bf: list Z):
  readable_share hsh -> readable_share ish -> isptr ip ->
  0 <= q -> q + have <= inn -> Zlength icont = inn -> inn <= Ptrofs.max_unsigned ->
  sublist q (q + have) icont = byte_vals bytes -> Zlength bytes = have -> bytes_ok bytes ->
  0 < have <= Int.max_unsigned -> 0 <= L0 <= max -> max <= 65536 ->
  Zlength buf0 = max -> Zlength lb0 = max -> sublist 0 L0 lb0 = byte_vals (sublist 0 L0 buf0) ->
  nb <> nullval ->
  zstr_f (Z.to_nat have) bytes have L0 max true buf0 0 = (c, b, ln, bf) ->
  semax Delta_cases5
    (PROP () LOCAL (temp _state sp; temp _next (offset_val q ip); temp _have (zv have); temp _copy (zv 0))
     SEP (field_at Ews t_state (DOT _length) (zv L0) sp;
          field_at Ews t_state (DOT _head) headp sp;
          data_at hsh t_head (vt, (vtm, (vxf, (vos, (vx, (vxl, (vxm, (vn, (vnm, (nb, (zv max, (vhc, vd))))))))))))
            headp;
          data_at Ews (tarray tuchar max) lb0 nb;
          (if zeq max 0 then malloc_token Ews (tarray tuchar 0) nb else emp);
          data_at ish (tarray tuchar inn) icont ip))
    comm_loop
    (normal_ret_assert
     (@exp (environ -> mpred) _ (list val) (fun lb: list val =>
      PROP (Zlength lb = max; sublist 0 ln lb = byte_vals (sublist 0 ln bf))
      LOCAL (temp _state sp; temp _next (offset_val q ip); temp _have (zv have); temp _copy (zv c);
             temp _len (zv b))
      SEP (field_at Ews t_state (DOT _length) (zv ln) sp;
           field_at Ews t_state (DOT _head) headp sp;
           data_at hsh t_head (vt, (vtm, (vxf, (vos, (vx, (vxl, (vxm, (vn, (vnm, (nb, (zv max, (vhc, vd))))))))))))
             headp;
           data_at Ews (tarray tuchar max) lb nb;
           (if zeq max 0 then malloc_token Ews (tarray tuchar 0) nb else emp);
           data_at ish (tarray tuchar inn) icont ip)))).
Proof.
  intros RH RI PI Q0 QH LI LM SB LB BB HV RL MX LB0 LL0 S0 NN ZS.
  assert_PROP (field_compatible (tarray tuchar inn) [] ip) as FC by entailer!.
  assert_PROP (isptr nb) as PN.
  { destruct (zeq max 0); [ | entailer!].
    sep_apply (malloc_token_local_facts Ews (tarray tuchar 0) nb). entailer!.
    }
  rewrite (in_split ish inn icont ip q) by (auto; lia).
  unfold comm_loop. abbreviate_semax.
  forward_loop
    (@exp (environ -> mpred) _ Z (fun j: Z => @exp (environ -> mpred) _ Z (fun L: Z =>
     @exp (environ -> mpred) _ (list Z) (fun buf: list Z => @exp (environ -> mpred) _ (list val) (fun lb: list val =>
     PROP (0 <= j < have; L0 <= L <= max; Zlength buf = max; Zlength lb = max;
           sublist 0 L lb = byte_vals (sublist 0 L buf);
           zstr_f (Z.to_nat (have - j)) bytes have L max true buf j = (c, b, ln, bf))
     LOCAL (temp _state sp; temp _next (offset_val q ip); temp _have (zv have); temp _copy (zv j))
     SEP (field_at Ews t_state (DOT _length) (zv L) sp;
          field_at Ews t_state (DOT _head) headp sp;
          data_at hsh t_head (vt, (vtm, (vxf, (vos, (vx, (vxl, (vxm, (vn, (vnm, (nb, (zv max, (vhc, vd))))))))))))
            headp;
          data_at Ews (tarray tuchar max) lb nb;
          (if zeq max 0 then malloc_token Ews (tarray tuchar 0) nb else emp);
          data_at ish (tarray tuchar q) (sublist 0 q icont) ip;
          data_at ish (tarray tuchar (inn - q)) (sublist q inn icont) (offset_val q ip)))))))
  continue:
    (@exp (environ -> mpred) _ Z (fun j: Z => @exp (environ -> mpred) _ Z (fun L: Z =>
     @exp (environ -> mpred) _ (list Z) (fun buf: list Z => @exp (environ -> mpred) _ (list val) (fun lb: list val =>
     PROP (0 <= j < have; L0 <= L <= max; Zlength buf = max; Zlength lb = max;
           sublist 0 L lb = byte_vals (sublist 0 L buf);
           zstr_f (Z.to_nat (have - j)) bytes have L max true buf j = (c, b, ln, bf))
     LOCAL (temp _state sp; temp _next (offset_val q ip); temp _have (zv have); temp _copy (zv (j + 1));
            temp _len (zv (Znth j bytes)))
     SEP (field_at Ews t_state (DOT _length) (zv (zst_L true L max)) sp;
          field_at Ews t_state (DOT _head) headp sp;
          data_at hsh t_head (vt, (vtm, (vxf, (vos, (vx, (vxl, (vxm, (vn, (vnm, (nb, (zv max, (vhc, vd))))))))))))
            headp;
          data_at Ews (tarray tuchar max) (zst_lb L max lb (Znth j bytes)) nb;
          (if zeq max 0 then malloc_token Ews (tarray tuchar 0) nb else emp);
          data_at ish (tarray tuchar q) (sublist 0 q icont) ip;
          data_at ish (tarray tuchar (inn - q)) (sublist q inn icont) (offset_val q ip)))))))
  break:
    (@exp (environ -> mpred) _ (list val) (fun lb: list val =>
     PROP (Zlength lb = max; sublist 0 ln lb = byte_vals (sublist 0 ln bf))
     LOCAL (temp _state sp; temp _next (offset_val q ip); temp _have (zv have); temp _copy (zv c);
                    temp _len (zv b))
     SEP (field_at Ews t_state (DOT _length) (zv ln) sp;
          field_at Ews t_state (DOT _head) headp sp;
          data_at hsh t_head (vt, (vtm, (vxf, (vos, (vx, (vxl, (vxm, (vn, (vnm, (nb, (zv max, (vhc, vd))))))))))))
            headp;
          data_at Ews (tarray tuchar max) lb nb;
          (if zeq max 0 then malloc_token Ews (tarray tuchar 0) nb else emp);
          data_at ish (tarray tuchar q) (sublist 0 q icont) ip;
          data_at ish (tarray tuchar (inn - q)) (sublist q inn icont) (offset_val q ip)))).
  { Exists 0 L0 buf0 lb0. rewrite Z.sub_0_r. entailer!. }
  { Intros j L buf lb. subst max.
    forward. forward.
    pose proof (ncl_byte_j q have inn icont bytes j Q0 QH LI SB LB H) as BJ.
    assert (BYJ: 0 <= Znth j bytes <= Byte.max_unsigned).
    { apply (Forall_Znth bytes (fun b => 0 <= b <= Byte.max_unsigned)); [exact BB | rewrite LB; lia]. }
    assert (BJd: forall d, @Znth val d j (sublist q inn icont) = Vint (Int.repr (Znth j bytes))).
    { intros d. rewrite <- BJ. unfold Znth. destruct (Z_lt_dec j 0); [lia | ]. apply nth_indep.
      rewrite <- ZtoNat_Zlength. rewrite Zlength_sublist by lia. lia. }
    forward.
    { rewrite BJd. entailer!; lia. }
    rewrite BJd.
    forward.
    forward.
    fif_temp _t'41 (Vint Int.one).
    { forward. forward.
      forward.
      { entailer!. eapply ncl_test_eq6; [exact NN | | cancel]. lia. }
      entailer!. destruct nb; try contradiction. reflexivity. }
    { assert_PROP (isptr headp) by entailer!.
      match goal with X: headp = nullval |- _ => rewrite X in *; contradiction end. }
    assert (LR: 0 <= L <= Int.max_unsigned) by rep_lia.
    fif_temp _t'42 (Vint (if L <? (Zlength buf0) then Int.one else Int.zero)).
    { forward. forward. forward. forward. entailer!.
      destruct (Z.ltb_spec L (Zlength buf0)), (zlt L (Zlength buf0)); try reflexivity; lia. }
    { contra_tac. }
    forward_if.
    { (* store the byte *)
      assert (LT: L < (Zlength buf0)) by (destruct (Z.ltb_spec L (Zlength buf0)); [lia | contra_tac]).
      forward. forward. forward. forward. forward.
      Exists j L buf lb.
      unfold zst_L, zst_lb. cbn [andb]. rewrite (proj2 (Z.ltb_lt _ _) LT).
      rewrite ncl_zext_byte by lia.
      entailer!. apply derives_refl. }
    { assert (LT: (Zlength buf0) <= L) by (destruct (Z.ltb_spec L (Zlength buf0)); [contra_tac | lia]).
      forward.
      Exists j L buf lb.
      unfold zst_L, zst_lb. cbn [andb]. rewrite (proj2 (Z.ltb_ge _ _) LT).
      entailer!. } }
  Intros j L buf lb.
  rewrite (zstr_f_step bytes have L max true buf j) in H4 by lia. cbv zeta in H4.
  assert (BYJ: 0 <= Znth j bytes <= Byte.max_unsigned).
  { apply (Forall_Znth bytes (fun b => 0 <= b <= Byte.max_unsigned)); [exact BB | rewrite LB; lia]. }
  fif_temp _t'38 (Vint (if andb (negb (Znth j bytes =? 0)) (j + 1 <? have) then Int.one else Int.zero)).
  { forward. entailer!.
    match goal with X: Znth j bytes <> 0 |- _ => rewrite (proj2 (Z.eqb_neq _ _) X) end.
    cbn [negb andb]. destruct (Z.ltb_spec (j + 1) (Zlength bytes)), (zlt (j + 1) (Zlength bytes));
      try reflexivity; lia. }
  { forward. entailer!.
    match goal with X: Int.repr (Znth j bytes) = Int.zero |- _ =>
      apply (f_equal Int.unsigned) in X; rewrite Int.unsigned_repr in X by rep_lia; rewrite X end.
    reflexivity. }
  assert (ZL: L0 <= zst_L true L max <= max) by (unfold zst_L; cbn [andb]; destruct (Z.ltb_spec L max); lia).
  destruct (vrel_zst L max lb buf (Znth j bytes) ltac:(lia) H2 H1 H3) as (V1 & V2 & V3).
  forward_if.
  { destruct ((negb (Znth j bytes =? 0) && (j + 1 <? have))%bool) eqn:EC;
      [ | exfalso; match goal with X: _ <> Int.zero |- _ => apply X; reflexivity end].
    forward. Exists (j + 1) (zst_L true L max) (zst_buf true L max buf (Znth j bytes)) (zst_lb L max lb (Znth j bytes)).
    apply andb_prop in EC. destruct EC as [_ EC]. apply Z.ltb_lt in EC.
    entailer!. }
  { destruct ((negb (Znth j bytes =? 0) && (j + 1 <? have))%bool) eqn:EC; [contra_tac | ].
    forward. cbv zeta in H4. inversion H4; subst. Exists (zst_lb L (Zlength buf0) lb (Znth j bytes)). entailer!. }
  unfold abbreviate in POSTCONDITION; subst POSTCONDITION. unfold normal_ret_assert; cbn [RA_normal].
  Intros lb. Exists lb. entailer!.
  Unshelve. all: exact 0.
Qed.

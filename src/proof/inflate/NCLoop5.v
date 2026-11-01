(* inflate(), cases NAME (6) and COMMENT (7): the do-while that reads the zero-terminated string from next
   and stores it into head->name / head->comment (Model.v zstr_f), in a minimal context (the state's length
   and head fields, the gz_header, its string buffer with its token, the input object). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate.NCKit5.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Definition name_loop : statement :=
  (Sloop (Ssequence (Ssequence (Ssequence (Sset _t'32 (Etempvar _copy tuint)) (Sset _copy (Ebinop Cop.Oadd (Etempvar _t'32 tuint) (Econst_int (Int.repr 1) tint) tuint))) (Ssequence (Sset _t'382 (Ederef (Ebinop Cop.Oadd (Etempvar _next (tptr tuchar)) (Etempvar _t'32 tuint) (tptr tuchar)) tuchar)) (Sset _len (Ecast (Etempvar _t'382 tuchar) tuint)))) (Ssequence (Ssequence (Ssequence (Sset _t'379 (Efield (Ederef (Etempvar _state (tptr (Tstruct _inflate_state noattr))) (Tstruct _inflate_state noattr)) _head (tptr (Tstruct _gz_header_s noattr)))) (Sifthenelse (Ebinop Cop.One (Etempvar _t'379 (tptr (Tstruct _gz_header_s noattr))) (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint) (Ssequence (Sset _t'380 (Efield (Ederef (Etempvar _state (tptr (Tstruct _inflate_state noattr))) (Tstruct _inflate_state noattr)) _head (tptr (Tstruct _gz_header_s noattr)))) (Ssequence (Sset _t'381 (Efield (Ederef (Etempvar _t'380 (tptr (Tstruct _gz_header_s noattr))) (Tstruct _gz_header_s noattr)) _name (tptr tuchar))) (Sset _t'34 (Ecast (Ebinop Cop.One (Etempvar _t'381 (tptr tuchar)) (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint) tbool)))) (Sset _t'34 (Econst_int (Int.repr 0) tint)))) (Sifthenelse (Etempvar _t'34 tint) (Ssequence (Sset _t'376 (Efield (Ederef (Etempvar _state (tptr (Tstruct _inflate_state noattr))) (Tstruct _inflate_state noattr)) _length tuint)) (Ssequence (Sset _t'377 (Efield (Ederef (Etempvar _state (tptr (Tstruct _inflate_state noattr))) (Tstruct _inflate_state noattr)) _head (tptr (Tstruct _gz_header_s noattr)))) (Ssequence (Sset _t'378 (Efield (Ederef (Etempvar _t'377 (tptr (Tstruct _gz_header_s noattr))) (Tstruct _gz_header_s noattr)) _name_max tuint)) (Sset _t'35 (Ecast (Ebinop Cop.Olt (Etempvar _t'376 tuint) (Etempvar _t'378 tuint) tint) tbool))))) (Sset _t'35 (Econst_int (Int.repr 0) tint)))) (Sifthenelse (Etempvar _t'35 tint) (Ssequence (Ssequence (Sset _t'33 (Efield (Ederef (Etempvar _state (tptr (Tstruct _inflate_state noattr))) (Tstruct _inflate_state noattr)) _length tuint)) (Sassign (Efield (Ederef (Etempvar _state (tptr (Tstruct _inflate_state noattr))) (Tstruct _inflate_state noattr)) _length tuint) (Ebinop Cop.Oadd (Etempvar _t'33 tuint) (Econst_int (Int.repr 1) tint) tuint))) (Ssequence (Sset _t'374 (Efield (Ederef (Etempvar _state (tptr (Tstruct _inflate_state noattr))) (Tstruct _inflate_state noattr)) _head (tptr (Tstruct _gz_header_s noattr)))) (Ssequence (Sset _t'375 (Efield (Ederef (Etempvar _t'374 (tptr (Tstruct _gz_header_s noattr))) (Tstruct _gz_header_s noattr)) _name (tptr tuchar))) (Sassign (Ederef (Ebinop Cop.Oadd (Etempvar _t'375 (tptr tuchar)) (Etempvar _t'33 tuint) (tptr tuchar)) tuchar) (Ecast (Etempvar _len tuint) tuchar))))) Sskip))) (Ssequence (Sifthenelse (Etempvar _len tuint) (Sset _t'31 (Ecast (Ebinop Cop.Olt (Etempvar _copy tuint) (Etempvar _have tuint) tint) tbool)) (Sset _t'31 (Econst_int (Int.repr 0) tint))) (Sifthenelse (Etempvar _t'31 tint) Sskip Sbreak))).

Definition comm_loop : statement :=
  (Sloop (Ssequence (Ssequence (Ssequence (Sset _t'39 (Etempvar _copy tuint)) (Sset _copy (Ebinop Cop.Oadd (Etempvar _t'39 tuint) (Econst_int (Int.repr 1) tint) tuint))) (Ssequence (Sset _t'367 (Ederef (Ebinop Cop.Oadd (Etempvar _next (tptr tuchar)) (Etempvar _t'39 tuint) (tptr tuchar)) tuchar)) (Sset _len (Ecast (Etempvar _t'367 tuchar) tuint)))) (Ssequence (Ssequence (Ssequence (Sset _t'364 (Efield (Ederef (Etempvar _state (tptr (Tstruct _inflate_state noattr))) (Tstruct _inflate_state noattr)) _head (tptr (Tstruct _gz_header_s noattr)))) (Sifthenelse (Ebinop Cop.One (Etempvar _t'364 (tptr (Tstruct _gz_header_s noattr))) (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint) (Ssequence (Sset _t'365 (Efield (Ederef (Etempvar _state (tptr (Tstruct _inflate_state noattr))) (Tstruct _inflate_state noattr)) _head (tptr (Tstruct _gz_header_s noattr)))) (Ssequence (Sset _t'366 (Efield (Ederef (Etempvar _t'365 (tptr (Tstruct _gz_header_s noattr))) (Tstruct _gz_header_s noattr)) _comment (tptr tuchar))) (Sset _t'41 (Ecast (Ebinop Cop.One (Etempvar _t'366 (tptr tuchar)) (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint) tbool)))) (Sset _t'41 (Econst_int (Int.repr 0) tint)))) (Sifthenelse (Etempvar _t'41 tint) (Ssequence (Sset _t'361 (Efield (Ederef (Etempvar _state (tptr (Tstruct _inflate_state noattr))) (Tstruct _inflate_state noattr)) _length tuint)) (Ssequence (Sset _t'362 (Efield (Ederef (Etempvar _state (tptr (Tstruct _inflate_state noattr))) (Tstruct _inflate_state noattr)) _head (tptr (Tstruct _gz_header_s noattr)))) (Ssequence (Sset _t'363 (Efield (Ederef (Etempvar _t'362 (tptr (Tstruct _gz_header_s noattr))) (Tstruct _gz_header_s noattr)) _comm_max tuint)) (Sset _t'42 (Ecast (Ebinop Cop.Olt (Etempvar _t'361 tuint) (Etempvar _t'363 tuint) tint) tbool))))) (Sset _t'42 (Econst_int (Int.repr 0) tint)))) (Sifthenelse (Etempvar _t'42 tint) (Ssequence (Ssequence (Sset _t'40 (Efield (Ederef (Etempvar _state (tptr (Tstruct _inflate_state noattr))) (Tstruct _inflate_state noattr)) _length tuint)) (Sassign (Efield (Ederef (Etempvar _state (tptr (Tstruct _inflate_state noattr))) (Tstruct _inflate_state noattr)) _length tuint) (Ebinop Cop.Oadd (Etempvar _t'40 tuint) (Econst_int (Int.repr 1) tint) tuint))) (Ssequence (Sset _t'359 (Efield (Ederef (Etempvar _state (tptr (Tstruct _inflate_state noattr))) (Tstruct _inflate_state noattr)) _head (tptr (Tstruct _gz_header_s noattr)))) (Ssequence (Sset _t'360 (Efield (Ederef (Etempvar _t'359 (tptr (Tstruct _gz_header_s noattr))) (Tstruct _gz_header_s noattr)) _comment (tptr tuchar))) (Sassign (Ederef (Ebinop Cop.Oadd (Etempvar _t'360 (tptr tuchar)) (Etempvar _t'40 tuint) (tptr tuchar)) tuchar) (Ecast (Etempvar _len tuint) tuchar))))) Sskip))) (Ssequence (Sifthenelse (Etempvar _len tuint) (Sset _t'38 (Ecast (Ebinop Cop.Olt (Etempvar _copy tuint) (Etempvar _have tuint) tint) tbool)) (Sset _t'38 (Econst_int (Int.repr 0) tint))) (Sifthenelse (Etempvar _t'38 tint) Sskip Sbreak))).

(* ---------------------------------------------------------------------------------------------- *)
(* helpers                                                                                        *)

Lemma ncl_byte_vals_upd: forall l i b, 0 <= i < Zlength l ->
  byte_vals (upd_Znth i l b) = upd_Znth i (byte_vals l) (Vint (Int.repr b)).
Proof. intros. unfold byte_vals. rewrite <- upd_Znth_map. reflexivity. Qed.

Lemma ncl_hbuf_rep_nn: forall b max c, b <> nullval ->
  hbuf_rep b max c = data_at Ews (tarray tuchar max) (byte_vals c) b.
Proof. intros. unfold hbuf_rep. rewrite if_false by auto. reflexivity. Qed.

Lemma ncl_btok_nn: forall b max, b <> nullval ->
  btok b max = if zeq max 0 then malloc_token Ews (tarray tuchar 0) b else emp.
Proof. intros. unfold btok. rewrite if_false by auto. reflexivity. Qed.

Ltac fif_temp i v := match goal with |- semax _ (PROPx ?A (LOCALx ?Q (SEPx ?R))) _ _ =>
  forward_if (PROPx A (LOCALx (temp i v :: Q) (SEPx R))) end.

Ltac contra_tac := first
  [ match goal with X: ?a <> ?a |- _ => exfalso; apply X; reflexivity end
  | match goal with X: false = true |- _ => discriminate X end
  | match goal with X: true = false |- _ => discriminate X end
  | match goal with X: Int.one = Int.zero |- _ => discriminate X end
  | match goal with X: Int.zero = Int.one |- _ => discriminate X end
  | match goal with X: Int.zero <> Int.zero |- _ => exfalso; apply X; reflexivity end
  | match goal with X: Int.repr 0 <> Int.zero |- _ => exfalso; apply X; reflexivity end
  | match goal with X: Int.one = Int.repr 0 |- _ => discriminate X end ].

Lemma ncl_bool_dec: forall b: bool, {b = true} + {b = false}.
Proof. intros []; auto. Defined.

Local Transparent denote_tc_test_eq.
(* the string buffer (non-NULL) with its token gives the pointer comparison with NULL *)
Lemma ncl_test_eq: forall P nb max buf,
  nb <> nullval -> 0 <= max ->
  P |-- data_at Ews (tarray tuchar max) (byte_vals buf) nb * (if zeq max 0 then malloc_token Ews (tarray tuchar 0) nb else emp) * TT ->
  P |-- denote_tc_test_eq nb (Vlong (Int64.repr 0)).
Proof.
  intros P nb max buf NN Hm H. eapply derives_trans; [exact H | ].
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

(* the gz_header struct (head_rep's first item) *)
Definition hstruct (hsh: share) (headp xb nb cb: val) (h: hstate) : mpred :=
  data_at hsh t_head
    (zv (h_text h), (lv (h_time h), (zv (h_xflags h), (zv (h_os h),
     ((if h_xp h then xb else nullval), (zv (h_extra_len h), (zv (h_extra_max h),
     ((if h_np h then nb else nullval), (zv (h_name_max h),
     ((if h_cp h then cb else nullval), (zv (h_comm_max h), (zv (h_hcrc h), zv (h_done h)))))))))))))
    headp.

Definition ncl_pre (sp np: val) (have j: Z) (L: Z) (hd: bool) (headp: val) (HS: mpred) (BUF: mpred)
    (ish: share) (ip: val) (q inn: Z) (icont: list val) : environ -> mpred :=
  PROP () LOCAL (temp _state sp; temp _next np; temp _have (zv have); temp _copy (zv j))
  SEP (field_at Ews t_state (DOT _length) (zv L) sp;
       field_at Ews t_state (DOT _head) (if hd then headp else nullval) sp;
       HS; BUF; data_at ish (tarray tuchar inn) icont ip).

Lemma zstr_f_nowr: forall k bytes have L max buf j c b ln bf,
  zstr_f k bytes have L max false buf j = (c, b, ln, bf) -> ln = L /\ bf = buf.
Proof.
  induction k; intros bytes have L max buf j c b ln bf Z; simpl in Z.
  - inversion Z; auto.
  - destruct (negb (Znth j bytes =? 0) && (j + 1 <? have))%bool.
    + eapply IHk; exact Z.
    + inversion Z; auto.
Qed.

Lemma ncl_zext_byte: forall x, 0 <= x <= Byte.max_unsigned -> Int.zero_ext 8 (Int.repr x) = Int.repr x.
Proof.
  intros x H. rewrite <- (Int.repr_unsigned (Int.zero_ext 8 (Int.repr x))).
  rewrite Int.zero_ext_mod by (cbn; lia). rewrite Int.unsigned_repr by rep_lia.
  change (two_p 8) with 256. rewrite Z.mod_small by rep_lia. reflexivity.
Qed.

Lemma ncl_byte_j: forall q have inn icont bytes j,
  0 <= q -> q + have <= inn -> Zlength icont = inn -> sublist q (q + have) icont = byte_vals bytes ->
  Zlength bytes = have -> 0 <= j < have ->
  Znth j (sublist q inn icont) = Vint (Int.repr (Znth j bytes)).
Proof.
  intros q have inn icont bytes j Q QH LI SB LB J.
  rewrite Znth_sublist by lia.
  assert (E: Znth (j + q) icont = Znth j (sublist q (q + have) icont)) by (rewrite Znth_sublist by lia; f_equal; lia).
  rewrite E, SB. unfold byte_vals. rewrite Znth_map by lia. reflexivity.
Qed.

(* the loop when nothing is stored (no header, or no name buffer in it) *)
Lemma semax_name_loop_nowr {Espec: OracleKind} sp hd headp hsh xb nb cb h HB L0 have bytes ish ip q inn icont
    c b ln bf:
  readable_share hsh -> readable_share ish -> isptr ip ->
  0 <= q -> q + have <= inn -> Zlength icont = inn -> inn <= Ptrofs.max_unsigned ->
  sublist q (q + have) icont = byte_vals bytes -> Zlength bytes = have -> bytes_ok bytes ->
  0 < have <= Int.max_unsigned -> urange L0 -> 
  andb hd (h_np h) = false ->
  zstr_f (Z.to_nat have) bytes have L0 (h_name_max h) false (h_nbuf h) 0 = (c, b, ln, bf) ->
  semax Delta_cases5
    (PROP () LOCAL (temp _state sp; temp _next (offset_val q ip); temp _have (zv have); temp _copy (zv 0))
     SEP (field_at Ews t_state (DOT _length) (zv L0) sp;
          field_at Ews t_state (DOT _head) (if hd then headp else nullval) sp;
          if hd then hstruct hsh headp xb nb cb h else emp; HB;
          data_at ish (tarray tuchar inn) icont ip))
    name_loop
    (normal_ret_assert
     (PROP () LOCAL (temp _state sp; temp _next (offset_val q ip); temp _have (zv have); temp _copy (zv c);
                     temp _len (zv b))
      SEP (field_at Ews t_state (DOT _length) (zv L0) sp;
           field_at Ews t_state (DOT _head) (if hd then headp else nullval) sp;
           if hd then hstruct hsh headp xb nb cb h else emp; HB;
           data_at ish (tarray tuchar inn) icont ip))).
Proof.
  intros RH RI PI Q0 QH LI LM SB LB BB HV RL WR ZS.
  assert_PROP (field_compatible (tarray tuchar inn) [] ip) as FC by entailer!.
  rewrite (in_split ish inn icont ip q) by (auto; lia).
  unfold name_loop. abbreviate_semax.
  forward_loop
    (@exp (environ -> mpred) _ Z (fun j: Z =>
     PROP (0 <= j < have; zstr_f (Z.to_nat (have - j)) bytes have L0 (h_name_max h) false (h_nbuf h) j = (c, b, ln, bf))
     LOCAL (temp _state sp; temp _next (offset_val q ip); temp _have (zv have); temp _copy (zv j))
     SEP (field_at Ews t_state (DOT _length) (zv L0) sp;
          field_at Ews t_state (DOT _head) (if hd then headp else nullval) sp;
          if hd then hstruct hsh headp xb nb cb h else emp; HB;
          data_at ish (tarray tuchar q) (sublist 0 q icont) ip;
          data_at ish (tarray tuchar (inn - q)) (sublist q inn icont) (offset_val q ip))))
  continue:
    (@exp (environ -> mpred) _ Z (fun j: Z =>
     PROP (0 <= j < have; zstr_f (Z.to_nat (have - j)) bytes have L0 (h_name_max h) false (h_nbuf h) j = (c, b, ln, bf))
     LOCAL (temp _state sp; temp _next (offset_val q ip); temp _have (zv have); temp _copy (zv (j + 1));
            temp _len (zv (Znth j bytes)))
     SEP (field_at Ews t_state (DOT _length) (zv L0) sp;
          field_at Ews t_state (DOT _head) (if hd then headp else nullval) sp;
          if hd then hstruct hsh headp xb nb cb h else emp; HB;
          data_at ish (tarray tuchar q) (sublist 0 q icont) ip;
          data_at ish (tarray tuchar (inn - q)) (sublist q inn icont) (offset_val q ip))))
  break:
    (PROP () LOCAL (temp _state sp; temp _next (offset_val q ip); temp _have (zv have); temp _copy (zv c);
                    temp _len (zv b))
     SEP (field_at Ews t_state (DOT _length) (zv L0) sp;
          field_at Ews t_state (DOT _head) (if hd then headp else nullval) sp;
          if hd then hstruct hsh headp xb nb cb h else emp; HB;
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
    assert (NP: hd = true -> h_np h = false) by (intro E; rewrite E in WR; exact WR).
    destruct (ncl_bool_dec hd) as [HD | HD]; rewrite HD.
    - unfold hstruct. rewrite (NP HD).
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
          { forward. Exists j. rewrite HD. unfold hstruct. rewrite (NP HD). entailer!. }
    - forward.
      fif_temp _t'34 (Vint Int.zero).
      + contra_tac.
      + forward. entailer!.
      + fif_temp _t'35 (Vint Int.zero).
        * contra_tac.
        * forward. entailer!.
        * forward_if.
          { contra_tac. }
          { forward. Exists j. rewrite HD. entailer!. } }
  Intros j.
  rewrite (zstr_f_step bytes have L0 (h_name_max h) false (h_nbuf h) j) in H0 by lia.
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


(* the loop storing into the name buffer (a header whose name field is non-NULL) *)
Lemma semax_name_loop_wr {Espec: OracleKind} sp headp hsh xb nb cb h buf0 L0 have bytes ish ip q inn icont
    c b ln bf:
  readable_share hsh -> readable_share ish -> isptr ip ->
  0 <= q -> q + have <= inn -> Zlength icont = inn -> inn <= Ptrofs.max_unsigned ->
  sublist q (q + have) icont = byte_vals bytes -> Zlength bytes = have -> bytes_ok bytes ->
  0 < have <= Int.max_unsigned -> urange L0 -> 0 <= h_name_max h <= 65536 ->
  Zlength buf0 = h_name_max h -> bytes_ok buf0 ->
  h_np h = true -> nb <> nullval ->
  zstr_f (Z.to_nat have) bytes have L0 (h_name_max h) true buf0 0 = (c, b, ln, bf) ->
  semax Delta_cases5
    (PROP () LOCAL (temp _state sp; temp _next (offset_val q ip); temp _have (zv have); temp _copy (zv 0))
     SEP (field_at Ews t_state (DOT _length) (zv L0) sp;
          field_at Ews t_state (DOT _head) headp sp;
          hstruct hsh headp xb nb cb h;
          data_at Ews (tarray tuchar (h_name_max h)) (byte_vals buf0) nb;
          (if zeq (h_name_max h) 0 then malloc_token Ews (tarray tuchar 0) nb else emp);
          data_at ish (tarray tuchar inn) icont ip))
    name_loop
    (normal_ret_assert
     (PROP () LOCAL (temp _state sp; temp _next (offset_val q ip); temp _have (zv have); temp _copy (zv c);
                     temp _len (zv b))
      SEP (field_at Ews t_state (DOT _length) (zv ln) sp;
           field_at Ews t_state (DOT _head) headp sp;
           hstruct hsh headp xb nb cb h;
           data_at Ews (tarray tuchar (h_name_max h)) (byte_vals bf) nb;
           (if zeq (h_name_max h) 0 then malloc_token Ews (tarray tuchar 0) nb else emp);
           data_at ish (tarray tuchar inn) icont ip))).
Proof.
  intros RH RI PI Q0 QH LI LM SB LB BB HV RL MX LB0 BB0 NP NN ZS.
  unfold hstruct. rewrite NP.
  assert_PROP (field_compatible (tarray tuchar inn) [] ip) as FC by entailer!.
  assert_PROP (isptr nb) as PN.
  { destruct (zeq (h_name_max h) 0); [ | entailer!].
    sep_apply (malloc_token_local_facts Ews (tarray tuchar 0) nb). entailer!.
    }
  rewrite (in_split ish inn icont ip q) by (auto; lia).
  unfold name_loop. abbreviate_semax.
  forward_loop
    (@exp (environ -> mpred) _ Z (fun j: Z => @exp (environ -> mpred) _ Z (fun L: Z =>
     @exp (environ -> mpred) _ (list Z) (fun buf: list Z =>
     PROP (0 <= j < have; L0 <= L <= Z.max L0 (h_name_max h); Zlength buf = (h_name_max h); bytes_ok buf;
           zstr_f (Z.to_nat (have - j)) bytes have L (h_name_max h) true buf j = (c, b, ln, bf))
     LOCAL (temp _state sp; temp _next (offset_val q ip); temp _have (zv have); temp _copy (zv j))
     SEP (field_at Ews t_state (DOT _length) (zv L) sp;
          field_at Ews t_state (DOT _head) headp sp;
          data_at hsh t_head
            (zv (h_text h), (lv (h_time h), (zv (h_xflags h), (zv (h_os h),
             ((if h_xp h then xb else nullval), (zv (h_extra_len h), (zv (h_extra_max h),
             (nb, (zv (h_name_max h), ((if h_cp h then cb else nullval), (zv (h_comm_max h), (zv (h_hcrc h), zv (h_done h)))))))))))))
            headp;
          data_at Ews (tarray tuchar (h_name_max h)) (byte_vals buf) nb;
          (if zeq (h_name_max h) 0 then malloc_token Ews (tarray tuchar 0) nb else emp);
          data_at ish (tarray tuchar q) (sublist 0 q icont) ip;
          data_at ish (tarray tuchar (inn - q)) (sublist q inn icont) (offset_val q ip))))))
  continue:
    (@exp (environ -> mpred) _ Z (fun j: Z => @exp (environ -> mpred) _ Z (fun L: Z =>
     @exp (environ -> mpred) _ (list Z) (fun buf: list Z =>
     PROP (0 <= j < have; L0 <= L <= Z.max L0 (h_name_max h); Zlength buf = (h_name_max h); bytes_ok buf;
           zstr_f (Z.to_nat (have - j)) bytes have L (h_name_max h) true buf j = (c, b, ln, bf))
     LOCAL (temp _state sp; temp _next (offset_val q ip); temp _have (zv have); temp _copy (zv (j + 1));
            temp _len (zv (Znth j bytes)))
     SEP (field_at Ews t_state (DOT _length) (zv (zst_L true L (h_name_max h))) sp;
          field_at Ews t_state (DOT _head) headp sp;
          data_at hsh t_head
            (zv (h_text h), (lv (h_time h), (zv (h_xflags h), (zv (h_os h),
             ((if h_xp h then xb else nullval), (zv (h_extra_len h), (zv (h_extra_max h),
             (nb, (zv (h_name_max h), ((if h_cp h then cb else nullval), (zv (h_comm_max h), (zv (h_hcrc h), zv (h_done h)))))))))))))
            headp;
          data_at Ews (tarray tuchar (h_name_max h)) (byte_vals (zst_buf true L (h_name_max h) buf (Znth j bytes))) nb;
          (if zeq (h_name_max h) 0 then malloc_token Ews (tarray tuchar 0) nb else emp);
          data_at ish (tarray tuchar q) (sublist 0 q icont) ip;
          data_at ish (tarray tuchar (inn - q)) (sublist q inn icont) (offset_val q ip))))))
  break:
    (PROP () LOCAL (temp _state sp; temp _next (offset_val q ip); temp _have (zv have); temp _copy (zv c);
                    temp _len (zv b))
     SEP (field_at Ews t_state (DOT _length) (zv ln) sp;
          field_at Ews t_state (DOT _head) headp sp;
          data_at hsh t_head
            (zv (h_text h), (lv (h_time h), (zv (h_xflags h), (zv (h_os h),
             ((if h_xp h then xb else nullval), (zv (h_extra_len h), (zv (h_extra_max h),
             (nb, (zv (h_name_max h), ((if h_cp h then cb else nullval), (zv (h_comm_max h), (zv (h_hcrc h), zv (h_done h)))))))))))))
            headp;
          data_at Ews (tarray tuchar (h_name_max h)) (byte_vals bf) nb;
          (if zeq (h_name_max h) 0 then malloc_token Ews (tarray tuchar 0) nb else emp);
          data_at ish (tarray tuchar q) (sublist 0 q icont) ip;
          data_at ish (tarray tuchar (inn - q)) (sublist q inn icont) (offset_val q ip))).
  { Exists 0 L0 buf0. rewrite Z.sub_0_r. entailer!. }
  { Intros j L buf.
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
      { entailer!. eapply ncl_test_eq; [exact NN | | cancel]. lia. }
      entailer!. destruct nb; try contradiction. reflexivity. }
    { assert_PROP (isptr headp) by entailer!.
      match goal with X: headp = nullval |- _ => rewrite X in *; contradiction end. }
    assert (LR: 0 <= L <= Int.max_unsigned) by (unfold urange in RL; rep_lia).
    fif_temp _t'35 (Vint (if L <? (h_name_max h) then Int.one else Int.zero)).
    { forward. forward. forward. forward. entailer!.
      destruct (Z.ltb_spec L (h_name_max h)), (zlt L (h_name_max h)); try reflexivity; lia. }
    { contra_tac. }
    forward_if.
    { (* store the byte *)
      assert (LT: L < (h_name_max h)) by (destruct (Z.ltb_spec L (h_name_max h)); [lia | contra_tac]).
      forward. forward. forward. forward. forward.
      Exists j L buf.
      unfold zst_L, zst_buf. cbn [andb]. rewrite (proj2 (Z.ltb_lt _ _) LT).
      rewrite ncl_byte_vals_upd by lia.
      rewrite ncl_zext_byte by lia.
      entailer!. apply derives_refl. }
    { assert (LT: (h_name_max h) <= L) by (destruct (Z.ltb_spec L (h_name_max h)); [contra_tac | lia]).
      forward.
      Exists j L buf.
      unfold zst_L, zst_buf. cbn [andb]. rewrite (proj2 (Z.ltb_ge _ _) LT).
      entailer!. } }
  Intros j L buf.
  rewrite (zstr_f_step bytes have L (h_name_max h) true buf j) in H3 by lia. cbv zeta in H3.
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
  assert (ZL: L0 <= zst_L true L (h_name_max h) <= Z.max L0 (h_name_max h)) by (unfold zst_L; cbn [andb]; destruct (Z.ltb_spec L (h_name_max h)); lia).
  assert (ZB: Zlength (zst_buf true L (h_name_max h) buf (Znth j bytes)) = (h_name_max h) /\ bytes_ok (zst_buf true L (h_name_max h) buf (Znth j bytes))).
  { unfold zst_buf. cbn [andb]. destruct (Z.ltb_spec L (h_name_max h)); [ | auto].
    split; [rewrite upd_Znth_Zlength by (unfold urange in RL; lia); lia | apply Forall_upd_Znth; auto]. }
  forward_if.
  { destruct ((negb (Znth j bytes =? 0) && (j + 1 <? have))%bool) eqn:EC;
      [ | exfalso; match goal with X: _ <> Int.zero |- _ => apply X; reflexivity end].
    forward. Exists (j + 1) (zst_L true L (h_name_max h)) (zst_buf true L (h_name_max h) buf (Znth j bytes)).
    apply andb_prop in EC. destruct EC as [_ EC]. apply Z.ltb_lt in EC.
    entailer!. apply ZB. }
  { destruct ((negb (Znth j bytes =? 0) && (j + 1 <? have))%bool) eqn:EC; [contra_tac | ].
    forward. cbv zeta in H3. inversion H3; subst. entailer!. }
  unfold abbreviate in POSTCONDITION; subst POSTCONDITION. unfold normal_ret_assert; cbn [RA_normal]. entailer!.
  Unshelve. all: exact 0.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* COMMENT: the same loops over head->comment *)

(* the loop when nothing is stored (no header, or no comment buffer in it) *)
Lemma semax_comm_loop_nowr {Espec: OracleKind} sp hd headp hsh xb nb cb h HB L0 have bytes ish ip q inn icont
    c b ln bf:
  readable_share hsh -> readable_share ish -> isptr ip ->
  0 <= q -> q + have <= inn -> Zlength icont = inn -> inn <= Ptrofs.max_unsigned ->
  sublist q (q + have) icont = byte_vals bytes -> Zlength bytes = have -> bytes_ok bytes ->
  0 < have <= Int.max_unsigned -> urange L0 -> 
  andb hd (h_cp h) = false ->
  zstr_f (Z.to_nat have) bytes have L0 (h_comm_max h) false (h_nbuf h) 0 = (c, b, ln, bf) ->
  semax Delta_cases5
    (PROP () LOCAL (temp _state sp; temp _next (offset_val q ip); temp _have (zv have); temp _copy (zv 0))
     SEP (field_at Ews t_state (DOT _length) (zv L0) sp;
          field_at Ews t_state (DOT _head) (if hd then headp else nullval) sp;
          if hd then hstruct hsh headp xb nb cb h else emp; HB;
          data_at ish (tarray tuchar inn) icont ip))
    comm_loop
    (normal_ret_assert
     (PROP () LOCAL (temp _state sp; temp _next (offset_val q ip); temp _have (zv have); temp _copy (zv c);
                     temp _len (zv b))
      SEP (field_at Ews t_state (DOT _length) (zv L0) sp;
           field_at Ews t_state (DOT _head) (if hd then headp else nullval) sp;
           if hd then hstruct hsh headp xb nb cb h else emp; HB;
           data_at ish (tarray tuchar inn) icont ip))).
Proof.
  intros RH RI PI Q0 QH LI LM SB LB BB HV RL WR ZS.
  assert_PROP (field_compatible (tarray tuchar inn) [] ip) as FC by entailer!.
  rewrite (in_split ish inn icont ip q) by (auto; lia).
  unfold comm_loop. abbreviate_semax.
  forward_loop
    (@exp (environ -> mpred) _ Z (fun j: Z =>
     PROP (0 <= j < have; zstr_f (Z.to_nat (have - j)) bytes have L0 (h_comm_max h) false (h_nbuf h) j = (c, b, ln, bf))
     LOCAL (temp _state sp; temp _next (offset_val q ip); temp _have (zv have); temp _copy (zv j))
     SEP (field_at Ews t_state (DOT _length) (zv L0) sp;
          field_at Ews t_state (DOT _head) (if hd then headp else nullval) sp;
          if hd then hstruct hsh headp xb nb cb h else emp; HB;
          data_at ish (tarray tuchar q) (sublist 0 q icont) ip;
          data_at ish (tarray tuchar (inn - q)) (sublist q inn icont) (offset_val q ip))))
  continue:
    (@exp (environ -> mpred) _ Z (fun j: Z =>
     PROP (0 <= j < have; zstr_f (Z.to_nat (have - j)) bytes have L0 (h_comm_max h) false (h_nbuf h) j = (c, b, ln, bf))
     LOCAL (temp _state sp; temp _next (offset_val q ip); temp _have (zv have); temp _copy (zv (j + 1));
            temp _len (zv (Znth j bytes)))
     SEP (field_at Ews t_state (DOT _length) (zv L0) sp;
          field_at Ews t_state (DOT _head) (if hd then headp else nullval) sp;
          if hd then hstruct hsh headp xb nb cb h else emp; HB;
          data_at ish (tarray tuchar q) (sublist 0 q icont) ip;
          data_at ish (tarray tuchar (inn - q)) (sublist q inn icont) (offset_val q ip))))
  break:
    (PROP () LOCAL (temp _state sp; temp _next (offset_val q ip); temp _have (zv have); temp _copy (zv c);
                    temp _len (zv b))
     SEP (field_at Ews t_state (DOT _length) (zv L0) sp;
          field_at Ews t_state (DOT _head) (if hd then headp else nullval) sp;
          if hd then hstruct hsh headp xb nb cb h else emp; HB;
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
    assert (NP: hd = true -> h_cp h = false) by (intro E; rewrite E in WR; exact WR).
    destruct (ncl_bool_dec hd) as [HD | HD]; rewrite HD.
    - unfold hstruct. rewrite (NP HD).
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
          { forward. Exists j. rewrite HD. unfold hstruct. rewrite (NP HD). entailer!. }
    - forward.
      fif_temp _t'41 (Vint Int.zero).
      + contra_tac.
      + forward. entailer!.
      + fif_temp _t'42 (Vint Int.zero).
        * contra_tac.
        * forward. entailer!.
        * forward_if.
          { contra_tac. }
          { forward. Exists j. rewrite HD. entailer!. } }
  Intros j.
  rewrite (zstr_f_step bytes have L0 (h_comm_max h) false (h_nbuf h) j) in H0 by lia.
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


(* the loop storing into the comment buffer (a header whose name field is non-NULL) *)
Lemma semax_comm_loop_wr {Espec: OracleKind} sp headp hsh xb nb cb h buf0 L0 have bytes ish ip q inn icont
    c b ln bf:
  readable_share hsh -> readable_share ish -> isptr ip ->
  0 <= q -> q + have <= inn -> Zlength icont = inn -> inn <= Ptrofs.max_unsigned ->
  sublist q (q + have) icont = byte_vals bytes -> Zlength bytes = have -> bytes_ok bytes ->
  0 < have <= Int.max_unsigned -> urange L0 -> 0 <= h_comm_max h <= 65536 ->
  Zlength buf0 = h_comm_max h -> bytes_ok buf0 ->
  h_cp h = true -> cb <> nullval ->
  zstr_f (Z.to_nat have) bytes have L0 (h_comm_max h) true buf0 0 = (c, b, ln, bf) ->
  semax Delta_cases5
    (PROP () LOCAL (temp _state sp; temp _next (offset_val q ip); temp _have (zv have); temp _copy (zv 0))
     SEP (field_at Ews t_state (DOT _length) (zv L0) sp;
          field_at Ews t_state (DOT _head) headp sp;
          hstruct hsh headp xb nb cb h;
          data_at Ews (tarray tuchar (h_comm_max h)) (byte_vals buf0) cb;
          (if zeq (h_comm_max h) 0 then malloc_token Ews (tarray tuchar 0) cb else emp);
          data_at ish (tarray tuchar inn) icont ip))
    comm_loop
    (normal_ret_assert
     (PROP () LOCAL (temp _state sp; temp _next (offset_val q ip); temp _have (zv have); temp _copy (zv c);
                     temp _len (zv b))
      SEP (field_at Ews t_state (DOT _length) (zv ln) sp;
           field_at Ews t_state (DOT _head) headp sp;
           hstruct hsh headp xb nb cb h;
           data_at Ews (tarray tuchar (h_comm_max h)) (byte_vals bf) cb;
           (if zeq (h_comm_max h) 0 then malloc_token Ews (tarray tuchar 0) cb else emp);
           data_at ish (tarray tuchar inn) icont ip))).
Proof.
  intros RH RI PI Q0 QH LI LM SB LB BB HV RL MX LB0 BB0 NP NN ZS.
  unfold hstruct. rewrite NP.
  assert_PROP (field_compatible (tarray tuchar inn) [] ip) as FC by entailer!.
  assert_PROP (isptr cb) as PN.
  { destruct (zeq (h_comm_max h) 0); [ | entailer!].
    sep_apply (malloc_token_local_facts Ews (tarray tuchar 0) cb). entailer!.
    }
  rewrite (in_split ish inn icont ip q) by (auto; lia).
  unfold comm_loop. abbreviate_semax.
  forward_loop
    (@exp (environ -> mpred) _ Z (fun j: Z => @exp (environ -> mpred) _ Z (fun L: Z =>
     @exp (environ -> mpred) _ (list Z) (fun buf: list Z =>
     PROP (0 <= j < have; L0 <= L <= Z.max L0 (h_comm_max h); Zlength buf = (h_comm_max h); bytes_ok buf;
           zstr_f (Z.to_nat (have - j)) bytes have L (h_comm_max h) true buf j = (c, b, ln, bf))
     LOCAL (temp _state sp; temp _next (offset_val q ip); temp _have (zv have); temp _copy (zv j))
     SEP (field_at Ews t_state (DOT _length) (zv L) sp;
          field_at Ews t_state (DOT _head) headp sp;
          data_at hsh t_head
            (zv (h_text h), (lv (h_time h), (zv (h_xflags h), (zv (h_os h),
             ((if h_xp h then xb else nullval), (zv (h_extra_len h), (zv (h_extra_max h),
             ((if h_np h then nb else nullval), (zv (h_name_max h), (cb, (zv (h_comm_max h), (zv (h_hcrc h), zv (h_done h)))))))))))))
            headp;
          data_at Ews (tarray tuchar (h_comm_max h)) (byte_vals buf) cb;
          (if zeq (h_comm_max h) 0 then malloc_token Ews (tarray tuchar 0) cb else emp);
          data_at ish (tarray tuchar q) (sublist 0 q icont) ip;
          data_at ish (tarray tuchar (inn - q)) (sublist q inn icont) (offset_val q ip))))))
  continue:
    (@exp (environ -> mpred) _ Z (fun j: Z => @exp (environ -> mpred) _ Z (fun L: Z =>
     @exp (environ -> mpred) _ (list Z) (fun buf: list Z =>
     PROP (0 <= j < have; L0 <= L <= Z.max L0 (h_comm_max h); Zlength buf = (h_comm_max h); bytes_ok buf;
           zstr_f (Z.to_nat (have - j)) bytes have L (h_comm_max h) true buf j = (c, b, ln, bf))
     LOCAL (temp _state sp; temp _next (offset_val q ip); temp _have (zv have); temp _copy (zv (j + 1));
            temp _len (zv (Znth j bytes)))
     SEP (field_at Ews t_state (DOT _length) (zv (zst_L true L (h_comm_max h))) sp;
          field_at Ews t_state (DOT _head) headp sp;
          data_at hsh t_head
            (zv (h_text h), (lv (h_time h), (zv (h_xflags h), (zv (h_os h),
             ((if h_xp h then xb else nullval), (zv (h_extra_len h), (zv (h_extra_max h),
             ((if h_np h then nb else nullval), (zv (h_name_max h), (cb, (zv (h_comm_max h), (zv (h_hcrc h), zv (h_done h)))))))))))))
            headp;
          data_at Ews (tarray tuchar (h_comm_max h)) (byte_vals (zst_buf true L (h_comm_max h) buf (Znth j bytes))) cb;
          (if zeq (h_comm_max h) 0 then malloc_token Ews (tarray tuchar 0) cb else emp);
          data_at ish (tarray tuchar q) (sublist 0 q icont) ip;
          data_at ish (tarray tuchar (inn - q)) (sublist q inn icont) (offset_val q ip))))))
  break:
    (PROP () LOCAL (temp _state sp; temp _next (offset_val q ip); temp _have (zv have); temp _copy (zv c);
                    temp _len (zv b))
     SEP (field_at Ews t_state (DOT _length) (zv ln) sp;
          field_at Ews t_state (DOT _head) headp sp;
          data_at hsh t_head
            (zv (h_text h), (lv (h_time h), (zv (h_xflags h), (zv (h_os h),
             ((if h_xp h then xb else nullval), (zv (h_extra_len h), (zv (h_extra_max h),
             ((if h_np h then nb else nullval), (zv (h_name_max h), (cb, (zv (h_comm_max h), (zv (h_hcrc h), zv (h_done h)))))))))))))
            headp;
          data_at Ews (tarray tuchar (h_comm_max h)) (byte_vals bf) cb;
          (if zeq (h_comm_max h) 0 then malloc_token Ews (tarray tuchar 0) cb else emp);
          data_at ish (tarray tuchar q) (sublist 0 q icont) ip;
          data_at ish (tarray tuchar (inn - q)) (sublist q inn icont) (offset_val q ip))).
  { Exists 0 L0 buf0. rewrite Z.sub_0_r. entailer!. }
  { Intros j L buf.
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
      { entailer!. eapply ncl_test_eq; [exact NN | | cancel]. lia. }
      entailer!. destruct cb; try contradiction. reflexivity. }
    { assert_PROP (isptr headp) by entailer!.
      match goal with X: headp = nullval |- _ => rewrite X in *; contradiction end. }
    assert (LR: 0 <= L <= Int.max_unsigned) by (unfold urange in RL; rep_lia).
    fif_temp _t'42 (Vint (if L <? (h_comm_max h) then Int.one else Int.zero)).
    { forward. forward. forward. forward. entailer!.
      destruct (Z.ltb_spec L (h_comm_max h)), (zlt L (h_comm_max h)); try reflexivity; lia. }
    { contra_tac. }
    forward_if.
    { (* store the byte *)
      assert (LT: L < (h_comm_max h)) by (destruct (Z.ltb_spec L (h_comm_max h)); [lia | contra_tac]).
      forward. forward. forward. forward. forward.
      Exists j L buf.
      unfold zst_L, zst_buf. cbn [andb]. rewrite (proj2 (Z.ltb_lt _ _) LT).
      rewrite ncl_byte_vals_upd by lia.
      rewrite ncl_zext_byte by lia.
      entailer!. apply derives_refl. }
    { assert (LT: (h_comm_max h) <= L) by (destruct (Z.ltb_spec L (h_comm_max h)); [contra_tac | lia]).
      forward.
      Exists j L buf.
      unfold zst_L, zst_buf. cbn [andb]. rewrite (proj2 (Z.ltb_ge _ _) LT).
      entailer!. } }
  Intros j L buf.
  rewrite (zstr_f_step bytes have L (h_comm_max h) true buf j) in H3 by lia. cbv zeta in H3.
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
  assert (ZL: L0 <= zst_L true L (h_comm_max h) <= Z.max L0 (h_comm_max h)) by (unfold zst_L; cbn [andb]; destruct (Z.ltb_spec L (h_comm_max h)); lia).
  assert (ZB: Zlength (zst_buf true L (h_comm_max h) buf (Znth j bytes)) = (h_comm_max h) /\ bytes_ok (zst_buf true L (h_comm_max h) buf (Znth j bytes))).
  { unfold zst_buf. cbn [andb]. destruct (Z.ltb_spec L (h_comm_max h)); [ | auto].
    split; [rewrite upd_Znth_Zlength by (unfold urange in RL; lia); lia | apply Forall_upd_Znth; auto]. }
  forward_if.
  { destruct ((negb (Znth j bytes =? 0) && (j + 1 <? have))%bool) eqn:EC;
      [ | exfalso; match goal with X: _ <> Int.zero |- _ => apply X; reflexivity end].
    forward. Exists (j + 1) (zst_L true L (h_comm_max h)) (zst_buf true L (h_comm_max h) buf (Znth j bytes)).
    apply andb_prop in EC. destruct EC as [_ EC]. apply Z.ltb_lt in EC.
    entailer!. apply ZB. }
  { destruct ((negb (Znth j bytes =? 0) && (j + 1 <? have))%bool) eqn:EC; [contra_tac | ].
    forward. cbv zeta in H3. inversion H3; subst. entailer!. }
  unfold abbreviate in POSTCONDITION; subst POSTCONDITION. unfold normal_ret_assert; cbn [RA_normal]. entailer!.
  Unshelve. all: exact 0.
Qed.

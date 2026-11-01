(* Law inflate_decode, main: the prologue (draws, the three mallocs, isb, the bit writer, the wrapper's header),
   from main's precondition to the head of the block loop (IDMainKit.enc_inv, no block yet). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.HarnessRef
               Zlib.proof.adler32.MainLib.
Require Zlib.proof.crc32.HarnessRef.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.inflate_common.HarnessLib.
Require Import Zlib.proof.harness.inflate_common.DRefSpec.
Require Import Zlib.proof.rfc1951.Decode.
Require Import Zlib.proof.harness.inflate_decode.IDLawCS Zlib.proof.harness.inflate_decode.IDGlobals.
Require Import Zlib.harness.x_inflate_decode.code.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.harness.inflate_decode.IDMainKit.

Ltac ifpostv t v := match goal with |- semax _ (PROPx _ (LOCALx ?Q (SEPx ?R))) _ _ =>
  forward_if (PROPx [] (LOCALx (temp t v :: Q) (SEPx R))) end.

Ltac nullsplit p := let D := fresh "D" in
  assert (D: p = nullval \/ p <> nullval) by (destruct (eq_dec p nullval); auto);
  destruct D as [D|D]; [rewrite (if_true _ (eq_dec p nullval)) by exact D | rewrite (if_false _ (eq_dec p nullval)) by exact D; Intros].

Ltac infeas := exfalso; first [ contradiction
                              | match goal with H: _ |- _ => solve [discriminate H] end
                              | match goal with H: Int.repr _ = Int.repr _ |- _ =>
                                  apply repr_inj_signed in H; [lia | rep_lia | rep_lia] end
                              | lia ].
Ltac ptrcmp := match goal with |- context [sem_cmp_pp Ceq ?p _] =>
  match goal with H: field_compatible _ _ p |- _ =>
    let P := fresh in assert (P: isptr p) by (destruct H; auto); destruct p; try contradiction; reflexivity end end.
Ltac br := first [ solve [infeas] | solve [forward; entailer!; ptrcmp] ].
Ltac ret0 HR := match goal with P := _ : ret_assert |- _ => unfold abbreviate in P; subst P end; eapply semax_post with (R' := POST_id);
  [ apply andp_left2; unfold POST_id, frame_ret_assert, function_body_ret_assert; simpl; intros x;
    first [ normalize; contradiction | rewrite FF_sepcon; apply FF_left | apply FF_left ] .. |
    intros vl; rewrite HR; apply andp_left2; unfold POST_id; simpl;
    intros x; apply derives_refl |
    unfold POST_id; forward; Exists (Int.repr 0); entailer!; repeat (sep_apply data_at_data_at_); cancel ].

Lemma pro_bw_cs sh (v: reptype (Tstruct _bw noattr)) q :
  @data_at Zlib.contracts.x_inflate_decode.Harness.CS sh t_bw v q = @data_at CS sh (Tstruct _bw noattr) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_harness); [apply JMeq_refl | reflexivity]. Qed.

Lemma pro_bytes_cs sh n (v: list val) q :
  @data_at Zlib.contracts.x_inflate_decode.Harness.CS sh (tarray tuchar n) v q = @data_at CS sh (tarray tuchar n) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_harness); [apply JMeq_refl | reflexivity]. Qed.

Lemma pro_bw_init (sh bsh: share) cap buf w : 0 <= cap ->
  @data_at CS sh (Tstruct _bw noattr) (buf, (Vint (Int.repr 0), Vint (Int.repr 0))) w *
  @data_at_ CS bsh (tarray tuchar cap) buf |-- bw_at sh bsh [] cap buf w.
Proof.
  intros Hc. unfold bw_at, bw_rep. Exists (Zrepeat Vundef cap).
  rewrite pro_bw_cs, pro_bytes_cs, data_at__eq.
  change (Zlength (@nil bool) / 8) with 0. change (Zlength (@nil bool) mod 8) with 0.
  entailer!. unfold bw_bytes_ok. change (pack []) with (@nil Z). rewrite Zlength_Zrepeat by lia.
  split; [auto | split; [ change (Zlength (@nil Z)) with 0; lia | reflexivity ]].
Qed.

Lemma pro_Zlength_bits_le v : Zlength (bits_le v 8) = 8.
Proof. reflexivity. Qed.

Lemma pro_Zlength_bytes_bits l : Zlength (bytes_bits l) = 8 * Zlength l.
Proof.
  induction l as [|b l IH]; [reflexivity | ].
  change (bytes_bits (b :: l)) with (bits_le b 8 ++ bytes_bits l).
  rewrite Zlength_app, IH, pro_Zlength_bits_le, Zlength_cons. lia.
Qed.

Lemma pro_bytes_bits_snoc (l: list Z) i : 0 <= i < Zlength l ->
  bytes_bits (sublist 0 (i + 1) l) = bytes_bits (sublist 0 i l) ++ bits_le (Znth i l) 8.
Proof.
  intros Hi. rewrite (sublist_split 0 i (i + 1)) by lia. rewrite sublist_len_1 by lia.
  unfold bytes_bits. rewrite Coq.Lists.List.flat_map_app. simpl. rewrite ?app_nil_r. reflexivity.
Qed.

Lemma pro_isb_ok N : 1 <= N -> 
  Zlength (upd_Znth 0 (Zrepeat 0 N) 1) = N /\ is_bytes (upd_Znth 0 (Zrepeat 0 N) 1) /\
  Znth 0 (upd_Znth 0 (Zrepeat 0 N) 1) = 1.
Proof.
  intros HN. split; [ | split ].
  - rewrite upd_Znth_Zlength; rewrite Zlength_Zrepeat; lia.
  - unfold is_bytes. apply Forall_upd_Znth; [ | rep_lia ].
    apply Forall_forall. intros x Hx. unfold Zrepeat in Hx. apply repeat_spec in Hx. subst. rep_lia.
  - rewrite upd_Znth_same; [ reflexivity | rewrite Zlength_Zrepeat; lia ].
Qed.

Lemma pro_isb_rep N : 1 <= N ->
  upd_Znth 0 (Zrepeat (Vint (Int.repr 0)) N) (Vint (Int.zero_ext 8 (Int.repr 1))) =
  bytes_rep (upd_Znth 0 (Zrepeat 0 N) 1).
Proof. intros. unfold bytes_rep. rewrite <- upd_Znth_map. unfold Zrepeat. rewrite map_repeat. reflexivity. Qed.

Lemma pro_shl wb : 8 <= wb <= 15 -> Int.shl (Int.repr 1) (Int.repr wb) = Int.repr (2 ^ wb).
Proof.
  intros H. assert (wb = 8 \/ wb = 9 \/ wb = 10 \/ wb = 11 \/ wb = 12 \/ wb = 13 \/ wb = 14 \/ wb = 15) by lia.
  repeat match goal with H: _ \/ _ |- _ => destruct H end; subst; reflexivity.
Qed.

Lemma pro_zlib_vals wb flevel : 8 <= wb <= 15 -> 0 <= flevel <= Byte.max_unsigned ->
  Int.zero_ext 8 (Int.or (Int.shl (Int.sub (Int.repr wb) (Int.repr 8)) (Int.repr 4)) (Int.repr 8)) =
    Int.repr (Znth 0 (zlib_hdr wb (Z.land flevel 3) false)) /\
  Int.zero_ext 8
    (Int.add (Int.shl (Int.and (Int.repr flevel) (Int.repr 3)) (Int.repr 6))
       (Int.modu
          (Int.sub (Int.repr 31)
             (Int.modu
                (Int.add
                   (Int.shl (Int.or (Int.shl (Int.sub (Int.repr wb) (Int.repr 8)) (Int.repr 4)) (Int.repr 8))
                      (Int.repr 8))
                   (Int.shl (Int.and (Int.repr flevel) (Int.repr 3)) (Int.repr 6))) (Int.repr 31)))
          (Int.repr 31))) =
    Int.repr (Znth 1 (zlib_hdr wb (Z.land flevel 3) false)) /\
  0 <= Znth 0 (zlib_hdr wb (Z.land flevel 3) false) <= 255 /\
  0 <= Znth 1 (zlib_hdr wb (Z.land flevel 3) false) <= 255.
Proof.
  intros Hwb Hfl.
  replace (Int.and (Int.repr flevel) (Int.repr 3)) with (Int.repr (Z.land flevel 3))
    by (unfold Int.and; rewrite !Int.unsigned_repr by rep_lia; reflexivity).
  assert (E: Z.land flevel 3 = flevel mod 4) by (apply (Z.land_ones flevel 2); lia).
  rewrite E. assert (Hm: 0 <= flevel mod 4 < 4) by (apply Z.mod_pos_bound; lia).
  revert Hm. generalize (flevel mod 4). clear E Hfl flevel. intros fl Hm.
  assert (wb = 8 \/ wb = 9 \/ wb = 10 \/ wb = 11 \/ wb = 12 \/ wb = 13 \/ wb = 14 \/ wb = 15) by lia.
  assert (fl = 0 \/ fl = 1 \/ fl = 2 \/ fl = 3) by lia.
  repeat match goal with H: _ \/ _ |- _ => destruct H end; subst;
    (split; [ reflexivity | split; [ reflexivity | vm_compute; repeat split; intro X; discriminate X ] ]).
Qed.

Lemma pro_zlib_bits wb flevel :
  bytes_bits (hdr_bytes (id_wrapper 1 wb flevel)) =
  ([] ++ bits_le (Znth 0 (zlib_hdr wb (Z.land flevel 3) false)) 8) ++
  bits_le (Znth 1 (zlib_hdr wb (Z.land flevel 3) false)) 8.
Proof. reflexivity. Qed.

Lemma pro_gz_nth j : 0 <= j < 10 ->
  (forall d, @Znth val d j (zvals gz_vals) = Vint (Int.repr (Znth j gz_vals))) /\ 0 <= Znth j gz_vals <= 255.
Proof.
  intros Hj. assert (j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8 \/ j = 9) by lia.
  repeat match goal with H: _ \/ _ |- _ => destruct H end; subst; (split; [ intros; reflexivity | cbv; split; congruence ]).
Qed.

Lemma pro_gz_bits wb flevel : bytes_bits gz_vals = bytes_bits (hdr_bytes (id_wrapper 2 wb flevel)).
Proof. reflexivity. Qed.

Lemma pro_raw_bits wrap wb flevel : wrap <> 1 -> wrap <> 2 -> [] = bytes_bits (hdr_bytes (id_wrapper wrap wb flevel)).
Proof.
  intros H1 H2. unfold id_wrapper. rewrite (proj2 (Z.eqb_neq _ _) H1), (proj2 (Z.eqb_neq _ _) H2). reflexivity.
Qed.

Lemma pro_enc_nil W : enc_bits W [] = bytes_bits (hdr_bytes W).
Proof. unfold enc_bits. simpl. apply app_nil_r. Qed.

Lemma pro_data_at__arr {cs: compspecs} sh t n p :
  data_at_ sh (tarray t n) p = data_at sh (tarray t n) (Zrepeat (default_val t) n) p.
Proof. rewrite data_at__eq. reflexivity. Qed.

Lemma pro_shl18 : Int.unsigned (Int.shl (Int.repr 1) (Int.repr 18)) = 262144.
Proof. reflexivity. Qed.

Lemma pro_iws : Int.unsigned Int.iwordsize = 32.
Proof. reflexivity. Qed.

Lemma isb_upd (N i: Z) : 0 <= i < N ->
  upd_Znth i (Zrepeat (Vint (Int.repr 0)) i ++ Zrepeat Vundef (N - i)) (Vint (Int.zero_ext 8 (Int.repr 0))) =
  Zrepeat (Vint (Int.repr 0)) (i + 1) ++ Zrepeat Vundef (N - (i + 1)).
Proof. intros. list_solve. Qed.

Ltac hdr_cases wb flevel :=
  let Hfl := fresh in
  assert (Hfl: 0 <= Z.land flevel 3 < 4)
    by (change 3 with (Z.ones 2); rewrite Z.land_ones by lia; apply Z.mod_pos_bound; lia);
  revert Hfl; generalize (Z.land flevel 3); let fl := fresh "fl" in intros fl Hfl;
  assert (wb = 8 \/ wb = 9 \/ wb = 10 \/ wb = 11 \/ wb = 12 \/ wb = 13 \/ wb = 14 \/ wb = 15) by lia;
  assert (fl = 0 \/ fl = 1 \/ fl = 2 \/ fl = 3) by lia;
  repeat match goal with H: _ \/ _ |- _ => destruct H end; subst wb fl; reflexivity.

(* The rest of main's prologue after the isb loop (from `isb[0] = 1`), and after `maxd` (from `if (wrap == 1)`). *)
Definition S_r11 : statement := ltac:(get_sub (0 :: ones 10)%nat).
Definition S_r16 : statement := ltac:(get_sub (0 :: ones 15)%nat).

(* after the isb loop (the three object sizes abstracted) *)
Definition pro_P11 (gv: globals) (vw vll vlc vdc vs vosn: val) (Fr: mpred) (wrap wb flevel isel: Z) (datap srcp isbp: val) (N0 N1 N2: Z) : environ -> mpred :=
  (PROP ()
      LOCAL (temp _isb isbp; temp _src srcp; temp _data datap;
         temp _isel (Vint (Int.repr isel)); temp _flevel (Vint (Int.repr flevel));
         temp _wb (Vint (Int.repr wb)); temp _wrap (Vint (Int.repr wrap));
         lvar _osnap (tptr tuchar) vosn; lvar _s (Tstruct _z_stream_s noattr) vs;
         lvar _dcodes (tarray tushort 30) vdc; lvar _lcodes (tarray tushort 286) vlc;
         lvar _ll (tarray tuchar 316) vll; lvar _w (Tstruct _bw noattr) vw; gvars gv)
      SEP (mem_mgr gv; malloc_token Ews (tarray tuchar N1) isbp;
         data_at Ews (tarray tuchar N1) (Zrepeat (Vint (Int.repr 0)) N1) isbp;
         malloc_token Ews (tarray tuchar N2) srcp; data_at_ Ews (tarray tuchar N2) srcp;
         malloc_token Ews (tarray tuchar N0) datap; data_at_ Ews (tarray tuchar N0) datap;
         data_at_ Tsh (tptr tuchar) vosn; data_at_ Tsh (Tstruct _z_stream_s noattr) vs;
         data_at_ Tsh (tarray tushort 30) vdc; data_at_ Tsh (tarray tushort 286) vlc;
         data_at_ Tsh (tarray tuchar 316) vll; data_at_ Tsh (Tstruct _bw noattr) vw;
         dref_tabs gv Ers id_tabs; data_at Ers (tarray tuchar 19) (zvals clorder) (gv _cl_order);
         data_at Ers (tarray tuchar 10) (zvals gz_vals) (gv _gz); dres gv; Fr)).

(* before the wrapper's header: the bit writer empty *)
Definition pro_P16 (gv: globals) (vw vll vlc vdc vs vosn: val) (Fr: mpred) (wrap wb flevel isel: Z) (datap srcp isbp: val) (N0 N1 N2: Z) : environ -> mpred :=
  PROP () LOCAL (temp _maxd (Vint (Int.repr (2 ^ wb))); temp _isb isbp; temp _src srcp; temp _data datap;
         temp _isel (Vint (Int.repr isel)); temp _flevel (Vint (Int.repr flevel));
         temp _wb (Vint (Int.repr wb)); temp _wrap (Vint (Int.repr wrap));
         lvar _osnap (tptr tuchar) vosn; lvar _s (Tstruct _z_stream_s noattr) vs;
         lvar _dcodes (tarray tushort 30) vdc; lvar _lcodes (tarray tushort 286) vlc;
         lvar _ll (tarray tuchar 316) vll; lvar _w (Tstruct _bw noattr) vw; gvars gv)
    SEP (mem_mgr gv; malloc_token Ews (tarray tuchar N1) isbp;
         data_at Ews (tarray tuchar N1) (bytes_rep (upd_Znth 0 (Zrepeat 0 N1) 1)) isbp;
         malloc_token Ews (tarray tuchar N2) srcp;
         malloc_token Ews (tarray tuchar N0) datap; data_at_ Ews (tarray tuchar N0) datap;
         data_at_ Tsh (tptr tuchar) vosn; data_at_ Tsh (Tstruct _z_stream_s noattr) vs;
         data_at_ Tsh (tarray tushort 30) vdc; data_at_ Tsh (tarray tushort 286) vlc;
         data_at_ Tsh (tarray tuchar 316) vll; bw_at Tsh Ews [] N2 srcp vw;
         dref_tabs gv Ers id_tabs; data_at Ers (tarray tuchar 19) (zvals clorder) (gv _cl_order);
         data_at Ers (tarray tuchar 10) (zvals gz_vals) (gv _gz); dres gv; Fr).

Lemma pro_tail16 {Espec: OracleKind} (gv: globals) (vw vll vlc vdc vs vosn: val) (Fr: mpred) (wrap wb flevel isel: Z) (datap srcp isbp: val) (N0 N1 N2: Z) (Post: ret_assert) :
  0 <= wrap <= Byte.max_unsigned -> 8 <= wb <= 15 -> 0 <= flevel <= Byte.max_unsigned ->
  0 <= isel <= Byte.max_unsigned -> isptr datap -> isptr srcp -> isptr isbp ->
  262144 <= N0 <= 262144 -> 262145 <= N1 <= 262145 -> 524288 <= N2 <= 524288 ->
  (forall wrap wb flevel isel datap srcp isbp,
     par_ok wrap wb flevel isel -> isptr datap -> isptr srcp -> isptr isbp ->
     semax Delta_id (enc_inv gv vw vll vlc vdc vs vosn wrap wb flevel isel datap srcp isbp
                       (data_at Ers (tarray tuchar 10) (zvals gz_vals) (gv _gz) * Fr)%logic) S_blk Post) ->
  semax Delta_id (pro_P16 gv vw vll vlc vdc vs vosn Fr wrap wb flevel isel datap srcp isbp N0 N1 N2) S_r16 Post.
Proof.
  intros H Hwb' H1 H2 Pd Ps Pi HN0 HN1 HN2 Hk. destruct Post as [Pn Pb Pc Pr].
  unfold S_r16, pro_P16, Delta_id, Gmain_k. simplify_func_tycontext. abbreviate_semax.
  forward_if (PROP () LOCAL (temp _maxd (Vint (Int.repr (2 ^ wb))); temp _isb isbp; temp _src srcp; temp _data datap;
         temp _isel (Vint (Int.repr isel)); temp _flevel (Vint (Int.repr flevel));
         temp _wb (Vint (Int.repr wb)); temp _wrap (Vint (Int.repr wrap));
         lvar _osnap (tptr tuchar) vosn; lvar _s (Tstruct _z_stream_s noattr) vs;
         lvar _dcodes (tarray tushort 30) vdc; lvar _lcodes (tarray tushort 286) vlc;
         lvar _ll (tarray tuchar 316) vll; lvar _w (Tstruct _bw noattr) vw; gvars gv)
    SEP (mem_mgr gv; malloc_token Ews (tarray tuchar N1) isbp;
         data_at Ews (tarray tuchar N1) (bytes_rep (upd_Znth 0 (Zrepeat 0 N1) 1)) isbp;
         malloc_token Ews (tarray tuchar N2) srcp;
         malloc_token Ews (tarray tuchar N0) datap; data_at_ Ews (tarray tuchar N0) datap;
         data_at_ Tsh (tptr tuchar) vosn; data_at_ Tsh (Tstruct _z_stream_s noattr) vs;
         data_at_ Tsh (tarray tushort 30) vdc; data_at_ Tsh (tarray tushort 286) vlc;
         data_at_ Tsh (tarray tuchar 316) vll; bw_at Tsh Ews (bytes_bits (hdr_bytes (id_wrapper wrap wb flevel))) N2 srcp vw;
         dref_tabs gv Ers id_tabs; data_at Ers (tarray tuchar 19) (zvals clorder) (gv _cl_order);
         data_at Ers (tarray tuchar 10) (zvals gz_vals) (gv _gz); dres gv; Fr)).
  { subst wrap. forward. forward. forward.
    destruct (pro_zlib_vals wb flevel Hwb' H1) as (_ & _ & B0 & B1).
    forward_call (Tsh, Ews, @nil bool, N2, srcp, vw, Znth 0 (zlib_hdr wb (Z.land flevel 3) false)).
    { entailer!. simpl. hdr_cases wb flevel. }
    { unfold bw_room. change (Zlength (@nil bool)) with 0. change ((0 + 8 + 7) / 8) with 1. rep_lia. }
    forward_call (Tsh, Ews, [] ++ bits_le (Znth 0 (zlib_hdr wb (Z.land flevel 3) false)) 8, N2, srcp, vw,
                  Znth 1 (zlib_hdr wb (Z.land flevel 3) false)).
    { entailer!. simpl. hdr_cases wb flevel. }
    { unfold bw_room. rewrite Zlength_app, pro_Zlength_bits_le. change (Zlength (@nil bool)) with 0.
      change ((0 + 8 + 8 + 7) / 8) with 2. rep_lia. }
    rewrite <- pro_zlib_bits. entailer!. }
  { forward_if.
    { forward.
      forward_loop (EX i: Z,
          PROP (0 <= i <= 10)
          LOCAL (temp _i__1 (Vint (Int.repr i)); temp _maxd (Vint (Int.repr (2 ^ wb))); temp _isb isbp; temp _src srcp; temp _data datap;
         temp _isel (Vint (Int.repr isel)); temp _flevel (Vint (Int.repr flevel));
         temp _wb (Vint (Int.repr wb)); temp _wrap (Vint (Int.repr wrap));
         lvar _osnap (tptr tuchar) vosn; lvar _s (Tstruct _z_stream_s noattr) vs;
         lvar _dcodes (tarray tushort 30) vdc; lvar _lcodes (tarray tushort 286) vlc;
         lvar _ll (tarray tuchar 316) vll; lvar _w (Tstruct _bw noattr) vw; gvars gv)
          SEP (mem_mgr gv; malloc_token Ews (tarray tuchar N1) isbp;
         data_at Ews (tarray tuchar N1) (bytes_rep (upd_Znth 0 (Zrepeat 0 N1) 1)) isbp;
         malloc_token Ews (tarray tuchar N2) srcp;
         malloc_token Ews (tarray tuchar N0) datap; data_at_ Ews (tarray tuchar N0) datap;
         data_at_ Tsh (tptr tuchar) vosn; data_at_ Tsh (Tstruct _z_stream_s noattr) vs;
         data_at_ Tsh (tarray tushort 30) vdc; data_at_ Tsh (tarray tushort 286) vlc;
         data_at_ Tsh (tarray tuchar 316) vll; bw_at Tsh Ews (bytes_bits (sublist 0 i gz_vals)) N2 srcp vw;
         dref_tabs gv Ers id_tabs; data_at Ers (tarray tuchar 19) (zvals clorder) (gv _cl_order);
         data_at Ers (tarray tuchar 10) (zvals gz_vals) (gv _gz); dres gv; Fr))
        continue: (EX i: Z,
          PROP (0 <= i < 10)
          LOCAL (temp _i__1 (Vint (Int.repr i)); temp _maxd (Vint (Int.repr (2 ^ wb))); temp _isb isbp; temp _src srcp; temp _data datap;
         temp _isel (Vint (Int.repr isel)); temp _flevel (Vint (Int.repr flevel));
         temp _wb (Vint (Int.repr wb)); temp _wrap (Vint (Int.repr wrap));
         lvar _osnap (tptr tuchar) vosn; lvar _s (Tstruct _z_stream_s noattr) vs;
         lvar _dcodes (tarray tushort 30) vdc; lvar _lcodes (tarray tushort 286) vlc;
         lvar _ll (tarray tuchar 316) vll; lvar _w (Tstruct _bw noattr) vw; gvars gv)
          SEP (mem_mgr gv; malloc_token Ews (tarray tuchar N1) isbp;
         data_at Ews (tarray tuchar N1) (bytes_rep (upd_Znth 0 (Zrepeat 0 N1) 1)) isbp;
         malloc_token Ews (tarray tuchar N2) srcp;
         malloc_token Ews (tarray tuchar N0) datap; data_at_ Ews (tarray tuchar N0) datap;
         data_at_ Tsh (tptr tuchar) vosn; data_at_ Tsh (Tstruct _z_stream_s noattr) vs;
         data_at_ Tsh (tarray tushort 30) vdc; data_at_ Tsh (tarray tushort 286) vlc;
         data_at_ Tsh (tarray tuchar 316) vll; bw_at Tsh Ews (bytes_bits (sublist 0 (i + 1) gz_vals)) N2 srcp vw;
         dref_tabs gv Ers id_tabs; data_at Ers (tarray tuchar 19) (zvals clorder) (gv _cl_order);
         data_at Ers (tarray tuchar 10) (zvals gz_vals) (gv _gz); dres gv; Fr))
        break: (PROP ()
          LOCAL (temp _maxd (Vint (Int.repr (2 ^ wb))); temp _isb isbp; temp _src srcp; temp _data datap;
         temp _isel (Vint (Int.repr isel)); temp _flevel (Vint (Int.repr flevel));
         temp _wb (Vint (Int.repr wb)); temp _wrap (Vint (Int.repr wrap));
         lvar _osnap (tptr tuchar) vosn; lvar _s (Tstruct _z_stream_s noattr) vs;
         lvar _dcodes (tarray tushort 30) vdc; lvar _lcodes (tarray tushort 286) vlc;
         lvar _ll (tarray tuchar 316) vll; lvar _w (Tstruct _bw noattr) vw; gvars gv)
          SEP (mem_mgr gv; malloc_token Ews (tarray tuchar N1) isbp;
         data_at Ews (tarray tuchar N1) (bytes_rep (upd_Znth 0 (Zrepeat 0 N1) 1)) isbp;
         malloc_token Ews (tarray tuchar N2) srcp;
         malloc_token Ews (tarray tuchar N0) datap; data_at_ Ews (tarray tuchar N0) datap;
         data_at_ Tsh (tptr tuchar) vosn; data_at_ Tsh (Tstruct _z_stream_s noattr) vs;
         data_at_ Tsh (tarray tushort 30) vdc; data_at_ Tsh (tarray tushort 286) vlc;
         data_at_ Tsh (tarray tuchar 316) vll; bw_at Tsh Ews (bytes_bits gz_vals) N2 srcp vw;
         dref_tabs gv Ers id_tabs; data_at Ers (tarray tuchar 19) (zvals clorder) (gv _cl_order);
         data_at Ers (tarray tuchar 10) (zvals gz_vals) (gv _gz); dres gv; Fr)).
      { Exists 0. entailer!. }
      { Intros i. forward_if.
        { destruct (pro_gz_nth i ltac:(lia)) as (Eg & Bg).
          forward. { rewrite Eg. entailer!. rep_lia. }
          rewrite Eg.
          forward_call (Tsh, Ews, bytes_bits (sublist 0 i gz_vals), N2, srcp, vw, Znth i gz_vals).
          { unfold bw_room. rewrite pro_Zlength_bytes_bits, Zlength_sublist by (change (Zlength gz_vals) with 10; lia).
            split; [ rewrite Z.mul_comm, Z.mod_mul by lia; reflexivity | ].
            split; [lia | split; [ apply Z.div_le_upper_bound; lia | rep_lia ] ]. }
          Exists i. entailer!. rewrite pro_bytes_bits_snoc by (change (Zlength gz_vals) with 10; lia). cancel. }
        { forward. entailer!. assert (i = 10) by lia. subst i. apply derives_refl. } }
      { Intros i. forward. Exists (i + 1). entailer!. }
      subst wrap. rewrite (pro_gz_bits wb flevel). unfold POSTCONDITION, abbreviate. simpl_ret_assert. entailer!. }
    { forward. rewrite <- (pro_raw_bits wrap wb flevel) by auto. entailer!. } }
  forward. forward.
  assert (Hpar: par_ok wrap wb flevel isel) by (unfold par_ok; rep_lia).
  specialize (Hk wrap wb flevel isel datap srcp isbp Hpar Pd Ps Pi).
  unfold enc_inv, enc_at in Hk.
  replace 262144 with N0 in Hk by lia. replace 262145 with N1 in Hk by lia. replace 524288 with N2 in Hk by lia.
  unfold MORE_COMMANDS, POSTCONDITION, abbreviate.
  eapply semax_pre; [ | exact Hk ].
  Exists (@nil block) 0 (Zrepeat Vundef N0) (upd_Znth 0 (Zrepeat 0 N1) 1)
    (Zrepeat Vundef 316) (Zrepeat Vundef 286) (Zrepeat Vundef 30).
  rewrite pro_enc_nil.
  rewrite !pro_data_at__arr.
  entailer!.
  split; [ | split ].
  - unfold data_ok. change (expand [] []) with (@nil Z). rewrite Zlength_Zrepeat by lia.
    change (Zlength (@nil Z)) with 0. rewrite sublist_nil.
    split; [lia | split; [lia | split; [constructor | reflexivity]]].
  - unfold isb_ok. destruct (pro_isb_ok N1 ltac:(lia)) as (A & B & C).
    split; [lia | split; [exact B | ]].
    intros k Hk'. change (Zlength (@nil block)) with 0 in Hk'. assert (k = 0) by lia. subst k.
    change (Zlength (expand [] (firstn (Z.to_nat 0) (@nil block)))) with 0. rewrite C. lia.
  - unfold codes_ok. rewrite !Zlength_Zrepeat by lia. auto.
Qed.

Lemma pro_mid11 {Espec: OracleKind} (gv: globals) (vw vll vlc vdc vs vosn: val) (Fr: mpred) (wrap wb flevel isel: Z) (datap srcp isbp: val) (N0 N1 N2: Z) (Post: ret_assert) :
  0 <= wrap <= Byte.max_unsigned -> 8 <= wb <= 15 -> 0 <= flevel <= Byte.max_unsigned ->
  0 <= isel <= Byte.max_unsigned -> isptr datap -> isptr srcp -> isptr isbp ->
  262144 <= N0 <= 262144 -> 262145 <= N1 <= 262145 -> 524288 <= N2 <= 524288 ->
  (forall wrap wb flevel isel datap srcp isbp,
     par_ok wrap wb flevel isel -> isptr datap -> isptr srcp -> isptr isbp ->
     semax Delta_id (enc_inv gv vw vll vlc vdc vs vosn wrap wb flevel isel datap srcp isbp
                       (data_at Ers (tarray tuchar 10) (zvals gz_vals) (gv _gz) * Fr)%logic) S_blk Post) ->
  semax Delta_id (pro_P11 gv vw vll vlc vdc vs vosn Fr wrap wb flevel isel datap srcp isbp N0 N1 N2) S_r11 Post.
Proof.
  intros H Hwb' H1 H2 Pd Ps Pi HN0 HN1 HN2 Hk. destruct Post as [Pn Pb Pc Pr].
  unfold S_r11, pro_P11, Delta_id, Gmain_k. simplify_func_tycontext. abbreviate_semax.
  forward. forward. forward. forward.
  forward. { entailer!. rewrite pro_iws. lia. }
  rewrite pro_shl by lia.
  sep_apply (pro_bw_init Tsh Ews N2 srcp vw); [ lia | ].
  rewrite pro_isb_rep by lia.
  unfold MORE_COMMANDS, POSTCONDITION, abbreviate.
  eapply semax_pre; [ | apply (pro_tail16 gv vw vll vlc vdc vs vosn Fr wrap wb flevel isel datap srcp isbp N0 N1 N2); auto ].
  unfold pro_P16. entailer!.
Qed.

Lemma id_pro_ok {Espec: OracleKind} gv vw vll vlc vdc vs vosn Fr (Post: ret_assert) :
  RA_return Post = RA_return POST_id ->
  (forall wrap wb flevel isel datap srcp isbp,
     par_ok wrap wb flevel isel -> isptr datap -> isptr srcp -> isptr isbp ->
     semax Delta_id (enc_inv gv vw vll vlc vdc vs vosn wrap wb flevel isel datap srcp isbp
                       (data_at Ers (tarray tuchar 10) (zvals gz_vals) (gv _gz) * Fr)%logic) S_blk Post) ->
  semax Delta_id (pro_pre gv vw vll vlc vdc vs vosn Fr) S_body Post.
Proof.
  intros HR Hk. destruct Post as [Pn Pb Pc Pr]. simpl in HR.
  unfold S_body, pro_pre, Delta_id, Gmain_k. simplify_func_tycontext. abbreviate_semax.
  forward_call tt. Intros wrap.
  forward_call tt. Intros wb.
  forward_call tt. Intros flevel.
  forward_call tt. Intros isel.
  forward_if (PROP () LOCAL (temp _t'5 (Vint (Int.repr (if andb (8 <=? wb) (wb <=? 15) then 1 else 0)));
     temp _isel (Vint (Int.repr isel)); temp _flevel (Vint (Int.repr flevel)); temp _wb (Vint (Int.repr wb));
     temp _wrap (Vint (Int.repr wrap));
     lvar _osnap (tptr tuchar) vosn; lvar _s (Tstruct _z_stream_s noattr) vs;
     lvar _dcodes (tarray tushort 30) vdc; lvar _lcodes (tarray tushort 286) vlc;
     lvar _ll (tarray tuchar 316) vll; lvar _w (Tstruct _bw noattr) vw; gvars gv)
   SEP (data_at_ Tsh (tptr tuchar) vosn; data_at_ Tsh (Tstruct _z_stream_s noattr) vs;
       data_at_ Tsh (tarray tushort 30) vdc; data_at_ Tsh (tarray tushort 286) vlc;
       data_at_ Tsh (tarray tuchar 316) vll; data_at_ Tsh (Tstruct _bw noattr) vw; mem_mgr gv;
       dref_tabs gv Ers id_tabs; data_at Ers (tarray tuchar 19) (zvals clorder) (gv _cl_order);
       data_at Ers (tarray tuchar 10) (zvals gz_vals) (gv _gz); dres gv; Fr)).
  { forward. entailer!. destruct (zlt 15 wb), (Z.leb_spec 8 wb), (Z.leb_spec wb 15); simpl; try reflexivity; lia. }
  { forward. entailer!. destruct (Z.leb_spec 8 wb); simpl; try reflexivity; lia. }
  forward_call (Int.repr (if andb (8 <=? wb) (wb <=? 15) then 1 else 0)).
  match goal with H: Int.repr (if _ then 1 else 0) <> Int.zero |- _ => rename H into Hwb end.
  assert (Hwb': 8 <= wb <= 15).
  { destruct (Z.leb_spec 8 wb), (Z.leb_spec wb 15); simpl in Hwb; try lia; contradiction. }
  clear Hwb.
  forward_call (tarray tuchar 262144, gv).
  { simpl; rep_lia. }
  Intros datap.
  forward_call (tarray tuchar 524288, gv).
  { simpl; rep_lia. }
  Intros srcp.
  forward_call (tarray tuchar 262145, gv).
  { simpl; rep_lia. }
  Intros isbp.
  nullsplit datap.
  { ifpostv _t'9 (Vint (Int.repr 1)); [ br .. | ].
    ifpostv _t'10 (Vint (Int.repr 1)); [ br .. | ].
    forward_if (PROP (False) LOCAL () SEP ()).
    { ret0 HR. }
    { br. } }
  nullsplit srcp.
  { ifpostv _t'9 (Vint (Int.repr 1)); [ br .. | ].
    ifpostv _t'10 (Vint (Int.repr 1)); [ br .. | ].
    forward_if (PROP (False) LOCAL () SEP ()); [ ret0 HR | br ]. }
  nullsplit isbp.
  { ifpostv _t'9 (Vint (Int.repr 0)); [ br .. | ].
    ifpostv _t'10 (Vint (Int.repr 1)); [ br .. | ].
    forward_if (PROP (False) LOCAL () SEP ()); [ ret0 HR | br ]. }
  ifpostv _t'9 (Vint (Int.repr 0)); [ br .. | ].
  ifpostv _t'10 (Vint (Int.repr 0)); [ br .. | ].
  match goal with |- semax _ (PROPx _ (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx [] (LOCALx Q (SEPx R))) end; [ br | forward; entailer! | ].
  abbreviate_semax.
  assert_PROP (isptr datap /\ isptr srcp /\ isptr isbp) as Pdsi by entailer!.
  destruct Pdsi as (Pd & Ps & Pi).
  remember 262144 as N0 eqn:EN0. remember 262145 as N1 eqn:EN1. remember 524288 as N2 eqn:EN2.
  assert (HN0: 262144 <= N0 <= 262144) by lia.
  assert (HN1: 262145 <= N1 <= 262145) by lia.
  assert (HN2: 524288 <= N2 <= 524288) by lia.
  clear EN0 EN1 EN2.
  forward.
  forward_loop (EX i: Z,
      PROP (0 <= i <= N1)
      LOCAL (temp _i (Vint (Int.repr i)); temp _isb isbp; temp _src srcp; temp _data datap;
         temp _isel (Vint (Int.repr isel)); temp _flevel (Vint (Int.repr flevel));
         temp _wb (Vint (Int.repr wb)); temp _wrap (Vint (Int.repr wrap));
         lvar _osnap (tptr tuchar) vosn; lvar _s (Tstruct _z_stream_s noattr) vs;
         lvar _dcodes (tarray tushort 30) vdc; lvar _lcodes (tarray tushort 286) vlc;
         lvar _ll (tarray tuchar 316) vll; lvar _w (Tstruct _bw noattr) vw; gvars gv)
      SEP (mem_mgr gv; malloc_token Ews (tarray tuchar N1) isbp;
         data_at Ews (tarray tuchar N1) (Zrepeat (Vint (Int.repr 0)) i ++ Zrepeat Vundef (N1 - i)) isbp;
         malloc_token Ews (tarray tuchar N2) srcp; data_at_ Ews (tarray tuchar N2) srcp;
         malloc_token Ews (tarray tuchar N0) datap; data_at_ Ews (tarray tuchar N0) datap;
         data_at_ Tsh (tptr tuchar) vosn; data_at_ Tsh (Tstruct _z_stream_s noattr) vs;
         data_at_ Tsh (tarray tushort 30) vdc; data_at_ Tsh (tarray tushort 286) vlc;
         data_at_ Tsh (tarray tuchar 316) vll; data_at_ Tsh (Tstruct _bw noattr) vw;
         dref_tabs gv Ers id_tabs; data_at Ers (tarray tuchar 19) (zvals clorder) (gv _cl_order);
         data_at Ers (tarray tuchar 10) (zvals gz_vals) (gv _gz); dres gv; Fr))
    continue: (EX i: Z,
      PROP (0 <= i < N1)
      LOCAL (temp _i (Vint (Int.repr i)); temp _isb isbp; temp _src srcp; temp _data datap;
         temp _isel (Vint (Int.repr isel)); temp _flevel (Vint (Int.repr flevel));
         temp _wb (Vint (Int.repr wb)); temp _wrap (Vint (Int.repr wrap));
         lvar _osnap (tptr tuchar) vosn; lvar _s (Tstruct _z_stream_s noattr) vs;
         lvar _dcodes (tarray tushort 30) vdc; lvar _lcodes (tarray tushort 286) vlc;
         lvar _ll (tarray tuchar 316) vll; lvar _w (Tstruct _bw noattr) vw; gvars gv)
      SEP (mem_mgr gv; malloc_token Ews (tarray tuchar N1) isbp;
         data_at Ews (tarray tuchar N1) (Zrepeat (Vint (Int.repr 0)) (i + 1) ++ Zrepeat Vundef (N1 - (i + 1))) isbp;
         malloc_token Ews (tarray tuchar N2) srcp; data_at_ Ews (tarray tuchar N2) srcp;
         malloc_token Ews (tarray tuchar N0) datap; data_at_ Ews (tarray tuchar N0) datap;
         data_at_ Tsh (tptr tuchar) vosn; data_at_ Tsh (Tstruct _z_stream_s noattr) vs;
         data_at_ Tsh (tarray tushort 30) vdc; data_at_ Tsh (tarray tushort 286) vlc;
         data_at_ Tsh (tarray tuchar 316) vll; data_at_ Tsh (Tstruct _bw noattr) vw;
         dref_tabs gv Ers id_tabs; data_at Ers (tarray tuchar 19) (zvals clorder) (gv _cl_order);
         data_at Ers (tarray tuchar 10) (zvals gz_vals) (gv _gz); dres gv; Fr))
    break: (PROP ()
      LOCAL (temp _isb isbp; temp _src srcp; temp _data datap;
         temp _isel (Vint (Int.repr isel)); temp _flevel (Vint (Int.repr flevel));
         temp _wb (Vint (Int.repr wb)); temp _wrap (Vint (Int.repr wrap));
         lvar _osnap (tptr tuchar) vosn; lvar _s (Tstruct _z_stream_s noattr) vs;
         lvar _dcodes (tarray tushort 30) vdc; lvar _lcodes (tarray tushort 286) vlc;
         lvar _ll (tarray tuchar 316) vll; lvar _w (Tstruct _bw noattr) vw; gvars gv)
      SEP (mem_mgr gv; malloc_token Ews (tarray tuchar N1) isbp;
         data_at Ews (tarray tuchar N1) (Zrepeat (Vint (Int.repr 0)) N1) isbp;
         malloc_token Ews (tarray tuchar N2) srcp; data_at_ Ews (tarray tuchar N2) srcp;
         malloc_token Ews (tarray tuchar N0) datap; data_at_ Ews (tarray tuchar N0) datap;
         data_at_ Tsh (tptr tuchar) vosn; data_at_ Tsh (Tstruct _z_stream_s noattr) vs;
         data_at_ Tsh (tarray tushort 30) vdc; data_at_ Tsh (tarray tushort 286) vlc;
         data_at_ Tsh (tarray tuchar 316) vll; data_at_ Tsh (Tstruct _bw noattr) vw;
         dref_tabs gv Ers id_tabs; data_at Ers (tarray tuchar 19) (zvals clorder) (gv _cl_order);
         data_at Ers (tarray tuchar 10) (zvals gz_vals) (gv _gz); dres gv; Fr)).
  { Exists 0. entailer!. rewrite data_at__eq; apply derives_refl. }
  { Intros i.
    forward_if.
    { rewrite pro_shl18 in *.
      forward. rewrite isb_upd by lia. Exists i. entailer!. }
    { forward. entailer!. assert (i = N1) by (rewrite pro_shl18 in *; lia). subst i.
      rewrite Z.sub_diag, Zrepeat_0, app_nil_r. apply derives_refl. } }
  { Intros i. forward. Exists (i + 1). entailer!. }
  unfold MORE_COMMANDS, POSTCONDITION, abbreviate.
  apply (pro_mid11 gv vw vll vlc vdc vs vosn Fr wrap wb flevel isel datap srcp isbp N0 N1 N2); auto.
Qed.

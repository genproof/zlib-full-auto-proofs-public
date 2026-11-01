(* inflate()'s exit inf_leave, UPDATE_CHECK of the tail for calls of any uInt size (RTH9ExitTail.v): the proof
   script of src/proof/hl/inflate_api/HlBody5ExitTail.v's et_chk_ok_hl (copied by hand) with tail_facts9. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.hl.inflate_api.HlBody5Parts.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.hl.inflate_api.HlBody5ExitKit.
Require Import Zlib.proof.hl.inflate_api.HlBody5ExitTail.

Require Import Zlib.proof.roundtrip.RTH9ExitTail.

#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Lemma et_chk_ok9 {Espec: OracleKind} (F: frame) (X: mpred) (m: mst):
  frame_ok5 F -> tail_facts9 m ->
  semax Delta_inflate5_hl (tst_hl F X m (lt_m1 m) (lt_inn m) (lt_out m)) et_chk
    (normal_ret_assert (tst_hl F X m (lt_m2 m) (lt_inn m) (lt_out m))).
Proof.
  intros FOK TF.
  pose proof (lt_out_eq9 m TF) as [EO RO].
  pose proof TF as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9 & T10 & T11 & T12 & T13 & T14 & T15 & _).
  pose proof FOK as ((HWS & HWH & HRG & HRT) & HFL).
  cbv beta iota zeta delta [et_chk ex_tail inflate_exit f_inflate fn_body].
  unfold lt_m2. destruct (lt_cond m) eqn:Ec.
  2: { unfold tst_hl. abbreviate_semax. Intros.
       forward.
       forward_if (temp _t'103 (Vint Int.zero)).
       - forward. entailer!.
         unfold lt_cond in Ec.
         match goal with HA: Int.and _ _ <> Int.zero |- _ => rewrite (ck_flagbit _ _ HA) in Ec end.
         cbn [negb andb] in Ec.
         apply negb_false_iff, Z.eqb_eq in Ec. rewrite Ec. reflexivity.
       - forward. entailer!.
       - forward_if.
         + exfalso. match goal with HA: 0 <> 0 |- _ => apply HA; reflexivity end.
         + forward. entailer!. }
  unfold lt_cond in Ec. apply andb_prop in Ec. destruct Ec as [Ec1 Ec2].
  apply negb_true_iff, Z.eqb_neq in Ec1. apply negb_true_iff, Z.eqb_neq in Ec2.
  set (c := lt_c m). set (o := lt_out m) in *.
  destruct F as [gv shs strmp sp headp winp hsh xb nb cb ib ob gsh tsh dt vres vhere vlast vhbuf flush].
  destruct ob as [osh op olo on oc].
  unfold tst_hl, strm_e, strm_rep. cbn [f_ob f_gv f_sp f_strmp f_shs f_ib f_tsh f_dt f_vres f_vhere f_vlast f_vhbuf f_flush] in *.
  abbreviate_semax. Intros.
  assert (P1: m_ow (lt_m1 m) = m_ow m /\ m_aout (lt_m1 m) = m_aout m /\ m_sow (lt_m1 m) = Zlength (m_ow m) /\
              i_check (m_s (lt_m1 m)) = i_check (m_s m) /\ i_flags (m_s (lt_m1 m)) = i_flags (m_s m) /\
              i_wrap (m_s (lt_m1 m)) = i_wrap (m_s m))
    by (unfold lt_m1, upd_s; cbn; rewrite T2; repeat split; reflexivity).
  assert (Hc: c = update_check (i_flags (m_s m)) (i_check (m_s m)) (sublist (Zlength (m_ow m) - o) (Zlength (m_ow m)) (m_ow m)))
    by reflexivity.
  clearbody c.
  set (m1 := lt_m1 m) in *. clearbody m1.
  destruct P1 as (P1 & P2 & P3 & P4 & P5 & P6).
  rewrite P1, P2, P3, P4, P5, P6 in *.
  destruct H as (Hosh & Hop & Holo & Haout & Hlo & Hoc & Hon).
  unfold out_rep, out_ptr.
  remember (gv _zcalloc) as zca eqn:Hzca. remember (gv _zcfree) as zcf eqn:Hzcf.
  forward.
  forward_if (temp _t'103 (Vint Int.one)).
  { forward. entailer!. rewrite ck_tbool by rep_lia. rewrite (proj2 (Z.eqb_neq _ _) Ec2). reflexivity. }
  { exfalso. apply Ec1. apply Z.eqb_eq.
    match goal with HA: Int.and _ _ = Int.zero |- _ => apply (ck_flagbit0 _ _ HA); rep_lia end. }
  forward_if; [ | exfalso; match goal with HA: Int.one = Int.zero |- _ => exact (Int.one_not_zero HA) end].
  forward.
  set (ct := sublist 0 olo oc ++ byte_vals (m_ow m) ++ sublist (olo + Zlength (m_ow m)) on oc).
  set (d := sublist (Zlength (m_ow m) - o) (Zlength (m_ow m)) (m_ow m)) in Hc.
  assert (CB: cbuf_ok false (offset_val (olo + Zlength (m_ow m) - o) op) osh op (olo + Zlength (m_ow m) - o) on o ct d).
  { unfold cbuf_ok. split; [reflexivity | ]. split; [auto | ]. split; [lia | ]. split; [lia | ].
    split; [unfold d; rewrite Zlength_sublist by lia; lia | ]. split.
    { unfold d. apply Forall_sublist. exact T9. }
    unfold ct, d, bytes_rep, byte_vals. autorewrite with sublist. list_solve. }
  assert (PT: force_val (sem_sub_pi tuchar Unsigned (offset_val (olo + Zlength (m_ow m)) op) (Vint (Int.repr o))) =
              offset_val (olo + Zlength (m_ow m) - o) op).
  { destruct op; try contradiction. simpl. unfold sem_sub_pi. simpl.
    rewrite Ptrofs.mul_commut, Ptrofs.mul_one. unfold Ptrofs.of_intu, Ptrofs.of_int.
    rewrite Int.unsigned_repr by rep_lia. f_equal.
    rewrite Ptrofs.sub_add_opp, Ptrofs.add_assoc. f_equal.
    rewrite Ptrofs.neg_repr, ptrofs_add_repr. f_equal; lia. }
  forward_if (temp _t'99 (Vlong (Int64.repr c))).
  { (* crc32 *)
    forward. forward.
    forward_call (i_check (m_s m), offset_val (olo + Zlength (m_ow m) - o) op, o, false, osh, op,
                  olo + Zlength (m_ow m) - o, on, ct, d, false, Ews, gv, tsh).
    { rewrite <- ck_da_cs_crc. cancel. }
    { apply cbuf_valid_pos. lia. }
    forward.
    rewrite Hc. unfold update_check. rewrite (proj2 (Z.eqb_neq _ _) H0'). rewrite <- ck_da_cs_crc.
    entailer!. }
  { (* adler32 *)
    forward. forward.
    forward_call (i_check (m_s m), offset_val (olo + Zlength (m_ow m) - o) op, o, false, osh, op,
                  olo + Zlength (m_ow m) - o, on, ct, d, false, Ews).
    { rewrite <- ck_da_cs_adler. cancel. }
    { apply cbuf_valid_pos. lia. }
    forward.
    assert (F0: i_flags (m_s m) = 0) by (apply ck_int_zero; [unfold srange in T15; rep_lia | assumption]).
    rewrite Hc. unfold update_check. rewrite F0, Z.eqb_refl. rewrite <- ck_da_cs_adler.
    entailer!. }
  forward. forward. forward.
  match goal with |- context [mem_rep_e_hl ?F0 (set_m_adler (upd_s m1 ?f) c)] =>
    change (mem_rep_e_hl F0 (set_m_adler (upd_s m1 f) c)) with (mem_rep_e_hl F0 m1) end.
  unfold upd_s, out_rep, out_ptr.
  cbn [m_s set_m_s set_m_adler set_i_check i_mode i_last i_wrap i_flags i_check i_total i_wsize i_hold i_bits
       m_tin m_tout m_snx m_sow m_inp m_aout m_msg m_adler m_ret m_ow].
  rewrite P1, P2, P3, P5, P6.
  subst ct.
  entailer!.
  unfold out_ok. split; [exact Hosh | ]. split; [exact Hop | ]. repeat split; auto; lia.
Qed.

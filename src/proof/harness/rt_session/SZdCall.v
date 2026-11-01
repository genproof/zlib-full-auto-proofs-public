(* Law rt_session, sessions with a dictionary and the zlib wrapper: the first inflate() call after
   inflateSetDictionary, any flush, any input (empty included).

   After Z_NEED_DICT and the right dictionary the state is DICT with havedict 1 and a window.  A call from it is
   the call from its TYPE version (RTIZDictDefs.d1_ty: check 1, adler 1), or it leaves at once (flush Z_BLOCK or
   Z_TREES, or no input) with Z_BUF_ERROR, nothing consumed or produced and the TYPE version as the state.  This
   is inflate_dict's ITD1.itd1_call stated on the state's fields instead of that law's invariant. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require compcert.lib.Integers.
Require Import Zlib.proof.roundtrip.RTIZDictDefs.
Require Import Zlib.proof.roundtrip.RTIZDictSet.
Require Zlib.proof.harness.inflate_dict.ITD1.
Import ListNotations.
Local Open Scope Z_scope.

Module D1 := Zlib.proof.harness.inflate_dict.ITD1.

Lemma szd_d1 flush z L inp res :
  i_mode (l_s L) = DICT -> i_havedict (l_s L) = 1 -> i_wsize (l_s L) <> 0 -> rtzs_wstruct (l_s L) ->
  i_win (l_s L) = true -> 0 <= i_total (l_s L) <= Integers.Int64.max_unsigned -> live_ok L -> zf_ok z ->
  run2 flush lenfix_list distfix_list (m_init z L inp) res ->
  run2 flush lenfix_list distfix_list (m_init (z_adl z 1) (set_l_s L (d1_ty (l_s L))) inp) res \/
  (r_ret res = Z_BUF_ERROR /\ m_snx (r_m res) = 0 /\ m_ow (r_m res) = [] /\ m_sow (r_m res) = 0 /\
   m_aout (r_m res) = zf_ao z /\ m_tout (r_m res) = zf_tout z /\ m_s (r_m res) = d1_ty (l_s L)).
Proof.
  intros MD HD Wne0 WS WI TT LV ZF [o [LP RS]].
  set (s := l_s L) in *.
  set (S := d1_ty s) in *.
  assert (SW: swf s) by apply LV.
  assert (Wne: i_wsize S <> 0) by exact Wne0.
  set (M2 := m_init (z_adl z 1) (set_l_s L S) inp).
  assert (E2: M2 = MS (set_i_mode S TYPEDO) (l_h L) inp (zf_ao z) 0 [] (i_hold s) (i_bits s) (Zlength inp)
                      (zf_ao z) Z_OK 0 1 (zf_msg z) (zf_tin z) (zf_tout z) 0 0) by reflexivity.
  assert (E0: m_init z L inp = MS s (l_h L) inp (zf_ao z) 0 [] (i_hold s) (i_bits s) (Zlength inp)
                      (zf_ao z) Z_OK 0 (zf_adler z) (zf_msg z) (zf_tin z) (zf_tout z) 0 0).
  { unfold m_init. cbv zeta. fold s. rewrite MD. reflexivity. }
  assert (St0: stepf2 flush lenfix_list distfix_list (m_init z L inp) =
               c_TYPE flush (set_mode M2 Zlib.proof.inflate.Model.TYPE)).
  { unfold stepf2. rewrite D1.itd1_step2_DICT by (rewrite E0; exact MD).
    rewrite E0. unfold c_DICT. cbn [m_s]. rewrite HD. reflexivity. }
  assert (St2: stepf2 flush lenfix_list distfix_list M2 = c_TYPEDO flush M2).
  { unfold stepf2. apply D1.itd1_step2_TYPEDO. reflexivity. }
  (* the leave case *)
  assert (LV2: stepf2 flush lenfix_list distfix_list (m_init z L inp) =
                 IBrk (set_leave (set_mode M2 Zlib.proof.inflate.Model.TYPE)) ->
               r_ret res = Z_BUF_ERROR /\ m_snx (r_m res) = 0 /\ m_ow (r_m res) = [] /\
               m_sow (r_m res) = 0 /\ m_aout (r_m res) = zf_ao z /\ m_tout (r_m res) = zf_tout z /\
               m_s (r_m res) = S).
  { intro St. inversion LP; subst.
    - congruence.
    - rewrite St in H. inversion H; subst m'. clear H.
      assert (EM: set_leave (set_mode M2 Zlib.proof.inflate.Model.TYPE) =
                  MS S (l_h L) inp (zf_ao z) 0 [] (i_hold S) (i_bits S) (Zlength inp) (zf_ao z) Z_OK 1 1
                     (zf_msg z) (zf_tin z) (zf_tout z) 0 0) by reflexivity.
      rewrite EM in RS. inversion RS; subst.
      + exfalso. match goal with Hw: i_win (m_s _) = false |- _ => cbn [m_s] in Hw end. unfold S, d1_ty in *.
        cbn in *. congruence.
      + destruct ZF as [_ [_ [ZT1 [ZT2 _]]]].
        destruct (D1.itd1_leave_fin flush S (l_h L) inp (zf_ao z) 1 (zf_msg z) (zf_tin z) (zf_tout z))
          as [dt Edt]; auto.
        rewrite Edt. cbn [r_ret r_m m_inp m_snx m_ow m_sow m_aout m_tout m_s]. auto 8.
    - rewrite St in H. inversion H; subst m'. exfalso. apply H0. reflexivity. }
  destruct (orb (flush =? Z_BLOCK) (flush =? Z_TREES)) eqn:FB.
  { right. apply LV2. rewrite St0. unfold c_TYPE. rewrite FB. reflexivity. }
  assert (St0': stepf2 flush lenfix_list distfix_list (m_init z L inp) =
                c_TYPEDO flush (set_mode M2 Zlib.proof.inflate.Model.TYPE)).
  { rewrite St0. unfold c_TYPE. rewrite FB. reflexivity. }
  destruct (Z.eq_dec (i_last (m_s M2)) 0) as [LZ|LZ];
    [destruct (Z.eq_dec (m_leave (needbits 3 M2)) 1) as [NL|NL]|].
  - right. apply LV2. rewrite St0'. unfold c_TYPEDO.
    change (i_last (m_s (set_mode M2 Zlib.proof.inflate.Model.TYPE))) with (i_last (m_s M2)). rewrite LZ.
    cbn [Z.eqb negb]. cbv zeta.
    assert (NL': m_leave (needbits 3 (set_mode M2 Zlib.proof.inflate.Model.TYPE)) = 1).
    { unfold needbits in *. rewrite D1.itd1_needbits_sm. exact NL. }
    rewrite D1.itd1_needbits_leave; [|reflexivity| |exact NL'].
    + reflexivity.
    + cbn [m_bits]. rewrite E2. cbn [m_bits]. apply SW.
  - left. exists o. split; [|exact RS].
    eapply D1.itd1_loop2_same; [|exact LP]. rewrite St0', St2. apply D1.itd1_typedo_sm. right; exact NL.
  - left. exists o. split; [|exact RS].
    eapply D1.itd1_loop2_same; [|exact LP]. rewrite St0', St2. apply D1.itd1_typedo_sm. left; exact LZ.
Qed.

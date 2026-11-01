(* case LEN (LnKit5.v): the sub-table lookup loop over lencode (ln_loop2_stmt) *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate.LnKit5.
Require Import Zlib.proof.inflate.NeedBits.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Lemma ln2_int_and_ones: forall b k, 0 <= b -> 0 <= k <= 32 ->
  Int.and (Int.repr b) (Int.repr (2 ^ k - 1)) = Int.repr (b mod 2 ^ k).
Proof.
  intros b k Hb Hk. unfold Int.and.
  rewrite (Int.unsigned_repr_eq b).
  rewrite (Int.unsigned_repr (2 ^ k - 1)).
  - f_equal. replace (2 ^ k - 1) with (Z.ones k) by (rewrite Z.ones_equiv; lia). rewrite Z.land_ones by lia.
    change Int.modulus with (2 ^ 32). symmetry. apply Znumtheory.Zmod_div_mod.
    + apply Z.pow_pos_nonneg; lia.
    + lia.
    + exists (2 ^ (32 - k)). rewrite <- Z.pow_add_r by lia. f_equal. lia.
  - split; [ | change Int.max_unsigned with (2 ^ 32 - 1)].
    + assert (0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia). lia.
    + assert (2 ^ k <= 2 ^ 32) by (apply Z.pow_le_mono_r; lia). lia.
Qed.

Lemma ln2_u32_repr: forall x, Int.repr (u32 x) = Int.repr x.
Proof.
  intros. unfold u32. apply Int.eqm_samerepr. unfold Int.eqm. apply Zbits.eqmod_sym, Zbits.eqmod_mod.
  reflexivity.
Qed.

Lemma ln2_mask: forall n, 0 <= n < 32 ->
  Int.sub (Int.shl (Int.repr 1) (Int.repr n)) (Int.repr 1) = Int.repr (2 ^ n - 1).
Proof.
  intros n Hn. rewrite Int.shl_mul_two_p. rewrite (Int.unsigned_repr n) by rep_lia.
  rewrite two_p_equiv. rewrite Int.mul_commut, Int.mul_one. rewrite sub_repr. reflexivity.
Qed.

Lemma ln2_index: forall h n, 0 <= n <= 15 ->
  Int.and (Int.repr (Int64.Z_mod_modulus h)) (Int.sub (Int.shl (Int.repr 1) (Int.repr n)) (Int.repr 1)) =
  Int.repr (h mod 2 ^ n).
Proof.
  intros h n Hn. rewrite ln2_mask by lia. rewrite Int64.Z_mod_modulus_eq.
  assert (M: 0 < Int64.modulus) by reflexivity.
  rewrite ln2_int_and_ones by (try apply Z.mod_pos_bound; lia). f_equal.
  symmetry. apply Znumtheory.Zmod_div_mod.
  - apply Z.pow_pos_nonneg; lia.
  - exact M.
  - exists (2 ^ (64 - n)). change Int64.modulus with (2 ^ 64). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

Lemma ln2_index2: forall h b o v, 0 <= b -> 0 <= o -> b + o <= 15 -> 0 <= v <= 65535 ->
  Int.add (Int.repr v) (Int.shru (Int.and (Int.repr (Int64.Z_mod_modulus h))
      (Int.sub (Int.shl (Int.repr 1) (Int.repr (b + o))) (Int.repr 1))) (Int.repr b)) =
  Int.repr (v + Z.shiftr (h mod 2 ^ (b + o)) b).
Proof.
  intros h b o v Hb Ho Hbo Hv. rewrite ln2_index by lia.
  assert (R: 0 <= h mod 2 ^ (b + o) < 2 ^ (b + o)) by (apply Z.mod_pos_bound, Z.pow_pos_nonneg; lia).
  assert (P: 2 ^ (b + o) <= 2 ^ 15) by (apply Z.pow_le_mono_r; lia).
  unfold Int.shru. rewrite (Int.unsigned_repr (h mod 2 ^ (b + o))) by rep_lia.
  rewrite (Int.unsigned_repr b) by rep_lia. rewrite add_repr. reflexivity.
Qed.

Lemma ln2_pull_fields: forall m,
  m_nx (pull m) = m_nx m + 1 /\ m_have (pull m) = m_have m - 1 /\
  m_hold (pull m) = u64 (m_hold m + Znth (m_nx m) (m_inp m) * 2 ^ m_bits m) /\
  m_bits (pull m) = u32 (m_bits m + 8) /\ m_left (pull m) = m_left m /\ m_ow (pull m) = m_ow m /\
  m_in (pull m) = m_in m /\ m_out (pull m) = m_out m /\ m_ret (pull m) = m_ret m /\ m_leave (pull m) = m_leave m.
Proof. intros. unfold m_have. repeat split; try reflexivity. simpl. lia. Qed.

Lemma ln2_lookup2_S: forall k fx dx t last m,
  lookup2_f (S k) fx dx t last m =
  let here := tab_entry fx dx (m_s m) t (e_val last + Z.shiftr (bitsn m (e_bits last + e_op last)) (e_bits last)) in
  if e_bits last + e_bits here <=? m_bits m then (here, m, true)
  else if m_have m =? 0 then (here, set_leave m, false)
  else lookup2_f k fx dx t last (pull m).
Proof. reflexivity. Qed.

Lemma ln2_mem_rep_leave: forall F m, mem_rep F (set_leave m) = mem_rep F m.
Proof. reflexivity. Qed.

Lemma ln2_readable: forall F t, frame_ok5 F -> readable_share (tab_sh F t).
Proof.
  intros F t [(_ & _ & G & _) _]. destruct t; simpl; auto; apply writable_readable_share, writable_Ews.
Qed.

Lemma ln_loop2_ok : ln_tab_stmt -> ln_loop2_stmt.
Proof.
  intros [TE [TL TV]]. unfold ln_loop2_stmt. intros Espec F m last hv sz HF W HM HL Hsz Hsub Hlok Hlb.
  cbv beta iota zeta delta [ln_loop2 ln_l1 ln_link ln_lif ln_s3 ln_s2 ln_s1 ln_slow ln_body case_body inflate_LS find_switch f_inflate fn_body ls_drop].
  pose proof (sw_lencode _ (mw_s _ W)) as Ht.
  destruct (sw_codes _ (mw_s _ W)) as [Hcl _].
  pose proof (ln2_readable F (i_lencode (m_s m)) HF) as Hrd.
  unfold ls_hl.
  replace_SEP 0 (ln_view F m * (ln_view F m -* mem_rep F m)).
  { apply andp_left2. unfold PROPx, LOCALx. apply andp_left2. apply andp_left2. unfold SEPx.
    intro rho; cbn [fold_right_sepcon]. rewrite sepcon_emp. apply TV; auto. }
  remember (ln_view F m -* mem_rep F m) as WD eqn:HWD.
  unfold ln_view at 1, tab_arr. Intros.
  set (t := i_lencode (m_s m)) in *.
  set (lb := i_lenbits (m_s m)) in *.
  set (s := m_s m) in *.
  set (tl := tab_list s t) in *.
  remember (tab_sh F t) as tsh' eqn:Htsh.
  remember (tref_val (f_gv F) (f_sp F) t) as tp eqn:Htp.
  destruct F as [gv shs strmp sp headp winp hsh xb nb cb ib ob gsh tsh dt vres vhere vlast vhbuf flush].
  unfold ln_locals. cbn [f_gv f_shs f_strmp f_sp f_headp f_winp f_hsh f_xb f_nb f_cb f_ib f_ob f_gsh f_tsh f_dt f_vres f_vhere f_vlast f_vhbuf f_flush] in *.
  destruct Hsub as (Hlb' & Ho1 & Ho15 & Hsubj).
  destruct Hlok as (Hlo & Hlbr & Hlvr).
  set (lo := e_op last) in *. set (lbb := e_bits last) in *. set (lv := e_val last) in *.
  assert (Hent: forall j, 0 <= j < 2 ^ lo ->
            tab_entry lenfix_list distfix_list s t (lv + j) = Znth (lv + j) tl /\
            entry_ok (Znth (lv + j) tl) /\ lbb + e_bits (Znth (lv + j) tl) <= 15 /\ 0 <= lv + j < sz).
  { intros j Hj. specialize (Hsubj j Hj). cbv zeta in Hsubj.
    destruct Hsubj as (Hr & Hok & _ & Hb & _).
    assert (E: tab_entry lenfix_list distfix_list s t (lv + j) = Znth (lv + j) tl) by (apply TE; auto; lia).
    rewrite E in Hok, Hb. rewrite <- Hlb' in Hb. auto. }
  clear Hsubj.
  assert (HTL: Zlength tl = tab_size t) by (apply TL; auto).
  assert (Hts: tab_size t <= 4096) by (clear - Ht; clearbody t; destruct t; simpl in *; unfold ENOUGH_CODES in *; lia).
  pose proof (mw_bits _ W) as WB. pose proof (mw_nx _ W) as WNX. pose proof (mw_inp _ W) as WINP.
  set (F0 := Fr gv shs strmp sp headp winp hsh xb nb cb ib ob gsh tsh dt vres vhere vlast vhbuf flush) in *.
  Ltac ln2_proj := match goal with X := Fr ?gv _ ?strmp ?sp _ _ _ _ _ _ ?ib ?ob _ _ _ _ ?vh ?vl ?vb ?fl |- _ =>
    change (f_gv X) with gv; change (f_strmp X) with strmp; change (f_sp X) with sp; change (f_ib X) with ib;
    change (f_ob X) with ob; change (f_flush X) with fl; change (f_vhere X) with vh; change (f_vlast X) with vl;
    change (f_vhbuf X) with vb end.
  change (ent last) with (Vint (Int.repr lo), (Vint (Int.repr lbb), Vint (Int.repr lv))).
  forward_loop (@exp (environ -> mpred) _ nat (fun k => @exp (environ -> mpred) _ (reptype t_code) (fun hv' =>
     PROPx [lookup2_f (3 - k) lenfix_list distfix_list t last (pullk k m) = lookup2 lenfix_list distfix_list t last m;
           m_bits (pullk k m) = (m_bits m + 8 * Z.of_nat k)%Z;
           (0 < k)%nat -> (m_bits m + 8 * (Z.of_nat k - 1) < 15)%Z;
           (m_nx m + Z.of_nat k <= Zlength (m_inp m))%Z]
     (LOCALx (ln_locals F0 (pullk k m))
     (SEPx [field_at Ews t_state (DOT _lencode) tp sp;
            field_at Ews t_state (DOT _lenbits) (Vint (Int.repr lb)) sp;
            data_at tsh' (tarray t_code (tab_size t)) (map ent tl) tp;
            in_rep ib; WD; data_at Tsh t_code hv' vhere;
            data_at Tsh t_code (Vint (Int.repr lo), (Vint (Int.repr lbb), Vint (Int.repr lv))) vlast;
            data_at_ Tsh (tarray tuchar 4) vhbuf])))))
    break: (@exp (environ -> mpred) _ entry (fun here => @exp (environ -> mpred) _ mst (fun m1 =>
       @exp (environ -> mpred) _ bool (fun ok =>
     PROPx [lookup2 lenfix_list distfix_list t last m = (here, m1, ok);
            mem_rep F0 m1 = mem_rep F0 m; m_inp m1 = m_inp m; m_aout m1 = m_aout m]
     (LOCALx (ln_locals F0 m1)
     (SEPx [field_at Ews t_state (DOT _lencode) tp sp;
            field_at Ews t_state (DOT _lenbits) (Vint (Int.repr lb)) sp;
            data_at tsh' (tarray t_code (tab_size t)) (map ent tl) tp;
            in_rep ib; WD; data_at Tsh t_code (ent here) vhere;
            data_at Tsh t_code (Vint (Int.repr lo), (Vint (Int.repr lbb), Vint (Int.repr lv))) vlast;
            data_at_ Tsh (tarray tuchar 4) vhbuf])))))).
  - Exists 0%nat hv. unfold ln_locals. simpl pullk. ln2_proj. entailer!.
  - Intros k hv'.
    destruct (pullk_fields k m) as (P1&P2&P3&P4&P5&P6&P7&P8&P9&P10).
    unfold ln_locals. ln2_proj.
    assert (Hk: (k <= 2)%nat).
    { destruct (Nat.eq_dec k 0); [lia|].
      match goal with Hx: (0 < k)%nat -> _ |- _ => specialize (Hx ltac:(lia)) end. lia. }
    assert (Hmr: mem_rep F0 (pullk k m) = mem_rep F0 m) by apply mem_rep_pullk.
    set (mk := pullk k m) in *.
    assert (Emk: pullk k m = mk) by reflexivity. clearbody mk.
    pose proof (sub_index_range (m_hold mk) lbb lo ltac:(lia) ltac:(lia)) as Hix.
    assert (Ulv: Int.unsigned (Int.repr lv) = lv) by (apply Int.unsigned_repr; rep_lia).
    assert (Ulo: Int.unsigned (Int.repr lo) = lo) by (apply Int.unsigned_repr; rep_lia).
    assert (Ulb: Int.unsigned (Int.repr lbb) = lbb) by (apply Int.unsigned_repr; rep_lia).
    Ltac ln2_ld U1 U2 U3 := forward; lazymatch goal with |- ENTAIL _, _ |-- _ =>
      go_lower; apply prop_right; simpl; rewrite ?U1, ?U2, ?U3; lia | _ => idtac end.
    set (j := Z.shiftr (m_hold mk mod 2 ^ (lbb + lo)) lbb) in *.
    assert (HI: Int.add (Int.repr lv) (Int.shru (Int.and (Int.repr (Int64.Z_mod_modulus (m_hold mk)))
                  (Int.sub (Int.shl (Int.repr 1) (Int.repr (lbb + lo))) (Int.repr 1))) (Int.repr lbb)) =
                Int.repr (lv + j)) by (apply ln2_index2; lia).
    destruct (Hent _ Hix) as (Etab & Heok & Heb & Hr).
    assert (HU: Int.unsigned (Int.repr (lv + j)) = lv + j) by (apply Int.unsigned_repr; rep_lia).
    set (e := Znth (lv + j) tl) in *.
    destruct Heok as (Heo & Heb2 & Hev).
    assert (Hit: lv + j < tab_size t) by lia.
    Ltac ln2_rd HI HU e :=
      forward; [ apply prop_right; rewrite HI, HU; lia
               | rewrite HI, HU, Znth_map by lia; fold e; unfold ent at 1; cbv beta iota; entailer!; rep_lia
               | entailer!; change (Int.unsigned Int.iwordsize) with 32; lia
               | rewrite HI, HU, Znth_map by lia; fold e; unfold ent at 1; cbv beta iota ].
    forward. ln2_ld Ulv Ulo Ulb. ln2_ld Ulv Ulo Ulb. ln2_ld Ulv Ulo Ulb. ln2_ld Ulv Ulo Ulb. ln2_rd HI HU e. forward.
    forward. ln2_ld Ulv Ulo Ulb. ln2_ld Ulv Ulo Ulb. ln2_ld Ulv Ulo Ulb. ln2_ld Ulv Ulo Ulb. ln2_rd HI HU e. forward.
    forward. ln2_ld Ulv Ulo Ulb. ln2_ld Ulv Ulo Ulb. ln2_ld Ulv Ulo Ulb. ln2_ld Ulv Ulo Ulb. ln2_rd HI HU e. forward.
    assert (Z1: Int.zero_ext 8 (Int.repr (e_op e)) = Int.repr (e_op e))
      by (apply zero_ext_inrange; rewrite Int.unsigned_repr by rep_lia; simpl; lia).
    assert (Z2: Int.zero_ext 8 (Int.repr (e_bits e)) = Int.repr (e_bits e))
      by (apply zero_ext_inrange; rewrite Int.unsigned_repr by rep_lia; simpl; lia).
    assert (Z3: Int.zero_ext 16 (Int.repr (e_val e)) = Int.repr (e_val e))
      by (apply zero_ext_inrange; rewrite Int.unsigned_repr by rep_lia; simpl; lia).
    rewrite Z1, Z2, Z3.
    assert (Etab': tab_entry lenfix_list distfix_list (m_s mk) t (lv + j) = e)
      by (rewrite P1; exact Etab).
    ln2_ld Ulv Ulo Ulb.
    forward.
    assert (Eix: e_val last + Z.shiftr (bitsn mk (e_bits last + e_op last)) (e_bits last) = lv + j) by reflexivity.
    forward_if.
    + forward.
      assert (EL: lookup2 lenfix_list distfix_list t last m = (e, mk, true)).
      { rewrite <- H1. replace (3 - k)%nat with (S (2 - k)) by lia. rewrite ln2_lookup2_S. cbv zeta.
        rewrite Eix, Etab'. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity. }
      Exists e mk true.
      unfold ln_locals; ln2_proj.
      change (ent e) with (Vint (Int.repr (e_op e)), (Vint (Int.repr (e_bits e)), Vint (Int.repr (e_val e)))).
      go_lower. apply andp_right; [apply prop_right | apply derives_refl].
      split; [exact EL|]. split; [exact Hmr|]. split; [exact P3|]. split; [exact P4|]. repeat split.
    + assert (HH: 0 <= m_have mk <= Int.max_signed) by (unfold m_have; rewrite P3, P10; lia).
      forward_if.
      * forward. forward.
        match goal with Hx: m_have mk = 0 |- _ => rename Hx into Hh0 end.
        assert (EL: lookup2 lenfix_list distfix_list t last m = (e, set_leave mk, false)).
        { rewrite <- H1. replace (3 - k)%nat with (S (2 - k)) by lia. rewrite ln2_lookup2_S. cbv zeta.
          rewrite Eix, Etab'. rewrite (proj2 (Z.leb_gt _ _)) by lia. rewrite Hh0. reflexivity. }
        Exists e (set_leave mk) false.
        unfold ln_locals; ln2_proj.
        change (ent e) with (Vint (Int.repr (e_op e)), (Vint (Int.repr (e_bits e)), Vint (Int.repr (e_val e)))).
        go_lower. apply andp_right; [apply prop_right | apply derives_refl].
        split; [exact EL|]. split; [rewrite ln2_mem_rep_leave; exact Hmr|]. split; [exact P3|]. split; [exact P4|].
        repeat split.
      * match goal with Hx: m_have mk <> 0 |- _ => rename Hx into Hh0 end.
        forward.
        destruct ib as [ | ish ip ilo inb ic].
        { exfalso. unfold in_ok in H. unfold m_have in Hh0. rewrite P3, P10, H in Hh0.
          rewrite H in H4. rewrite Zlength_nil in *. lia. }
        assert (Hj: 0 <= m_nx mk < Zlength (m_inp m)).
        { unfold m_have in Hh0, HH. rewrite P3 in Hh0, HH. rewrite P10. lia. }
        pose proof (in_byte _ _ _ _ _ _ (m_nx mk) H Hj) as HBYTE.
        pose proof H as HINOK.
        destruct H as (Hish & Hip & Hilo & Hinb & Hic & Hinbm & Hsub & Hbytes).
        pose proof (bytes_ok_Znth _ _ Hbytes Hj) as HBR.
        change (in_rep (InBuf ish ip ilo inb ic)) with (data_at ish (tarray tuchar inb) ic ip).
        change (in_ptr (InBuf ish ip ilo inb ic) (m_nx mk)) with (offset_val (ilo + m_nx mk) ip).
        forward.
        forward.
        assert_PROP (field_compatible (tarray tuchar inb) [] ip) by entailer!.
        rewrite (offset_val_field_address_tuchar inb (ilo + m_nx mk) ip) by (auto; lia).
        forward.
        { rewrite HBYTE. go_lower. apply prop_right. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
        rewrite HBYTE.
        forward.
        { go_lower. apply prop_right. change (Int.unsigned Int64.iwordsize') with 64.
          rewrite Int.unsigned_repr by rep_lia. lia. }
        forward.
        assert (Epull: pullk (S k) m = pull mk) by (rewrite pullk_S, Emk; reflexivity).
        destruct (ln2_pull_fields mk) as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10).
        assert (F1: lookup2_f (3 - S k) lenfix_list distfix_list t last (pull mk) =
                    lookup2 lenfix_list distfix_list t last m).
        { rewrite <- H1. replace (3 - k)%nat with (S (2 - k)) by lia. rewrite ln2_lookup2_S. cbv zeta.
          rewrite Eix, Etab'. rewrite (proj2 (Z.leb_gt _ _)) by lia. rewrite (proj2 (Z.eqb_neq _ _)) by exact Hh0.
          replace (3 - S k)%nat with (2 - k)%nat by lia. reflexivity. }
        assert (F2: m_bits (pull mk) = m_bits m + 8 * Z.of_nat (S k)).
        { rewrite R4. unfold u32. rewrite Z.mod_small by lia. rewrite Nat2Z.inj_succ. lia. }
        assert (F3: (0 < S k)%nat -> m_bits m + 8 * (Z.of_nat (S k) - 1) < 15).
        { intros _. rewrite Nat2Z.inj_succ. lia. }
        assert (F4: m_nx m + Z.of_nat (S k) <= Zlength (m_inp m)) by (rewrite Nat2Z.inj_succ; lia).
        Exists (S k) (ent e).
        rewrite Epull.
        unfold ln_locals; ln2_proj.
        change (in_ptr (InBuf ish ip ilo inb ic) (m_nx (pull mk))) with (offset_val (ilo + m_nx (pull mk)) ip).
        change (in_rep (InBuf ish ip ilo inb ic)) with (data_at ish (tarray tuchar inb) ic ip).
        rewrite R1, R2, R3, R4, R5, R6, R7, R8, R9, R10.
        change (ent e) with (Vint (Int.repr (e_op e)), (Vint (Int.repr (e_bits e)), Vint (Int.repr (e_val e)))).
        go_lower.
        apply andp_right; [apply prop_right | cancel].
        split; [exact F1|]. split; [exact F2|]. split; [exact F3|]. split; [exact F4|].
        repeat split.
        all: try (f_equal; rewrite sub_repr; reflexivity).
        all: try (rewrite ln2_u32_repr, add_repr; reflexivity).
        { rewrite <- (offset_val_field_address_tuchar inb (ilo + m_nx mk) ip) by (auto; lia).
          destruct ip; try contradiction; simpl.
          rewrite Ptrofs.add_assoc. f_equal.
          change (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_ints (Int.repr 1))) with (Ptrofs.repr 1).
          rewrite ptrofs_add_repr. f_equal. f_equal. lia. }
        { rewrite P3. rewrite (Int.unsigned_repr (Znth (m_nx mk) (m_inp m))) by rep_lia.
          rewrite (Int.unsigned_repr (m_bits mk)) by rep_lia. f_equal. apply hold_add_eq; lia. }
  - clear Hent.
    assert (Hclose: field_at Ews t_state (DOT _lencode) tp sp *
                    field_at Ews t_state (DOT _lenbits) (Vint (Int.repr lb)) sp *
                    data_at tsh' (tarray t_code (tab_size t)) (map ent tl) tp * in_rep ib * WD |-- mem_rep F0 m).
    { subst WD. eapply derives_trans; [|apply modus_ponens_wand]. apply sepcon_derives; [|apply derives_refl].
      unfold ln_view, tab_arr. subst tp tsh'. apply derives_refl. }
    Intros here m1 ok.
    Exists here m1 ok.
    unfold ln_locals; ln2_proj.
    match goal with Hx: mem_rep F0 m1 = mem_rep F0 m, Hi: m_inp m1 = m_inp m, Ha: m_aout m1 = m_aout m |- _ =>
      rewrite Hx, Hi, Ha end.
    go_lower.
    apply andp_right; [apply prop_right; assumption | ].
    apply andp_right; [apply prop_right; split; [assumption|]; split; [assumption|]; repeat split | ].
    sep_apply Hclose. cancel.
Qed.

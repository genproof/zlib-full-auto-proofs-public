(** * deflateSetDictionary without the size limits of the deflate laws

    [W3_dict_w] is LTCore.W3_dict (interface LTIface.cf_dict) for what the C types allow: a dictionary of up to
    2^32 - 1 bytes (deflateSetDictionary keeps its last w_size bytes when it is longer; the Adler-32 is of the
    whole dictionary) and any total_in (fill_window adds the bytes it reads to total_in modulo 2^64).  It is the
    field [cw_dict] of LTWIface.core_facts_w for LTCore's invariant [W3]. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTWIface.
Require Import Zlib.proof.deflate.LTCore.
Require Import Zlib.proof.deflate.LTCLib Zlib.proof.deflate.LTCMisc Zlib.proof.deflate.LTCFill.
Require Import Zlib.proof.deflate.LTCDictKit Zlib.proof.deflate.LTCDictFrame Zlib.proof.deflate.LTCDictIns.
Require Import Zlib.proof.deflate.LTCDictProj Zlib.proof.deflate.LTCDict.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** Any dictionary length

    LTCDict3.dict_ok3 for a dictionary of any length: only its last [min (Zlength d) w_size] bytes are fed to
    fill_window, so the proof of dict_ok3 never uses the bound on [Zlength d]; it is that proof without it. *)
Lemma dict_ok3_any : fill_spec ->
  forall s z d,
    W s -> bad_state s = false -> (d_wrap s = 1 -> d_status s = INIT_STATE) -> 0 <= d_wrap s <= 1 ->
    d_strstart s = 0 -> d_lookahead s = 0 -> d_block_start s = 0 -> d_sym_next s = 0 ->
    bytes d -> 0 <= z_total_in z <= 1099511627776 -> adler_pre (d_wrap s) (z_adler z) ->
    exists s' z' k,
      c_deflateSetDictionary s z (Some d) = Some (s', z', Z_OK) /\ W s' /\
      api_eq s s' /\ out_eq s s' /\ same_prm s s' /\
      d_lookahead s' = 0 /\ d_strstart s' = d_block_start s' /\ (d_strstart s' = 0 <-> d = []) /\
      d_sym_next s' = 0 /\ 0 <= k <= Zlength d /\
      z' = mkST (z_in z) (z_next_in z) (z_avail_in z) (z_total_in z + k) (z_out z) (z_avail_out z)
                (z_total_out z)
                (if d_wrap s =? 1 then Zlib.proof.adler32.Model.ref_adler32 (z_adler z) d else z_adler z)
                (z_msg z).
Proof.
  intros Hfill s z d HW Hbad Hst Hwrap Hss Hla Hbs Hsn Hbytes Htot Hadl.
  pose proof HW as (Hprm & Hws & Hwp & Hww & Hwh & Hwm & Hl0 & syms & Hwt).
  assert (Ec : (d_wrap s =? 2) || ((d_wrap s =? 1) && negb (d_status s =? INIT_STATE)) || negb (d_lookahead s =? 0)
               = false).
  { rewrite Hla. destruct (Z.eqb_spec (d_wrap s) 1) as [E|E].
    - rewrite (Hst E), E. reflexivity.
    - rewrite (proj2 (Z.eqb_neq (d_wrap s) 2)) by lia. reflexivity. }
  unfold c_deflateSetDictionary.
  rewrite Hbad. cbv zeta. rewrite Ec.
  cbv beta iota zeta.
  set (z1 := if d_wrap s =? 1 then set_z_adler z (Zlib.proof.adler32.Model.adler32_z_val (z_adler z) d) else z).
  set (a1 := if d_wrap s =? 1 then Zlib.proof.adler32.Model.ref_adler32 (z_adler z) d else z_adler z).
  assert (Ez1 : z1 = mkST (z_in z) (z_next_in z) (z_avail_in z) (z_total_in z) (z_out z) (z_avail_out z)
                          (z_total_out z) a1 (z_msg z)).
  { subst z1 a1. destruct (Z.eqb_spec (d_wrap s) 1) as [E|E].
    - rewrite Zlib.proof.adler32.Model.adler32_z_val_ref by (apply Hadl; exact E). destruct z; reflexivity.
    - destruct z; reflexivity. }
  rewrite Ez1. cbn [z_in z_next_in z_avail_in z_total_in z_out z_avail_out z_total_out z_adler z_msg].
  clear Ez1 z1.
  (* common facts *)
  pose proof Hprm as (Pwb & Pws & Pwm & Phb & Phs & Phm & Psh & _).
  assert (Hw512 : 512 <= d_w_size s <= 32768).
  { rewrite Pws. split.
    - change 512 with (2 ^ 9). apply Z.pow_le_mono_r; lia.
    - change 32768 with (2 ^ 15). apply Z.pow_le_mono_r; lia. }
  assert (Hh256 : 256 <= d_hash_size s <= 65536).
  { rewrite Phs. split.
    - change 256 with (2 ^ 8). apply Z.pow_le_mono_r; lia.
    - change 65536 with (2 ^ 16). apply Z.pow_le_mono_r; lia. }
  pose proof Hwp as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
  pose proof Hws as (V1 & V2 & V3 & V4 & V5).
  assert (Hins : d_insert s = 0) by lia.
  match goal with |- exists _ _ _, bind ?e _ = _ /\ _ =>
    assert (Hbr : exists s2 off len, e = Some (s2, off, len) /\
      prm s2 /\ wstruct s2 /\ wpos s2 /\ wwin s2 /\ d_insert s2 = 0 /\ d_block_start s2 = 0 /\
      d_wrap s2 = 0 /\ d_strstart s2 = 0 /\ d_lookahead s2 = 0 /\ fw_keep s2 = fw_keep (set_d_wrap s 0) /\
      d_prev s2 = d_prev s /\
      (d_head s2 = d_head s \/ d_head s2 = repeat 0 (Z.to_nat (d_hash_size s))) /\
      len = Z.min (Zlength d) (d_w_size s) /\ off = Zlength d - len) end.
  { autorewrite with dproj.
    assert (Hpre : forall s2, d_prev s2 = d_prev s -> d_head s2 = d_head s \/
                     d_head s2 = repeat 0 (Z.to_nat (d_hash_size s)) ->
                   fw_keep s2 = fw_keep (set_d_wrap s 0) -> d_insert s2 = 0 -> d_block_start s2 = 0 ->
                   d_wrap s2 = 0 -> d_strstart s2 = 0 -> d_lookahead s2 = 0 -> d_high_water s2 = d_high_water s ->
                   d_window s2 = d_window s ->
                   prm s2 /\ wstruct s2 /\ wpos s2 /\ wwin s2).
    { intros s2 E1 E2 E3 E4 E5 E6 E7 E8 E9 E10.
      assert (Ew : d_w_size s2 = d_w_size s) by exact (f_equal d_w_size E3).
      assert (Eh : d_hash_size s2 = d_hash_size s) by exact (f_equal d_hash_size E3).
      assert (Ews : d_window_size s2 = d_window_size s) by exact (f_equal d_window_size E3).
      split.
      { exact (prm_keep _ _ E3 Hprm). }
      split.
      { unfold wstruct. rewrite E10, Ew, Ews, E1, Eh. split; [exact V1|]. split; [exact V2|].
        split; [exact V3|]. split; [exact V4|]. destruct E2 as [E2|E2]; rewrite E2; [exact V5|].
        apply Zlength_repeat; lia. }
      split.
      { unfold wpos. rewrite E4, E5, E7, E8, E9, Ews, Ew. unfold MAX_DIST. lia. }
      { pose proof Hww as Hww2. unfold wwin in *. rewrite E7, E8, E9, E10. rewrite Hss, Hla in Hww2. exact Hww2. } }
    destruct (Z.geb_spec (Zlength d) (d_w_size s)) as [Hge|Hlt].
    - destruct (Z.eqb_spec (d_wrap s) 0) as [Ew0|Ew0].
      + rewrite clear_hash_ok by (autorewrite with dproj; lia). rewrite !bind_Some.
        eexists _, _, _. split; [reflexivity|].
        br_fin Hpre.
      + rewrite !bind_Some. eexists _, _, _. split; [reflexivity|]. br_fin Hpre.
    - eexists _, _, _. split; [reflexivity|]. br_fin Hpre. }
  destruct Hbr as (s2 & off & len & Ebr & B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12 & B13 & B14).
  rewrite Ebr, bind_Some. cbv beta iota.
  set (zd2 := mkST d off len (z_total_in z) (z_out z) (z_avail_out z) (z_total_out z) a1 (z_msg z)).
  assert (Hz2 : zin_in zd2).
  { unfold zin_in; subst zd2; cbn [z_in z_next_in z_avail_in z_total_in]. split; [exact Hbytes|].
    pose proof (Zlength_nonneg d). lia. }
  assert (Ew2 : d_w_size s2 = d_w_size s) by exact (f_equal d_w_size B10).
  destruct (fill_step Hfill s2 zd2 B1 B2 B3 B4 B5 B7 ltac:(subst zd2; cbn [z_avail_in]; lia) Hz2
              ltac:(subst zd2; cbn [z_avail_in z_total_in]; lia)) as
    (s3 & k1 & Ef1 & R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13).
  rewrite Ef1, bind_Some. cbv beta iota.
  change (mkST (z_in zd2) (z_next_in zd2 + k1) (z_avail_in zd2 - k1) (z_total_in zd2 + k1) (z_out zd2)
            (z_avail_out zd2) (z_total_out zd2) (z_adler zd2) (z_msg zd2)) with (zadv zd2 k1).
  assert (HJ : Jl s2 zd2 (chains 0 (d_head s2) (d_prev s2)) (heads_le (d_w_size s2) (d_head s2)) (s3, zadv zd2 k1)).
  { unfold Jl. rewrite R9, R11, B8, B9.
    split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R5|].
    split; [rewrite R10; exact B6|]. split; [rewrite (f_equal d_wrap R6 : d_wrap s3 = _); exact B7|].
    split; [exact R6|]. split; [lia|]. split; [f_equal; lia|].
    split; [intros Hl; destruct R13; lia|].
    split; [intros C; rewrite R7, R8; exact C|].
    intros C; rewrite R7, (f_equal d_w_size R6 : d_w_size s3 = _); exact C. }
  destruct (sd_loop Hfill s2 zd2 _ _ Hz2 ltac:(subst zd2; cbn [z_avail_in]; lia)
              ltac:(subst zd2; cbn [z_avail_in z_total_in]; lia) _ HJ) as ([sF zdF] & Eloop & JF & HlaF).
  rewrite Eloop, bind_Some. cbv beta iota.
  destruct JF as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13).
  subst zdF. cbn [fst] in HlaF.
  pose proof F3 as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9).
  assert (Hn : d_strstart sF + d_lookahead sF = len).
  { unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in *. subst zd2. cbn [z_avail_in] in F9, F11.
    specialize (F11 ltac:(lia)). lia. }
  assert (Hu : u32 (d_strstart sF + d_lookahead sF) = d_strstart sF + d_lookahead sF).
  { unfold u32. apply Z.mod_small. lia. }
  rewrite Hu.
  assert (Ek : fw_keep sF = fw_keep (set_d_wrap s 0)) by (rewrite F8; exact B10).
  assert (K1 : d_tr sF = d_tr s) by exact (f_equal d_tr Ek).
  assert (K2 : d_pbm sF = d_pbm s) by exact (f_equal d_pbm Ek).
  assert (K3 : d_w_size sF = d_w_size s) by exact (f_equal d_w_size Ek).
  assert (K4 : d_hash_size sF = d_hash_size s) by exact (f_equal d_hash_size Ek).
  eexists _, _, len. split; [reflexivity|].
  match goal with |- W ?x /\ _ => set (sf := x) end.
  assert (Hlv : d_level sf = d_level s) by (subst sf; autorewrite with dproj; unfold d_level; rewrite K1; reflexivity).
  assert (Hsyms : syms = []).
  { destruct Hwt as ((_ & _ & T3 & _) & _). unfold d_sym_next in Hsn. rewrite Hsn in T3.
    apply Zlength_nil_inv. lia. }
  subst syms.
  split.
  { split; [subst sf; exact F1|]. split; [subst sf; exact F2|].
    split.
    { subst sf. unfold wpos. autorewrite with dproj. unfold MAX_DIST. lia. }
    split.
    { subst sf. unfold wwin in *. autorewrite with dproj. rewrite Z.add_0_r. exact F4. }
    split.
    { (* whash *)
      assert (Hc1 : chain_ok s -> chains 0 (d_head s2) (d_prev s2)).
      { intros Hch. destruct B12 as [E|E]; rewrite E.
        - apply chains_of_chain_ok; [exact Hch|exact Hss|exact V5].
        - split; [|intros; lia]. intros i Hi. left. rewrite Znth_repeat'; [reflexivity|].
          rewrite Zlength_repeat in Hi by lia. rewrite Z2Nat.id by lia. lia. }
      assert (Hc1F : chain_ok s -> chain_ok sf).
      { intros Hch. specialize (F12 (Hc1 Hch)).
        destruct F2 as (_ & _ & _ & _ & L5). destruct F1 as (Fwb & Fws & Fwm & _).
        subst sf. apply (chain_ok_of_chains _ (d_strstart sF)); autorewrite with dproj; try lia; auto. }
      assert (Hc2F : chain_ok (slide_hc s) -> chain_ok (slide_hc sf)).
      { intros Hch. assert (Hle : heads_le (d_w_size s2) (d_head s2)).
        { rewrite Ew2. destruct B12 as [E|E]; rewrite E.
          - apply heads_le_of_slide; [exact Hch|exact Hss|exact V5].
          - intros i Hi. rewrite Znth_repeat'; [lia|]. rewrite Zlength_repeat in Hi by lia. lia. }
        specialize (F13 Hle). destruct F2 as (_ & _ & _ & _ & L5).
        subst sf. apply slide_chain_ok; autorewrite with dproj; assumption. }
      assert (Hm : d_matches sf = d_matches s) by (subst sf; autorewrite with dproj; unfold d_matches; rewrite K1; reflexivity).
      unfold whash in *. rewrite Hlv, Hm.
      destruct (d_level s =? 0).
      - destruct Hwh as [[A B]|[[A B]|A]].
        + left. split; [exact A|exact (Hc1F B)].
        + right; left. split; [exact A|exact (Hc2F B)].
        + right; right; exact A.
      - destruct Hwh as [A B]. split; [exact A|exact (Hc1F B)]. }
    split.
    { subst sf. unfold wmatch. autorewrite with dproj. unfold MIN_MATCH, MAX_MATCH. lia. }
    split.
    { intros _. subst sf. autorewrite with dproj. lia. }
    exists [].
    destruct Hwt as (T1 & T2 & T3 & T4 & T5).
    split; [subst sf; autorewrite with dproj; rewrite K1, K2; exact T1|].
    split; [subst sf; autorewrite with dproj; unfold d_L in *; rewrite K1; exact T2|].
    split; [constructor|].
    split; [reflexivity|].
    intros _. subst sf. autorewrite with dproj. replace (blk_len []) with 0 by reflexivity. lia. }
  assert (K5 : d_status sF = d_status s) by exact (f_equal d_status Ek).
  assert (K6 : d_gzhead sF = d_gzhead s) by exact (f_equal d_gzhead Ek).
  assert (K7 : d_gzindex sF = d_gzindex s) by exact (f_equal d_gzindex Ek).
  assert (K8 : d_last_flush sF = d_last_flush s) by exact (f_equal d_last_flush Ek).
  assert (K9 : d_method sF = d_method s) by exact (f_equal d_method Ek).
  assert (K10 : d_po sF = d_po s) by exact (f_equal d_po Ek).
  assert (K11 : d_w_bits sF = d_w_bits s) by exact (f_equal d_w_bits Ek).
  assert (K12 : d_hash_bits sF = d_hash_bits s) by exact (f_equal d_hash_bits Ek).
  assert (K13 : d_pending_buf_size sF = d_pending_buf_size s) by exact (f_equal d_pending_buf_size Ek).
  subst sf.
  split.
  { unfold api_eq. autorewrite with dproj. rewrite K5, K6, K7, K8, K9. tauto. }
  split.
  { unfold out_eq. autorewrite with dproj. rewrite K1, K2, K10. tauto. }
  split.
  { unfold same_prm. autorewrite with dproj. unfold d_L, d_level, d_strategy. rewrite K1, K3, K11, K12, K13.
    tauto. }
  autorewrite with dproj.
  split; [reflexivity|].
  split; [reflexivity|].
  split.
  { rewrite Hn, B13. split.
    - intros E. destruct d; [reflexivity|]. rewrite Zlength_cons in E. pose proof (Zlength_nonneg d). lia.
    - intros ->. rewrite Zlength_nil. lia. }
  split; [unfold d_sym_next in *; rewrite K1; exact Hsn|].
  split; [pose proof (Zlength_nonneg d); lia|].
  rewrite Hn. subst zd2. unfold zadv. cbn [z_total_in z_out z_avail_out z_total_out z_adler z_msg]. reflexivity.
Qed.

(** ** total_in is only added to

    read_buf adds the bytes it reads to total_in modulo 2^64 and nothing reads total_in, so a run of
    fill_window, or of deflateSetDictionary's insertion loop, from total_in [x + t] ends where the run from [x]
    ends, with [t] added to total_in. *)
Definition tsh (t : Z) (z : strm) : strm := set_z_total_in z (u64 (z_total_in z + t)).

Lemma u64_shift a b t : u64 (u64 (a + t) + b) = u64 (u64 (a + b) + t).
Proof.
  unfold u64. rewrite !Z.add_mod_idemp_l by lia. f_equal. lia.
Qed.

Lemma read_buf_tsh s z n t :
  c_read_buf s (tsh t z) n =
    match c_read_buf s z n with Some (z', x) => Some (tsh t z', x) | None => None end.
Proof.
  destruct z. unfold c_read_buf, tsh, set_z_avail_in, set_z_adler, set_z_next_in, set_z_total_in. cbn.
  destruct (_ =? 0); [reflexivity|].
  unfold bind. destruct (rds _ _ _); [|reflexivity].
  destruct (d_wrap s =? 1); [|destruct (d_wrap s =? 2)]; cbn; rewrite u64_shift; reflexivity.
Qed.

Definition ftsh (t : Z) (a : dstate * strm) : dstate * strm := (fst a, tsh t (snd a)).

Lemma fw_body_tsh t a :
  fw_body (ftsh t a) = match fw_body a with Some (inl a') => Some (inl (ftsh t a'))
                       | Some (inr b) => Some (inr (ftsh t b)) | None => None end.
Proof.
  destruct a as [s z]. unfold fw_body, ftsh. cbn [fst snd].
  destruct (c_fw_slide s _) as [[s1 more]|]; cbn [bind]; [|reflexivity].
  change (z_avail_in (tsh t z)) with (z_avail_in z).
  destruct (z_avail_in z =? 0); [reflexivity|].
  rewrite read_buf_tsh. destruct (c_read_buf s1 z more) as [[z' x]|]; cbn [bind]; [|reflexivity].
  destruct (mb_write _ _ _); cbn [bind]; [|reflexivity].
  destruct (c_fw_insert _); cbn [bind]; [|reflexivity].
  change (z_avail_in (tsh t z')) with (z_avail_in z').
  destruct (_ && _); reflexivity.
Qed.

Lemma loop_tsh (body : dstate * strm -> option ((dstate * strm) + (dstate * strm))) t :
  (forall a, body (ftsh t a) = match body a with Some (inl a') => Some (inl (ftsh t a'))
                               | Some (inr b) => Some (inr (ftsh t b)) | None => None end) ->
  forall n a, loop n body (ftsh t a) = match loop n body a with Some b => Some (ftsh t b) | None => None end.
Proof.
  intros Hb n a. unfold loop.
  destruct (loop2_sim body (ftsh t) (ftsh t) (fun _ => True) (fun _ => True)) with (d := n) (a := a)
    as [E _]; [|exact I|].
  - intros a0 _. split; [apply Hb|]. split; intros; exact I.
  - rewrite E. destruct (loop2 n body a) as [[|]|]; reflexivity.
Qed.

Lemma fill_tsh s z t :
  c_fill_window s (tsh t z) =
    match c_fill_window s z with Some (s', z') => Some (s', tsh t z') | None => None end.
Proof.
  unfold c_fill_window. change (s, tsh t z) with (ftsh t (s, z)).
  rewrite (loop_tsh fw_body t (fw_body_tsh t)).
  destruct (loop FUEL fw_body (s, z)) as [[s1 z1]|]; cbn [bind ftsh fst snd]; [|reflexivity].
  destruct (c_fw_high_water s1); reflexivity.
Qed.

Lemma sd_body_tsh t a :
  sd_body (ftsh t a) = match sd_body a with Some (inl a') => Some (inl (ftsh t a'))
                       | Some (inr b) => Some (inr (ftsh t b)) | None => None end.
Proof.
  destruct a as [s z]. unfold sd_body, ftsh. cbn [fst snd].
  destruct (_ >=? _); [|reflexivity].
  destruct (loop FUEL sd_insert_body _) as [[s1 str]|]; cbn [bind]; [|reflexivity].
  rewrite fill_tsh. destruct (c_fill_window _ z) as [[s2 z2]|]; reflexivity.
Qed.

(** deflateSetDictionary from total_in [t] is deflateSetDictionary from total_in 0 with [t] added. *)
Lemma dsd_tsh s z d :
  0 <= z_total_in z < 18446744073709551616 ->
  c_deflateSetDictionary s z (Some d) =
    match c_deflateSetDictionary s (set_z_total_in z 0) (Some d) with
    | Some (s', z', r) => Some (s', tsh (z_total_in z) z', r) | None => None end.
Proof.
  intros Ht.
  assert (Ez : tsh (z_total_in z) (set_z_total_in z 0) = z).
  { unfold tsh. destruct z. cbn in *. rewrite u64_id by lia. reflexivity. }
  unfold c_deflateSetDictionary.
  destruct (bad_state s); [rewrite Ez; reflexivity|].
  destruct (_ || _); [rewrite Ez; reflexivity|].
  cbv zeta. clear Ez.
  destruct z as [zi zn za zt zo zao zto zad zm]; cbn [z_total_in] in Ht.
  destruct (d_wrap s =? 1).
  all: cbn [set_z_adler set_z_total_in z_in z_next_in z_avail_in z_total_in z_out z_avail_out z_total_out
            z_adler z_msg].
  all: match goal with |- bind ?e _ = _ => destruct e as [[[s0 off] len]|] end.
  all: cbn [bind]; try reflexivity.
  all: match goal with |- context [c_fill_window ?S (mkST ?D ?O ?L ?T ?a ?b ?c ?e ?f)] =>
         replace (mkST D O L T a b c e f) with (tsh T (mkST D O L 0 a b c e f))
           by (unfold tsh; cbn; rewrite u64_id by lia; reflexivity);
         rewrite fill_tsh;
         destruct (c_fill_window S (mkST D O L 0 a b c e f)) as [[s1 zd1]|]
       end.
  all: cbn [bind]; try reflexivity.
  all: change (s1, tsh zt zd1) with (ftsh zt (s1, zd1)); rewrite (loop_tsh sd_body zt (sd_body_tsh zt)).
  all: destruct (loop FUEL sd_body (s1, zd1)) as [[s2 zd2]|]; cbn [bind ftsh fst snd]; try reflexivity.
  all: destruct zd2; reflexivity.
Qed.

Lemma W3_dict_w : forall s z d,
    W3 s -> 0 <= d_wrap s <= 1 -> bad_state s = false -> (d_wrap s = 1 -> d_status s = INIT_STATE) ->
    d_strstart s = 0 -> d_lookahead s = 0 -> d_block_start s = 0 ->
    bytes d -> Zlength d <= 4294967295 -> 0 <= z_total_in z <= 18446744073709551615 ->
    adler_pre (d_wrap s) (z_adler z) ->
    exists s' z' k,
      c_deflateSetDictionary s z (Some d) = Some (s', z', Z_OK) /\ W3 s' /\
      api_eq s s' /\ out_eq s s' /\ same_prm s s' /\
      d_lookahead s' = 0 /\ d_strstart s' = d_block_start s' /\
      (d_strstart s' = 0 <-> d = []) /\
      d_sym_next s' = d_sym_next s /\ 0 <= k <= Zlength d /\
      z' = mkST (z_in z) (z_next_in z) (z_avail_in z) (u64 (z_total_in z + k)) (z_out z) (z_avail_out z)
                (z_total_out z)
                (if d_wrap s =? 1 then Zlib.proof.adler32.Model.ref_adler32 (z_adler z) d else z_adler z)
                (z_msg z).
Proof.
  intros s z d [HW2 HX] Hw Hbad Hst Hss Hla Hbs Hb Hl Ht Ha.
  pose proof (proj1 HW2) as HW. pose proof HW as (_ & _ & _ & _ & _ & _ & _ & syms & Hwt).
  destruct (W_empty s syms HW Hwt Hla ltac:(lia)) as [_ Hsy]. subst syms.
  assert (Hsn : d_sym_next s = 0).
  { destruct Hwt as ((_ & _ & T3 & _) & _). unfold d_sym_next. rewrite T3. reflexivity. }
  set (z0 := set_z_total_in z 0).
  destruct (dict_ok3_any fill_ok s z0 d HW Hbad Hst Hw Hss Hla Hbs Hsn Hb ltac:(subst z0; cbn; lia) Ha)
    as (s' & z' & k & E & HW' & A & O & P & La & Sb & Sd & Sn & K & Z).
  exists s', (tsh (z_total_in z) z'), k.
  split; [rewrite (dsd_tsh s z d ltac:(lia)); fold z0; rewrite E; reflexivity|].
  split.
  { split; [split; [exact HW'|exact (extra_ma0 s' (W_ma0' s' HW' La Sb))]|].
    intros _. rewrite Sb. pose proof (W_sn s' HW'). lia. }
  split; [exact A|]. split; [exact O|]. split; [exact P|]. split; [exact La|]. split; [exact Sb|].
  split; [exact Sd|]. split; [rewrite Sn, Hsn; reflexivity|]. split; [exact K|].
  subst z' z0. unfold tsh, set_z_total_in. destruct z. cbn. f_equal. f_equal. lia.
Qed.

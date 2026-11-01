(* Law inflate_reset, theory part: one pass of the decode modes LEN_ .. LIT from related machines. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.inflate_reset.IRDefs.
Require Import Zlib.proof.inflate.MwfLemmas.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* stepf2 per mode                                                                                *)

Lemma irdc_step_LEN_ fl fx dx m : m_mode m = LEN_ -> stepf2 fl fx dx m = c_LEN_ fx dx (fast fx dx) m.
Proof. intros H. unfold stepf2, Zlib.proof.inflate.Model2.step2. rewrite H. reflexivity. Qed.
Lemma irdc_step_LEN fl fx dx m : m_mode m = LEN -> stepf2 fl fx dx m = c_LEN fx dx (fast fx dx) m.
Proof. intros H. unfold stepf2, Zlib.proof.inflate.Model2.step2. rewrite H. reflexivity. Qed.
Lemma irdc_step_LENEXT fl fx dx m : m_mode m = LENEXT -> stepf2 fl fx dx m = c_LENEXT fx dx m.
Proof. intros H. unfold stepf2, Zlib.proof.inflate.Model2.step2. rewrite H. reflexivity. Qed.
Lemma irdc_step_DIST fl fx dx m : m_mode m = DIST -> stepf2 fl fx dx m = c_DIST fx dx m.
Proof. intros H. unfold stepf2, Zlib.proof.inflate.Model2.step2. rewrite H. reflexivity. Qed.
Lemma irdc_step_DISTEXT fl fx dx m : m_mode m = DISTEXT -> stepf2 fl fx dx m = c_DISTEXT m.
Proof. intros H. unfold stepf2, Zlib.proof.inflate.Model2.step2. rewrite H. reflexivity. Qed.
Lemma irdc_step_MATCH fl fx dx m : m_mode m = MATCH -> stepf2 fl fx dx m = c_MATCH m.
Proof. intros H. unfold stepf2, Zlib.proof.inflate.Model2.step2. rewrite H. reflexivity. Qed.
Lemma irdc_step_LIT fl fx dx m : m_mode m = LIT -> stepf2 fl fx dx m = c_LIT m.
Proof. intros H. unfold stepf2, Zlib.proof.inflate.Model2.step2. rewrite H. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Tables: the getter, and what the relation gives of the tables a lookup reads                   *)

Definition irdc_get (codes: list entry) (t: tref) (i: Z) : entry :=
  match t with
  | TLenfix => Znth i lenfix_list
  | TDistfix => Znth i distfix_list
  | TCodes k => Znth (k + i) codes
  end.

Lemma irdc_get_eq s t i : tab_entry lenfix_list distfix_list s t i = irdc_get (i_codes s) t i.
Proof. destruct t; reflexivity. Qed.

(* the reachable entries of t (root bits rb) in codes ca equal those in cb, with the root entries' ranges *)
Definition irdc_tt (kind: Z) (ca cb: list entry) (t: tref) (rb: Z) : Prop :=
  forall i, 0 <= i < 2 ^ rb ->
    irdc_get ca t i = irdc_get cb t i /\ 0 <= e_bits (irdc_get cb t i) /\ 0 <= e_op (irdc_get cb t i) /\
    (islink kind (e_op (irdc_get cb t i)) = true -> forall j, 0 <= j < 2 ^ e_op (irdc_get cb t i) ->
       irdc_get ca t (e_val (irdc_get cb t i) + j) = irdc_get cb t (e_val (irdc_get cb t i) + j)).

Definition irdc_tabs (sa sb: istate) : Prop :=
  0 <= i_lenbits sb <= 15 /\ 0 <= i_distbits sb <= 15 /\
  irdc_tt LENS (i_codes sa) (i_codes sb) (i_lencode sb) (i_lenbits sb) /\
  irdc_tt DISTS (i_codes sa) (i_codes sb) (i_distcode sb) (i_distbits sb).

Lemma irdc_tt_of kind sa sb t rb :
  treach_eq kind sa sb t rb -> tvalid kind lenfix_list distfix_list sb t rb ->
  irdc_tt kind (i_codes sa) (i_codes sb) t rb.
Proof.
  intros TR (sz & _ & [R S T]) i Hi.
  destruct (TR i Hi) as [E1 E2]. destruct (T i Hi) as [Eok _].
  rewrite !irdc_get_eq in *. destruct Eok as (O1 & O2 & O3).
  rewrite <- E1 in O1, O2 |- *. split; [reflexivity|]. split; [lia|]. split; [lia|].
  intros L j Hj. specialize (E2 L j Hj). rewrite !irdc_get_eq in E2. exact E2.
Qed.

Lemma irdc_tabs_of noout sa sb :
  srel noout sa sb -> decode_mode (i_mode sb) -> swf sb -> modewf sb -> irdc_tabs sa sb.
Proof.
  intros SR D W M. destruct (sr_dectab _ _ _ SR D) as [T1 T2]. destruct (md_tables _ M D) as [V1 V2].
  pose proof (sw_lenbits _ W). pose proof (sw_distbits _ W).
  split; [lia|]. split; [lia|]. split; eapply irdc_tt_of; eauto.
Qed.

Lemma irdc_treach_tr kind sa sb sa' sb' t rb :
  treach_eq kind sa sb t rb -> i_codes sa' = i_codes sa -> i_codes sb' = i_codes sb ->
  treach_eq kind sa' sb' t rb.
Proof.
  intros TR Ea Eb. destruct t; unfold treach_eq in *; cbn [tab_entry] in *; try rewrite Ea, Eb; exact TR.
Qed.

Lemma irdc_islink_l op : (negb (op =? 0) && (Z.land op 240 =? 0))%bool = true -> islink LENS op = true.
Proof. intros H. exact H. Qed.
Lemma irdc_islink_d op : (Z.land op 240 =? 0) = true -> islink DISTS op = true.
Proof. intros H. exact H. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* NEEDBITS and the lookups in explicit form                                                      *)

Fixpoint irdc_nbr (k: nat) (n: Z) (inp: list Z) (nx hold bits leave: Z) : Z * Z * Z * Z :=
  match k with
  | O => (nx, hold, bits, leave)
  | S k' => if bits <? n then
              if Zlength inp - nx =? 0 then (nx, hold, bits, 1)
              else irdc_nbr k' n inp (nx + 1) (u64 (hold + Znth nx inp * 2 ^ bits)) (u32 (bits + 8)) leave
            else (nx, hold, bits, leave)
  end.

Definition irdc_lset (m: mst) (r: Z * Z * Z * Z) : mst :=
  let '(nx, h, b, l) := r in set_m_leave (set_m_bits (set_m_hold (set_m_nx m nx) h) b) l.

Lemma irdc_nb_eq k n m :
  needbits_f k n m = irdc_lset m (irdc_nbr k n (m_inp m) (m_nx m) (m_hold m) (m_bits m) (m_leave m)).
Proof.
  revert m. induction k as [|k IH]; intros m.
  - destruct m; reflexivity.
  - cbn [needbits_f irdc_nbr]. unfold m_have.
    destruct (m_bits m <? n); [|destruct m; reflexivity].
    destruct (Zlength (m_inp m) - m_nx m =? 0); [destruct m; reflexivity|].
    rewrite IH. destruct m; reflexivity.
Qed.

Fixpoint irdc_lk1r (k: nat) (g: Z -> entry) (nb: Z) (inp: list Z) (nx hold bits leave: Z)
  : entry * (Z * Z * Z * Z) * bool :=
  let here := g (hold mod 2 ^ nb) in
  match k with
  | O => (here, (nx, hold, bits, leave), true)
  | S k' => if e_bits here <=? bits then (here, (nx, hold, bits, leave), true)
            else if Zlength inp - nx =? 0 then (here, (nx, hold, bits, 1), false)
            else irdc_lk1r k' g nb inp (nx + 1) (u64 (hold + Znth nx inp * 2 ^ bits)) (u32 (bits + 8)) leave
  end.

Fixpoint irdc_lk2r (k: nat) (g: Z -> entry) (last: entry) (inp: list Z) (nx hold bits leave: Z)
  : entry * (Z * Z * Z * Z) * bool :=
  let here := g (e_val last + Z.shiftr (hold mod 2 ^ (e_bits last + e_op last)) (e_bits last)) in
  match k with
  | O => (here, (nx, hold, bits, leave), true)
  | S k' => if e_bits last + e_bits here <=? bits then (here, (nx, hold, bits, leave), true)
            else if Zlength inp - nx =? 0 then (here, (nx, hold, bits, 1), false)
            else irdc_lk2r k' g last inp (nx + 1) (u64 (hold + Znth nx inp * 2 ^ bits)) (u32 (bits + 8)) leave
  end.

Lemma irdc_lk1_eq k t nb m :
  lookup1_f k lenfix_list distfix_list t nb m =
  let '(here, r, ok) := irdc_lk1r k (irdc_get (i_codes (m_s m)) t) nb (m_inp m) (m_nx m) (m_hold m)
                          (m_bits m) (m_leave m) in
  (here, irdc_lset m r, ok).
Proof.
  revert m. induction k as [|k IH]; intros m.
  - cbn [lookup1_f irdc_lk1r]. unfold bitsn. rewrite irdc_get_eq. destruct m; reflexivity.
  - cbn [lookup1_f irdc_lk1r]. unfold bitsn, m_have. rewrite irdc_get_eq.
    destruct (e_bits _ <=? m_bits m); [destruct m; reflexivity|].
    destruct (Zlength (m_inp m) - m_nx m =? 0); [destruct m; reflexivity|].
    rewrite IH. destruct m; reflexivity.
Qed.

Lemma irdc_lk2_eq k t last m :
  lookup2_f k lenfix_list distfix_list t last m =
  let '(here, r, ok) := irdc_lk2r k (irdc_get (i_codes (m_s m)) t) last (m_inp m) (m_nx m) (m_hold m)
                          (m_bits m) (m_leave m) in
  (here, irdc_lset m r, ok).
Proof.
  revert m. induction k as [|k IH]; intros m.
  - cbn [lookup2_f irdc_lk2r]. unfold bitsn. rewrite irdc_get_eq. destruct m; reflexivity.
  - cbn [lookup2_f irdc_lk2r]. unfold bitsn, m_have. rewrite irdc_get_eq.
    destruct (e_bits last + e_bits _ <=? m_bits m); [destruct m; reflexivity|].
    destruct (Zlength (m_inp m) - m_nx m =? 0); [destruct m; reflexivity|].
    rewrite IH. destruct m; reflexivity.
Qed.

Lemma irdc_lk1r_ext k g1 g2 nb inp nx h b l :
  0 <= nb -> (forall i, 0 <= i < 2 ^ nb -> g1 i = g2 i) ->
  irdc_lk1r k g1 nb inp nx h b l = irdc_lk1r k g2 nb inp nx h b l.
Proof.
  intros Hnb E. assert (P: 0 < 2 ^ nb) by (apply Z.pow_pos_nonneg; lia).
  revert nx h b l. induction k as [|k IH]; intros; cbn [irdc_lk1r];
    rewrite E by (apply Z.mod_pos_bound; exact P); [reflexivity|].
  rewrite IH. reflexivity.
Qed.

Lemma irdc_lk1r_root k g nb inp nx h b l hr r ok :
  irdc_lk1r k g nb inp nx h b l = (hr, r, ok) -> 0 <= nb -> exists i, 0 <= i < 2 ^ nb /\ hr = g i.
Proof.
  intros E Hnb. assert (P: 0 < 2 ^ nb) by (apply Z.pow_pos_nonneg; lia).
  revert nx h b l E. induction k as [|k IH]; intros nx h b l E; cbn [irdc_lk1r] in E.
  - inversion E. exists (h mod 2 ^ nb). split; [apply Z.mod_pos_bound; exact P | reflexivity].
  - destruct (e_bits _ <=? b).
    + inversion E. exists (h mod 2 ^ nb). split; [apply Z.mod_pos_bound; exact P | reflexivity].
    + destruct (Zlength inp - nx =? 0).
      * inversion E. exists (h mod 2 ^ nb). split; [apply Z.mod_pos_bound; exact P | reflexivity].
      * eapply IH; exact E.
Qed.

Lemma irdc_shr_range x eb eo :
  0 <= eb -> 0 <= eo -> 0 <= Z.shiftr (x mod 2 ^ (eb + eo)) eb < 2 ^ eo.
Proof.
  intros Hb Ho. rewrite Z.shiftr_div_pow2 by lia.
  assert (P1: 0 < 2 ^ eb) by (apply Z.pow_pos_nonneg; lia).
  assert (P2: 0 < 2 ^ eo) by (apply Z.pow_pos_nonneg; lia).
  rewrite Z.pow_add_r by lia.
  pose proof (Z.mod_pos_bound x (2 ^ eb * 2 ^ eo) ltac:(nia)).
  split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia.
Qed.

Lemma irdc_lk2r_ext k g1 g2 last inp nx h b l :
  0 <= e_bits last -> 0 <= e_op last ->
  (forall j, 0 <= j < 2 ^ e_op last -> g1 (e_val last + j) = g2 (e_val last + j)) ->
  irdc_lk2r k g1 last inp nx h b l = irdc_lk2r k g2 last inp nx h b l.
Proof.
  intros Hb Ho E.
  revert nx h b l. induction k as [|k IH]; intros; cbn [irdc_lk2r];
    rewrite E by (apply irdc_shr_range; lia); [reflexivity|].
  rewrite IH. reflexivity.
Qed.

Lemma irdc_tt_lk1 kind ca cb t rb :
  irdc_tt kind ca cb t rb -> 0 <= rb ->
  forall k inp nx h b l,
  irdc_lk1r k (irdc_get ca t) rb inp nx h b l = irdc_lk1r k (irdc_get cb t) rb inp nx h b l.
Proof.
  intros TT Hrb k inp nx h b l. apply irdc_lk1r_ext; [exact Hrb|].
  intros i Hi. exact (proj1 (TT i Hi)).
Qed.

Lemma irdc_tt_lk2 kind ca cb t rb ri :
  irdc_tt kind ca cb t rb -> 0 <= ri < 2 ^ rb -> islink kind (e_op (irdc_get cb t ri)) = true ->
  forall k inp nx h b l,
  irdc_lk2r k (irdc_get ca t) (irdc_get cb t ri) inp nx h b l =
  irdc_lk2r k (irdc_get cb t) (irdc_get cb t ri) inp nx h b l.
Proof.
  intros TT Hri L k inp nx h b l. destruct (TT ri Hri) as (_ & B & O & LK).
  apply irdc_lk2r_ext; [exact B | exact O |]. exact (LK L).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The cases on destructed machines                                                               *)

Ltac irdc_cst := unfold HEAD, FLAGS, DICTID, TYPEDO, SYNC, DONE, DICT, BAD, MEM, STORED, LEN_, TABLE, CHECK,
                 COPY_, COPY, LENEXT, DIST, DISTEXT, MATCH, LIT, EXTRA, LEN, LENLENS, CODELENS, LENGTH,
                 Zlib.proof.inflate.Model.TYPE in *.
Ltac irdc_cstg := unfold HEAD, FLAGS, DICTID, TYPEDO, SYNC, DONE, DICT, BAD, MEM, STORED, LEN_, TABLE, CHECK,
                 COPY_, COPY, LENEXT, DIST, DISTEXT, MATCH, LIT, EXTRA, LEN, LENLENS, CODELENS, LENGTH,
                 Zlib.proof.inflate.Model.TYPE.

Ltac irdc_cbn := cbv beta iota zeta delta [set_i_mode set_i_last set_i_wrap set_i_havedict set_i_flags set_i_dmax set_i_check set_i_total set_i_head set_i_wbits set_i_wsize set_i_whave set_i_wnext set_i_win set_i_wdata set_i_hold set_i_bits set_i_length set_i_offset set_i_extra set_i_lencode set_i_distcode set_i_lenbits set_i_distbits set_i_ncode set_i_nlen set_i_ndist set_i_have set_i_next set_i_lens set_i_codes set_i_sane set_i_back set_i_was set_m_s set_m_h set_m_inp set_m_aout set_m_nx set_m_ow set_m_hold set_m_bits set_m_in set_m_out set_m_ret set_m_leave set_m_adler set_m_msg set_m_tin set_m_tout set_m_snx set_m_sow m_mode m_have m_left bitsn set_mode upd_s set_leave dropbits initbits bytebits set_bad restore needbits lookup1 lookup2 irdc_lset i_mode i_last i_wrap i_havedict i_flags i_dmax i_check i_total i_head i_wbits i_wsize i_whave i_wnext i_win i_wdata i_hold i_bits i_length i_offset i_extra i_lencode i_distcode i_lenbits i_distbits i_ncode i_nlen i_ndist i_have i_next i_lens i_codes i_sane i_back i_was m_s m_h m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave m_adler m_msg m_tin m_tout m_snx m_sow] in *.

Definition irdc_case_stmt (c: mst -> iout) (P: Z -> Prop) : Prop :=
  forall W0 wrap src pos inp aout ma mb,
    Kr W0 wrap src pos inp aout ma mb -> irdc_tabs (m_s ma) (m_s mb) -> P (m_mode mb) ->
    sim_post W0 wrap src pos inp aout (c ma) (c mb).

Ltac irdc_spec H :=
  first [ specialize (H ltac:(unfold lenlive, decode_mode; cbn [i_mode]; irdc_cstg; lia)) | clear H ].

Ltac irdc_prep :=
  intros W0 wrap src pos inp aout ma mb K TB Hmd;
  destruct ma as [[as_mode as_last as_wrap as_havedict as_flags as_dmax as_check as_total as_head as_wbits as_wsize as_whave as_wnext as_win as_wdata as_hold as_bits as_length as_offset as_extra as_lencode as_distcode as_lenbits as_distbits as_ncode as_nlen as_ndist as_have as_next as_lens as_codes as_sane as_back as_was] am_h am_inp am_aout am_nx am_ow am_hold am_bits am_in am_out am_ret am_leave am_adler am_msg am_tin am_tout am_snx am_sow], mb as [[bs_mode bs_last bs_wrap bs_havedict bs_flags bs_dmax bs_check bs_total bs_head bs_wbits bs_wsize bs_whave bs_wnext bs_win bs_wdata bs_hold bs_bits bs_length bs_offset bs_extra bs_lencode bs_distcode bs_lenbits bs_distbits bs_ncode bs_nlen bs_ndist bs_have bs_next bs_lens bs_codes bs_sane bs_back bs_was] bm_h bm_inp bm_aout bm_nx bm_ow bm_hold bm_bits bm_in bm_out bm_ret bm_leave bm_adler bm_msg bm_tin bm_tout bm_snx bm_sow];
  destruct K as [MR Ki Ka Kw Kh Kwa Kwb Khd];
  destruct MR as [SR ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ?];
  destruct SR as [? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? Ewb Eck Elen Eoff Eext Elb Edb _ _ _ _ _ Edt];
  cbv beta in Hmd; irdc_cbn; subst;
  destruct Ewb as [?|[E|E]]; try (exfalso; irdc_cst; discriminate); try subst;
  destruct Eck as [?|[?|[[E|E] _]]]; try (exfalso; irdc_cst; discriminate); try subst;
  irdc_spec Elen; irdc_spec Eoff; irdc_spec Eext; irdc_spec Elb; irdc_spec Edb; irdc_spec Edt;
  try subst;
  destruct Edt as [Etl Etd];
  unfold irdc_tabs in TB; irdc_cbn; destruct TB as (Hlb & Hdb & TTL & TTD).

Ltac irdc_kr :=
  apply Build_Kr; try apply Build_mrel; try apply Build_srel; intros; irdc_cbn;
  first [ reflexivity | assumption | (left; reflexivity) | (right; left; reflexivity)
        | (split; (eapply irdc_treach_tr; [eassumption | reflexivity | reflexivity]))
        | (exfalso; unfold lenlive, decode_mode in *; irdc_cbn; irdc_cst; lia) ].

Ltac irdc_tabs_tac :=
  unfold irdc_tabs; irdc_cbn; split; [lia|]; split; [lia|]; split; assumption.

Ltac irdc_lkext :=
  match goal with
  | TT: irdc_tt ?kd ?ca ?cb ?t ?rb |- context [irdc_lk1r ?k (irdc_get ?ca ?t) ?rb ?i ?x ?h ?b ?l] =>
      rewrite (irdc_tt_lk1 kd ca cb t rb TT ltac:(lia) k i x h b l)
  | TT: irdc_tt ?kd ?ca ?cb ?t ?rb, Hri: 0 <= ?ri < 2 ^ ?rb
    |- context [irdc_lk2r ?k (irdc_get ?ca ?t) (irdc_get ?cb ?t ?ri) ?i ?x ?h ?b ?l] =>
      rewrite (irdc_tt_lk2 kd ca cb t rb ri TT Hri
                 ltac:(first [apply irdc_islink_l; assumption | apply irdc_islink_d; assumption]) k i x h b l)
  end.

Ltac irdc_lk1des :=
  match goal with
  | |- context [irdc_lk1r ?k (irdc_get ?c ?t) ?nb ?i ?x ?h ?b ?l] =>
      lazymatch goal with
      | _: irdc_tt _ c _ _ _ |- _ => fail
      | _ =>
        let hr := fresh "hr" in let nx' := fresh "nx" in let h' := fresh "h" in let b' := fresh "b" in
        let l' := fresh "l" in let ok := fresh "ok" in let E := fresh "E" in
        let ri := fresh "ri" in let Hri := fresh "Hri" in let Eh := fresh "Eh" in
        destruct (irdc_lk1r k (irdc_get c t) nb i x h b l) as [[hr [[[nx' h'] b'] l']] ok] eqn:E;
        destruct (irdc_lk1r_root _ _ _ _ _ _ _ _ _ _ _ E ltac:(lia)) as (ri & Hri & Eh);
        subst hr; clear E
      end
  end.

Ltac irdc_lk2des :=
  match goal with
  | |- context [irdc_lk2r ?k (irdc_get ?c ?t) ?last ?i ?x ?h ?b ?l] =>
      lazymatch goal with
      | _: irdc_tt _ c _ _ _ |- _ => fail
      | _ =>
        let hr := fresh "hr" in let nx' := fresh "nx" in let h' := fresh "h" in let b' := fresh "b" in
        let l' := fresh "l" in let ok := fresh "ok" in
        destruct (irdc_lk2r k (irdc_get c t) last i x h b l) as [[hr [[[nx' h'] b'] l']] ok]
      end
  end.

Ltac irdc_step :=
  first [ rewrite irdc_nb_eq
        | rewrite irdc_lk1_eq
        | rewrite irdc_lk2_eq
        | irdc_lkext
        | match goal with |- context [irdc_nbr ?k ?n ?i ?x ?h ?b ?l] =>
            destruct (irdc_nbr k n i x h b l) as [[[? ?] ?] ?] end
        | irdc_lk1des
        | match goal with |- context [copy_bytes ?a ?b ?c ?d] => destruct (copy_bytes a b c d) end
        | match goal with |- context [if ?c then _ else _] => let Ec := fresh "Ec" in destruct c eqn:Ec end
        | irdc_lk2des ].

Ltac irdc_fin := irdc_cbn; cbn [sim_post]; first [ irdc_kr | (split; [reflexivity | irdc_kr]) ].

Ltac irdc_sub L := eapply L; [ irdc_kr | irdc_tabs_tac | irdc_cbn; reflexivity ].

Ltac irdc_loop s := repeat (irdc_cbn; cbn [negb andb]; first [s tt | irdc_step]); irdc_fin.

Lemma irdc_lit : irdc_case_stmt c_LIT (fun md => md = LIT).
Proof.
  unfold irdc_case_stmt. irdc_prep; unfold c_LIT; irdc_loop ltac:(fun _ => fail).
Qed.

Lemma irdc_match : irdc_case_stmt c_MATCH (fun md => md = MATCH).
Proof.
  unfold irdc_case_stmt. irdc_prep; unfold c_MATCH; irdc_loop ltac:(fun _ => fail).
Qed.

Lemma irdc_distext : irdc_case_stmt c_DISTEXT (fun md => md = DISTEXT).
Proof.
  unfold irdc_case_stmt. irdc_prep; unfold c_DISTEXT; irdc_loop ltac:(fun _ => irdc_sub irdc_match).
Qed.

Lemma irdc_dist : irdc_case_stmt (c_DIST lenfix_list distfix_list) (fun md => md = DIST).
Proof.
  unfold irdc_case_stmt. irdc_prep; unfold c_DIST; irdc_loop ltac:(fun _ => irdc_sub irdc_distext).
Qed.

Lemma irdc_lenext : irdc_case_stmt (c_LENEXT lenfix_list distfix_list) (fun md => md = LENEXT).
Proof.
  unfold irdc_case_stmt. irdc_prep; unfold c_LENEXT; irdc_loop ltac:(fun _ => irdc_sub irdc_dist).
Qed.

(* LEN: the slow path (the fast path is inflate_fast, fast_sim_stmt) *)
Definition irdc_lenslow (m: mst) : iout :=
  let m := upd_s m (fun s => set_i_back s 0) in
  let s := m_s m in
  let '(here, m, ok) := lookup1 lenfix_list distfix_list (i_lencode s) (i_lenbits s) m in
  if negb ok then IBrk m else
  let '(here, m, ok) :=
    if (negb (e_op here =? 0) && (Z.land (e_op here) 240 =? 0))%bool then
      let '(h2, m, ok) := lookup2 lenfix_list distfix_list (i_lencode s) here m in
      if negb ok then (h2, m, false) else
      (h2, dropbits (e_bits here) (upd_s m (fun s => set_i_back s (i_back s + e_bits here))), true)
    else (here, m, true) in
  if negb ok then IBrk m else
  let m := dropbits (e_bits here) (upd_s m (fun s => set_i_back s (i_back s + e_bits here))) in
  let m := upd_s m (fun s => set_i_length s (e_val here)) in
  if e_op here =? 0 then IBrk (set_mode m LIT) else
  if negb (Z.land (e_op here) 32 =? 0) then
    IBrk (set_mode (upd_s m (fun s => set_i_back s (-1))) Zlib.proof.inflate.Model.TYPE) else
  if negb (Z.land (e_op here) 64 =? 0) then IBrk (set_bad m M_ll_code) else
  c_LENEXT lenfix_list distfix_list
    (set_mode (upd_s m (fun s => set_i_extra s (Z.land (e_op here) 15))) LENEXT).

Lemma irdc_LEN_eq m :
  c_LEN lenfix_list distfix_list (fast lenfix_list distfix_list) m =
  if ((6 <=? m_have m) && (258 <=? m_left m) && (m_bits m <? 8))%bool then
    IBrk (if m_mode (fast lenfix_list distfix_list (restore m)) =? Zlib.proof.inflate.Model.TYPE
          then upd_s (fast lenfix_list distfix_list (restore m)) (fun s => set_i_back s (-1))
          else fast lenfix_list distfix_list (restore m))
  else irdc_lenslow m.
Proof. reflexivity. Qed.

Lemma irdc_lenslow_ok : irdc_case_stmt irdc_lenslow (fun md => md = LEN).
Proof.
  unfold irdc_case_stmt. irdc_prep; unfold irdc_lenslow; irdc_loop ltac:(fun _ => irdc_sub irdc_lenext).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Record-level transfers: back := v (after inflate_fast), LEN_ -> LEN                             *)

Lemma irdc_srel_back noout sa sb v :
  srel noout sa sb -> srel noout (set_i_back sa v) (set_i_back sb v).
Proof.
  intros SR. destruct SR.
  apply Build_srel; simpl; auto; intros;
    first [ eapply irdc_treach_tr; [apply sr_cltab; exact H | reflexivity | reflexivity]
          | destruct (sr_dectab H) as [T1 T2];
            split; (eapply irdc_treach_tr; [eassumption | reflexivity | reflexivity]) ].
Qed.

Lemma irdc_srel_len noout sa sb :
  srel noout sa sb -> i_mode sb = LEN_ -> srel noout (set_i_mode sa LEN) (set_i_mode sb LEN).
Proof.
  intros SR Hm. assert (D: decode_mode (i_mode sb)) by (rewrite Hm; unfold decode_mode; auto).
  destruct SR.
  apply Build_srel; simpl; auto; intros;
    try (exfalso; unfold lenlive, decode_mode in *; simpl in *; irdc_cst; lia);
    first [ destruct sr_wbits as [E|[E|E]]; [left; exact E | exfalso; irdc_cst; lia | exfalso; irdc_cst; lia]
          | destruct sr_check as [E|[E|[[E|E] _]]]; [left; exact E | right; left; exact E
                                                     | exfalso; irdc_cst; lia | exfalso; irdc_cst; lia]
          | destruct (sr_dectab D) as [T1 T2];
            split; (eapply irdc_treach_tr; [eassumption | reflexivity | reflexivity]) ].
Qed.

Lemma irdc_Kr_back W0 wrap src pos inp aout ma mb v :
  Kr W0 wrap src pos inp aout ma mb ->
  Kr W0 wrap src pos inp aout (upd_s ma (fun s => set_i_back s v)) (upd_s mb (fun s => set_i_back s v)).
Proof.
  intros K. destruct K as [MR Ki Ka Kw Kh Kwa Kwb Khd]. destruct MR.
  apply Build_Kr; [apply Build_mrel; [apply irdc_srel_back; exact mr_s | ..] | ..]; simpl; auto.
Qed.

Lemma irdc_Kr_len W0 wrap src pos inp aout ma mb :
  Kr W0 wrap src pos inp aout ma mb -> m_mode mb = LEN_ ->
  Kr W0 wrap src pos inp aout (set_mode ma LEN) (set_mode mb LEN).
Proof.
  intros K Hm. destruct K as [MR Ki Ka Kw Kh Kwa Kwb Khd]. destruct MR.
  apply Build_Kr; [apply Build_mrel; [apply irdc_srel_len; [exact mr_s | exact Hm] | ..] | ..]; simpl; auto.
  intros _ E. exfalso. unfold m_mode in E. simpl in E. irdc_cst. lia.
Qed.

Lemma irdc_mwf3_len m : mwf3 m -> m_mode m = LEN_ -> mwf3 (set_mode m LEN).
Proof.
  intros [W W3] Hm. assert (D: decode_mode (i_mode (m_s m))) by (unfold m_mode in Hm; rewrite Hm; unfold decode_mode; auto).
  split.
  - apply mwf_set_mode; auto;
      first [ (intros _; exact (md_tables _ (mw_md _ W) D))
            | (left; apply mwf_out_eq; [exact W | ..]; rewrite Hm; unfold LENGTH; irdc_cst; lia)
            | (intros E; exfalso; irdc_cst; lia)
            | (irdc_cst; lia) ].
  - destruct W3. constructor; simpl; intros; try (exfalso; irdc_cst; lia).
    exact (s3_len D).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The group                                                                                      *)

Lemma irdc_gen c P W0 wrap src pos inp aout ma mb :
  irdc_case_stmt c P -> Kr W0 wrap src pos inp aout ma mb -> mwf3 mb -> P (m_mode mb) ->
  decode_mode (m_mode mb) -> sim_post W0 wrap src pos inp aout (c ma) (c mb).
Proof.
  intros L K Wb HP D. apply L; auto.
  eapply irdc_tabs_of; [exact (mr_s _ _ (kr_rel _ _ _ _ _ _ _ _ K)) | exact D
                       | exact (mw_s _ (mwf3_mwf _ Wb)) | exact (mw_md _ (mwf3_mwf _ Wb))].
Qed.

Lemma irdc_LEN W0 wrap src pos inp aout ma mb :
  fast_sim_stmt -> ir_ctx src pos inp -> Kr W0 wrap src pos inp aout ma mb -> mwf3 ma -> mwf3 mb ->
  m_leave mb = 0 -> m_mode mb = LEN ->
  sim_post W0 wrap src pos inp aout (c_LEN lenfix_list distfix_list (fast lenfix_list distfix_list) ma)
    (c_LEN lenfix_list distfix_list (fast lenfix_list distfix_list) mb).
Proof.
  intros FS Hc K Wa Wb Hl Hm.
  rewrite !irdc_LEN_eq.
  pose proof (kr_rel _ _ _ _ _ _ _ _ K) as MR.
  assert (Ec: ((6 <=? m_have ma) && (258 <=? m_left ma) && (m_bits ma <? 8))%bool =
              ((6 <=? m_have mb) && (258 <=? m_left mb) && (m_bits mb <? 8))%bool).
  { unfold m_have, m_left. rewrite (mr_inp _ _ MR), (mr_nx _ _ MR), (mr_aout _ _ MR), (mr_ow _ _ MR),
      (mr_bits _ _ MR). reflexivity. }
  rewrite Ec. destruct ((6 <=? m_have mb) && (258 <=? m_left mb) && (m_bits mb <? 8))%bool eqn:C.
  - apply andb_prop in C. destruct C as [C C3]. apply andb_prop in C. destruct C as [C1 C2].
    apply Z.leb_le in C1. apply Z.leb_le in C2. apply Z.ltb_lt in C3.
    assert (Ho: m_out mb = m_aout mb).
    { apply mwf_out_eq; [exact (mwf3_mwf _ Wb) | ..]; rewrite Hm; irdc_cst; lia. }
    pose proof (FS W0 wrap src pos inp aout ma mb Hc K Wa Wb Hl Hm Ho C1 C2 C3) as K'.
    assert (Em: m_mode (fast lenfix_list distfix_list (restore ma)) =
                m_mode (fast lenfix_list distfix_list (restore mb)))
      by exact (sr_mode _ _ _ (mr_s _ _ (kr_rel _ _ _ _ _ _ _ _ K'))).
    rewrite Em. cbn [sim_post].
    destruct (m_mode (fast lenfix_list distfix_list (restore mb)) =? Zlib.proof.inflate.Model.TYPE).
    + apply irdc_Kr_back. exact K'.
    + exact K'.
  - apply (irdc_gen _ _ _ _ _ _ _ _ ma mb irdc_lenslow_ok K Wb Hm).
    rewrite Hm. unfold decode_mode. auto.
Qed.

Lemma dec_sim : dec_sim_stmt.
Proof.
  intros FS W0 wrap src pos inp aout flush ma mb Hc K Wa Wb Hl Hmd.
  pose proof (sr_mode _ _ _ (mr_s _ _ (kr_rel _ _ _ _ _ _ _ _ K))) as Em.
  assert (Ea : forall md, m_mode mb = md -> m_mode ma = md)
    by (intros md E; unfold m_mode in *; rewrite Em; exact E).
  pose proof Hmd as D.
  unfold decode_mode in Hmd. destruct Hmd as [M|[M|[M|[M|[M|[M|M]]]]]].
  - rewrite (irdc_step_LEN_ _ _ _ mb M), (irdc_step_LEN_ _ _ _ ma (Ea _ M)). unfold c_LEN_.
    apply irdc_LEN; auto.
    + apply irdc_Kr_len; auto.
    + apply irdc_mwf3_len; auto.
    + apply irdc_mwf3_len; auto.
  - rewrite (irdc_step_LEN _ _ _ mb M), (irdc_step_LEN _ _ _ ma (Ea _ M)). apply irdc_LEN; auto.
  - rewrite (irdc_step_LENEXT _ _ _ mb M), (irdc_step_LENEXT _ _ _ ma (Ea _ M)).
    exact (irdc_gen _ _ _ _ _ _ _ _ ma mb irdc_lenext K Wb M D).
  - rewrite (irdc_step_DIST _ _ _ mb M), (irdc_step_DIST _ _ _ ma (Ea _ M)).
    exact (irdc_gen _ _ _ _ _ _ _ _ ma mb irdc_dist K Wb M D).
  - rewrite (irdc_step_DISTEXT _ _ _ mb M), (irdc_step_DISTEXT _ _ _ ma (Ea _ M)).
    exact (irdc_gen _ _ _ _ _ _ _ _ ma mb irdc_distext K Wb M D).
  - rewrite (irdc_step_MATCH _ _ _ mb M), (irdc_step_MATCH _ _ _ ma (Ea _ M)).
    exact (irdc_gen _ _ _ _ _ _ _ _ ma mb irdc_match K Wb M D).
  - rewrite (irdc_step_LIT _ _ _ mb M), (irdc_step_LIT _ _ _ ma (Ea _ M)).
    exact (irdc_gen _ _ _ _ _ _ _ _ ma mb irdc_lit K Wb M D).
Qed.

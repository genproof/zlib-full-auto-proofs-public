(* Law inflate_reset, theory part: one pass of DICTID, DICT, TYPE, TYPEDO from related machines. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.inflate_reset.IRDefs.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* stepf2 per mode                                                                                *)

Lemma irdi_step_DICTID fl fx dx m : m_mode m = DICTID -> stepf2 fl fx dx m = c_DICTID fl m.
Proof. intros H. unfold stepf2, Zlib.proof.inflate.Model2.step2. rewrite H. reflexivity. Qed.
Lemma irdi_step_DICT fl fx dx m : m_mode m = DICT -> stepf2 fl fx dx m = c_DICT fl m.
Proof. intros H. unfold stepf2, Zlib.proof.inflate.Model2.step2. rewrite H. reflexivity. Qed.
Lemma irdi_step_TYPE fl fx dx m : m_mode m = Zlib.proof.inflate.Model.TYPE -> stepf2 fl fx dx m = c_TYPE fl m.
Proof. intros H. unfold stepf2, Zlib.proof.inflate.Model2.step2. rewrite H. reflexivity. Qed.
Lemma irdi_step_TYPEDO fl fx dx m : m_mode m = TYPEDO -> stepf2 fl fx dx m = c_TYPEDO fl m.
Proof. intros H. unfold stepf2, Zlib.proof.inflate.Model2.step2. rewrite H. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* NEEDBITS reads and writes only nx, hold, bits, leave                                           *)

Fixpoint irdi_nbr (k: nat) (n: Z) (inp: list Z) (nx hold bits leave: Z) : Z * Z * Z * Z :=
  match k with
  | O => (nx, hold, bits, leave)
  | S k' => if bits <? n then
              if Zlength inp - nx =? 0 then (nx, hold, bits, 1)
              else irdi_nbr k' n inp (nx + 1) (u64 (hold + Znth nx inp * 2 ^ bits)) (u32 (bits + 8)) leave
            else (nx, hold, bits, leave)
  end.

Lemma irdi_nb_eq k n m :
  needbits_f k n m =
  let '(nx, h, b, l) := irdi_nbr k n (m_inp m) (m_nx m) (m_hold m) (m_bits m) (m_leave m) in
  set_m_leave (set_m_bits (set_m_hold (set_m_nx m nx) h) b) l.
Proof.
  revert m. induction k as [|k IH]; intros m.
  - destruct m; reflexivity.
  - cbn [needbits_f irdi_nbr]. unfold m_have.
    destruct (m_bits m <? n); [|destruct m; reflexivity].
    destruct (Zlength (m_inp m) - m_nx m =? 0); [destruct m; reflexivity|].
    rewrite IH. destruct m; reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The cases on destructed machines                                                               *)

Ltac irdi_cst := unfold HEAD, FLAGS, DICTID, TYPEDO, SYNC, DONE, DICT, BAD, MEM, STORED, LEN_, TABLE, CHECK,
                 COPY_, COPY, LENEXT, DIST, DISTEXT, MATCH, LIT, EXTRA, LEN, LENLENS, CODELENS,
                 Zlib.proof.inflate.Model.TYPE in *.

Ltac irdi_cbn := cbv beta iota zeta delta [set_i_mode set_i_last set_i_wrap set_i_havedict set_i_flags set_i_dmax set_i_check set_i_total set_i_head set_i_wbits set_i_wsize set_i_whave set_i_wnext set_i_win set_i_wdata set_i_hold set_i_bits set_i_length set_i_offset set_i_extra set_i_lencode set_i_distcode set_i_lenbits set_i_distbits set_i_ncode set_i_nlen set_i_ndist set_i_have set_i_next set_i_lens set_i_codes set_i_sane set_i_back set_i_was set_m_s set_m_h set_m_inp set_m_aout set_m_nx set_m_ow set_m_hold set_m_bits set_m_in set_m_out set_m_ret set_m_leave set_m_adler set_m_msg set_m_tin set_m_tout set_m_snx set_m_sow m_mode m_have bitsn set_mode upd_s set_leave dropbits initbits bytebits set_bad restore i_mode i_last i_wrap i_havedict i_flags i_dmax i_check i_total i_head i_wbits i_wsize i_whave i_wnext i_win i_wdata i_hold i_bits i_length i_offset i_extra i_lencode i_distcode i_lenbits i_distbits i_ncode i_nlen i_ndist i_have i_next i_lens i_codes i_sane i_back i_was m_s m_h m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave m_adler m_msg m_tin m_tout m_snx m_sow] in *.

Ltac irdi_prep :=
  intros W0 wrap src pos inp aout flush ma mb K Hmd;
  match type of Hmd with _ \/ _ => destruct Hmd as [Hmd|Hmd] | _ => idtac end;
  destruct ma as [[as_mode as_last as_wrap as_havedict as_flags as_dmax as_check as_total as_head as_wbits as_wsize as_whave as_wnext as_win as_wdata as_hold as_bits as_length as_offset as_extra as_lencode as_distcode as_lenbits as_distbits as_ncode as_nlen as_ndist as_have as_next as_lens as_codes as_sane as_back as_was] am_h am_inp am_aout am_nx am_ow am_hold am_bits am_in am_out am_ret am_leave am_adler am_msg am_tin am_tout am_snx am_sow], mb as [[bs_mode bs_last bs_wrap bs_havedict bs_flags bs_dmax bs_check bs_total bs_head bs_wbits bs_wsize bs_whave bs_wnext bs_win bs_wdata bs_hold bs_bits bs_length bs_offset bs_extra bs_lencode bs_distcode bs_lenbits bs_distbits bs_ncode bs_nlen bs_ndist bs_have bs_next bs_lens bs_codes bs_sane bs_back bs_was] bm_h bm_inp bm_aout bm_nx bm_ow bm_hold bm_bits bm_in bm_out bm_ret bm_leave bm_adler bm_msg bm_tin bm_tout bm_snx bm_sow];
  destruct K as [MR Ki Ka Kw Kh Kwa Kwb Khd];
  destruct MR as [SR ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ?];
  destruct SR as [? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? Ewb Eck _ _ _ _ _ _ _ _ _ _ _ _];
  irdi_cbn; subst;
  destruct Ewb as [?|[E|E]]; try (exfalso; irdi_cst; discriminate); try subst;
  destruct Eck as [?|[?|[[E|E] _]]]; try (exfalso; irdi_cst; discriminate); try subst.

Ltac irdi_kr :=
  apply Build_Kr; try apply Build_mrel; try apply Build_srel; intros; irdi_cbn;
  first [ reflexivity | assumption | (left; reflexivity) | (right; left; reflexivity)
        | (unfold treach_eq; split; intros; cbn [tab_entry]; split; intros; reflexivity)
        | (exfalso; unfold lenlive, decode_mode in *; irdi_cbn; irdi_cst; lia) ].

Ltac irdi_step :=
  first [ rewrite irdi_nb_eq
        | match goal with |- context [irdi_nbr ?k ?n ?i ?x ?h ?b ?l] =>
            destruct (irdi_nbr k n i x h b l) as [[[? ?] ?] ?] end
        | match goal with |- context [if ?c then _ else _] => destruct c end ].

Ltac irdi_fin := irdi_cbn; cbn [sim_post]; first [ irdi_kr | (split; [reflexivity | irdi_kr]) ].

Ltac irdi_loop s := repeat (irdi_cbn; first [s tt | irdi_step]); irdi_fin.

Ltac irdi_sub L := eapply L; solve [irdi_kr | irdi_cbn; first [reflexivity | left; reflexivity | right; reflexivity]].

Definition irdi_case_stmt (c: Z -> mst -> iout) (P: Z -> Prop) : Prop :=
  forall W0 wrap src pos inp aout flush ma mb,
    Kr W0 wrap src pos inp aout ma mb -> P (m_mode mb) ->
    sim_post W0 wrap src pos inp aout (c flush ma) (c flush mb).

Lemma irdi_typedo : irdi_case_stmt c_TYPEDO (fun md => md = Zlib.proof.inflate.Model.TYPE \/ md = TYPEDO).
Proof.
  unfold irdi_case_stmt; cbv beta. irdi_prep; unfold c_TYPEDO, needbits; irdi_loop ltac:(fun _ => fail).
Qed.

Lemma irdi_type : irdi_case_stmt c_TYPE (fun md => md = Zlib.proof.inflate.Model.TYPE).
Proof.
  unfold irdi_case_stmt; cbv beta. irdi_prep; unfold c_TYPE; irdi_loop ltac:(fun _ => irdi_sub irdi_typedo).
Qed.

Lemma irdi_dict : irdi_case_stmt c_DICT (fun md => md = DICT).
Proof.
  unfold irdi_case_stmt; cbv beta. irdi_prep; unfold c_DICT; irdi_loop ltac:(fun _ => irdi_sub irdi_type).
Qed.

Lemma irdi_dictid : irdi_case_stmt c_DICTID (fun md => md = DICTID).
Proof.
  unfold irdi_case_stmt; cbv beta. irdi_prep; unfold c_DICTID, needbits; irdi_loop ltac:(fun _ => irdi_sub irdi_dict).
Qed.

Lemma dict_sim : dict_sim_stmt.
Proof.
  intros W0 wrap src pos inp aout flush ma mb Hc K Hwa Hwb Hl Hmd.
  pose proof (sr_mode _ _ _ (mr_s _ _ (kr_rel _ _ _ _ _ _ _ _ K))) as Em.
  assert (Ea : forall md, m_mode mb = md -> m_mode ma = md) by (intros md E; unfold m_mode in *; rewrite Em; exact E).
  unfold md_dict in Hmd. destruct Hmd as [D|[D|[D|D]]].
  - rewrite (irdi_step_DICTID _ _ _ mb D), (irdi_step_DICTID _ _ _ ma (Ea _ D)).
    exact (irdi_dictid W0 wrap src pos inp aout flush ma mb K D).
  - rewrite (irdi_step_DICT _ _ _ mb D), (irdi_step_DICT _ _ _ ma (Ea _ D)).
    exact (irdi_dict W0 wrap src pos inp aout flush ma mb K D).
  - rewrite (irdi_step_TYPE _ _ _ mb D), (irdi_step_TYPE _ _ _ ma (Ea _ D)).
    exact (irdi_type W0 wrap src pos inp aout flush ma mb K D).
  - rewrite (irdi_step_TYPEDO _ _ _ mb D), (irdi_step_TYPEDO _ _ _ ma (Ea _ D)).
    exact (irdi_typedo W0 wrap src pos inp aout flush ma mb K (or_intror D)).
Qed.

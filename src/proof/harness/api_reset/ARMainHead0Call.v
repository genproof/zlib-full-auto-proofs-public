(* Law api_reset, main: the do-while body in phase 0 after the test of the four objects against NULL
   (ARMainHead0.v): offer() on both streams (fresh is still the raw struct), inflate(&used, flush)
   (SpecW.inflate_specW; ARFacts.af_inflate0 for the new invariant), `code_fresh = code_used`, the skipped
   `if (phase == 1)`, the test of Z_MEM_ERROR; the rest of the body is tail0_stmt.  Also the tactics of
   ARMainHead0*.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.api_reset.ARMainDefs Zlib.proof.harness.api_reset.ARMainKit.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.harness.api_reset.code.
Local Open Scope logic.

(* right-associate the statement, so that `x = f(...)` is a call followed by a set: forward_call on a call of a
   function returning a pointer immediately followed by `x = t'` is very slow *)
Ltac split_call := repeat match goal with |- semax _ _ (Ssequence (Ssequence _ _) _) _ => apply -> seq_assoc end.
(* forward_if whose join adds temp t = v to the current assertion *)
Ltac ifpostv t v := match goal with |- semax _ (PROPx _ (LOCALx ?Q (SEPx ?R))) _ _ =>
  forward_if (PROPx [] (LOCALx (temp t v :: Q) (SEPx R))) end.
(* a branch that cannot be taken *)
Ltac infeas := exfalso; first [ match goal with H: ?a <> ?b |- _ => solve [apply H; reflexivity] end
                              | match goal with H: _ |- _ => solve [discriminate H] end
                              | contradiction
                              | lia ].

(* `t = (p == NULL)` for a pointer p known to be valid *)
Ltac cmpz := forward; entailer!;
  try match goal with |- _ = force_val (sem_cast_i2bool (force_val (sem_cmp_pp Ceq ?p _))) =>
        destruct p; try contradiction; reflexivity end.

(* the do-while body from its 9th statement, offer(&used, ...) *)
Definition path_call0 : list nat := path_dbody ++ repeat 1%nat 8.
Definition seg_call0 : statement := ltac:(get_seg path_call0).

(* the facts after the draws of one iteration: the piece src[pos .. pos + take), room bytes of output space,
   flush *)
Definition hd0_facts (J0: J0T) (J1: J1T) (w: Z) (inp: val) (src: list Z) (va vb: val) (pos take room flush: Z)
    (za: zfields) (La: live) (zb: zfields) : Prop :=
  g_facts J0 J1 w inp src va vb /\ J0 w src pos za La /\ swfW (l_s La) /\ raw_live (Some La) = (w <? 0) /\
  zf_ok zb /\ 0 <= pos /\ 0 <= take <= Int.max_unsigned /\ pos + take <= Zlength src /\
  0 <= room <= Int.max_unsigned /\ Int.min_signed <= flush <= Int.max_signed.

(* the state after the test against NULL: the piece in the objects iu (used's) and ifr (fresh's), the output
   space in the objects ou and ofr *)
Definition call0_facts (J0: J0T) (J1: J1T) (w: Z) (inp: val) (src: list Z) (va vb: val) (pos take room flush: Z)
    (iu ifr ou ofr: val) (za: zfields) (La: live) (zb: zfields) : Prop :=
  hd0_facts J0 J1 w inp src va vb pos take room flush za La zb /\ isptr iu /\ isptr ifr /\ isptr ou /\ isptr ofr.

Definition call0_pre (gv: globals) (va vb: val) (w: Z) (inp: val) (src: list Z) (pos take room flush: Z)
    (iu ifr ou ofr: val) (za: zfields) (La: live) (zb: zfields) : environ -> mpred :=
  PROP ()
  LOCAL (temp _out_fresh ofr; temp _out_used ou; temp _in_fresh ifr; temp _in_used iu;
         temp _flush (Vint (Int.repr flush)); temp _room (Vlong (Int64.repr room));
         temp _take (Vlong (Int64.repr take)); temp _window_bits (Vint (Int.repr w));
         temp _phase (Vint (Int.repr 0)); temp _input_len (Vlong (Int64.repr (Zlength src)));
         temp _input inp; temp _read (Vlong (Int64.repr pos)); lvar _used t_z va; lvar _fresh t_z vb; gvars gv)
  SEP (istreamA gv Tsh va za Vundef (Some La); fresh_raw vb zb;
       data_at Ews (tarray tuchar take) (bytes_rep (sublist pos (pos + take) src)) iu;
       malloc_token Ews (tarray tuchar take) iu;
       data_at Ews (tarray tuchar take) (bytes_rep (sublist pos (pos + take) src)) ifr;
       malloc_token Ews (tarray tuchar take) ifr;
       data_at Ews (tarray tuchar room) (Zrepeat Vundef room) ou; malloc_token Ews (tarray tuchar room) ou;
       data_at Ews (tarray tuchar room) (Zrepeat Vundef room) ofr; malloc_token Ews (tarray tuchar room) ofr;
       malloc_token Ews (tarray tuchar (Zlength src)) inp; data_at Ews (tarray tuchar (Zlength src)) (bytes_rep src) inp;
       mem_mgr gv; zfuncs gv; tables_rep Ers gv; crc_table_at Ers gv; version_lit gv;
       hversion_at ___stringlit_api_reset_1 gv; ir_msg_lits gv; TT).

Definition call0_stmt : Prop :=
  forall {Espec: OracleKind} J0 J1 gv va vb w inp src pos take room flush iu ifr ou ofr za La zb,
  call0_facts J0 J1 w inp src va vb pos take room flush iu ifr ou ofr za La zb ->
  semax Delta_m (call0_pre gv va vb w inp src pos take room flush iu ifr ou ofr za La zb) seg_call0
    (dpost J0 J1 gv va vb w 0 inp src).

Lemma call0_of : tail0_stmt -> call0_stmt.
Proof.
  intros TAIL0. unfold call0_stmt.
  intros Espec J0 J1 gv va vb w inp src pos take room flush iu ifr ou ofr za La zb HF.
  destruct HF as (HD & Piu & Pifr & Pou & Pofr). destruct HD as (GF & HJ & Sw & Rl & Zb & Hp & Ht & Hpt & Hr & Hfl).
  pose proof GF as GF0. destruct GF as (AF & Wok & Hw & Hn & Hsb & Pinp & Pva & Pvb).
  unfold seg_call0, Delta_m, Gmain, dpost, POST_m, call0_pre. simplify_func_tycontext. abbreviate_semax.
  assert (Hdl: Zlength (sublist pos (pos + take) src) = take) by (rewrite Zlength_sublist; lia).
  assert (Hdb: bytes_ok (sublist pos (pos + take) src)) by (apply Forall_sublist; auto).
  (* offer(&used, in_used, take, out_used, room) *)
  sep_apply (istreamA_zs gv va za Vundef La). Intros.
  assert (HL: live_ok La) by assumption. assert (Za: zf_ok za) by assumption.
  forward_call (va, Tsh, iu, take, ou, room, zf_ni za, Vint (Int.repr (zf_ai za)), Vlong (Int64.repr (zf_tin za)),
                zf_no za, Vint (Int.repr (zf_ao za)), Vlong (Int64.repr (zf_tout za)), msg_val gv (zf_msg za), l_sp La,
                gv Zlib.inflate.code._zcalloc, gv Zlib.inflate.code._zcfree, nullval, Vint (Int.repr (zf_dt za)),
                adler_v (raw_live (Some La)) za Vundef, zf_res za).
  pose proof (af_head0 _ _ AF w src pos za La HJ) as Hhd.
  sep_apply (offer_fold gv va za Vundef La iu take ou room); auto; try rep_lia.
  (* offer(&fresh, in_fresh, take, out_fresh, room) *)
  rewrite fresh_raw_c.
  forward_call (vb, Tsh, ifr, take, ofr, room, zf_ni zb, Vint (Int.repr (zf_ai zb)), Vundef, zf_no zb,
                Vint (Int.repr (zf_ao zb)), Vundef, Vundef, Vundef, nullval, nullval, nullval, Vundef, Vundef, Vundef).
  assert (Efr: @data_at Zlib.units.Compress.CS Tsh t_zs
                 (zs_val ifr (Vint (Int.repr take)) Vundef ofr (Vint (Int.repr room)) Vundef Vundef Vundef nullval
                    nullval nullval Vundef Vundef Vundef) vb = fresh_raw vb (ir_call zb ifr take ofr room))
    by (rewrite fresh_raw_c; reflexivity).
  rewrite Efr. clear Efr.
  (* code_used = inflate(&used, flush) *)
  sep_apply (bufs_pre La iu take (sublist pos (pos + take) src) ou room); [lia | ].
  replace (bufs_opt (Some La)) with (bufs_opt (is_live va (Some La))) by (rewrite is_live_ptr; auto).
  assert (INOK: in_ok (ar_ib iu take (sublist pos (pos + take) src)) (sublist pos (pos + take) src))
    by (apply ar_in_ok; auto; rep_lia).
  assert (OUTOK: out_ok (ar_ob ou room) room) by (apply ar_out_ok; auto; rep_lia).
  forward_call (gv, Tsh, va, ir_call za iu take ou room, Vundef, Some La, ar_ib iu take (sublist pos (pos + take) src),
                sublist pos (pos + take) src, Some (ar_ob ou room), flush, Ers, Ers, true, true).
  { rewrite ar_in_ptr, ar_out_ptr by auto. unfold ir_call; cbn [zf_ni zf_ai zf_no].
    refine (conj eq_refl (conj (conj INOK _) eq_refl)). lia. }
  Intros vret. destruct vret as [[[r z'] st'] ow]. simpl fst in *; simpl snd in *.
  match goal with H: inflate_rel _ _ _ _ _ _ _ _ _ _ _ |- _ => rename H into REL end.
  match goal with H: raw_live st' = _ |- _ => rename H into Hrl end.
  match goal with H: match st' with Some _ => _ | None => _ end |- _ => rename H into Hsw end.
  forward.
  (* if (phase == 1) code_fresh = inflate(&fresh, flush): not in phase 0 *)
  apply semax_if_seq. forward_if; [infeas | ].
  (* if (code_used == Z_MEM_ERROR || code_fresh == Z_MEM_ERROR) return 0 *)
  split_call.
  destruct (Int.eq_dec (Int.repr r) (Int.repr (-4))) as [EM|NM].
  { ifpostv _t'19 (Vint (Int.repr 1)); [forward; entailer! | contradiction | ].
    forward_if; [ | infeas].
    forward. Exists (Int.repr 0). sep_apply a_frame_opt. sep_apply fresh_frame. entailer!. }
  ifpostv _t'19 (Vint (Int.repr 0)); [contradiction | forward; entailer!; rewrite Int.eq_false by auto; reflexivity | ].
  (* the sequence is split by hand: after forward_if, VST would replace the loop's postcondition by its normal
     part (the rest has no break, continue or return), which tail0_stmt does not give *)
  match goal with |- semax _ ?Pre _ _ => apply semax_seq with Pre end.
  { forward_if; [infeas | forward; entailer!]. }
  assert (Hm: r <> Z_MEM_ERROR) by (intro E; apply NM; rewrite E; reflexivity).
  assert (REL': inflate_rel flush va
                  (ir_call za (in_ptr (ar_ib iu take (sublist pos (pos + take) src)) 0) take (out_ptr (ar_ob ou room) 0) room)
                  (Some La) (ar_ib iu take (sublist pos (pos + take) src)) (sublist pos (pos + take) src)
                  (Some (ar_ob ou room)) r z' st' ow)
    by (rewrite ar_in_ptr, ar_out_ptr by auto; exact REL).
  destruct (af_inflate0 _ _ AF w src pos za La va flush (ar_ib iu take (sublist pos (pos + take) src))
              (sublist pos (pos + take) src) (ar_ob ou room) take room r z' st' ow
              HJ HL Za Sw ltac:(intro E; subst va; contradiction) Hp Ht Hpt Hsb Hr Hfl ltac:(discriminate) eq_refl
              REL' Hm)
    as (L' & Est & Hai & Hao & HJ').
  subst st'.
  rewrite istreamA_opt_ptr by auto. rewrite head_none by (auto; eapply af_head0; eauto).
  rewrite is_live_ptr by auto.
  sep_apply (bufs_post La iu take (sublist pos (pos + take) src) ou room ow).
  (* the rest of the body: tail0_stmt *)
  unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
  eapply semax_pre; [ | apply (TAIL0 Espec J0 J1 gv va vb w inp src pos take room iu ifr ou ofr
                                 (out_after (Zrepeat Vundef room) ow room) (Zrepeat Vundef room) r z' L'
                                 (ir_call zb ifr take ofr room))].
  { unfold mid0_at. entailer!. }
  assert (Zb': zf_ok (ir_call zb ifr take ofr room)) by (unfold zf_ok, ir_call in *; simpl; rep_lia).
  unfold mid0_facts. refine (conj GF0 (conj HJ' (conj Hsw (conj _ (conj Zb' _))))).
  - rewrite Hrl. exact Rl.
  - repeat split; auto; lia.
Qed.

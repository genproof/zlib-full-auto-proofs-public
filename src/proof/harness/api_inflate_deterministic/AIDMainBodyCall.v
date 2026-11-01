(* Law api_inflate_deterministic, main: the do-while body from its 11th statement (seg_bcall): inflate(&first),
   inflate(&second), the test of Z_MEM_ERROR (return 0), then the rest of the body (AIDMainKit.tail_stmt) from
   mid_at, with AIDFacts.df_inflate for the facts.  The assertion before it (bc_pre) is the one AIDMainBody.v
   reaches after the two set_buffer() calls. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.EnvBodies.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.api_inflate_deterministic.AIDMainDefs.
Require Import Zlib.proof.harness.api_inflate_deterministic.AIDMainKit.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.harness.api_inflate_deterministic.code.
Local Open Scope logic.

(* VST's after_forward_call simplifies remove_localdef_temp with `simpl rlt_ident_eq`, which runs away on main's
   identifiers (_input against _input_len); each identifier comparison is decided by vm_compute instead.  Also
   used by AIDMainBodyNull.v, AIDMainBodyOff.v and AIDMainBody.v, which Require this file. *)
Ltac aid_rlt_fix u :=
  lazymatch u with
  | context C [rlt_ident_eq ?a ?b] =>
      let v := eval vm_compute in (rlt_ident_eq a b) in
      let u2 := context C [v] in aid_rlt_fix u2
  | _ => u
  end.

Ltac simplify_remove_localdef_temp ::=
  match goal with |- context [remove_localdef_temp ?i ?L] =>
    let u := constr:(remove_localdef_temp i L) in
    let u' := eval lazy delta [remove_localdef_temp] beta iota in u in
    let u' := aid_rlt_fix u' in
    let u' := eval lazy beta iota in u' in
    let u' := eval lazy zeta in u' in
    change u with u'
  end.

(* the do-while body from its 11th statement, inflate(&first) *)
Definition path_bcall : list nat := path_dbody ++ repeat 1%nat 10.
Definition seg_bcall : statement := ltac:(get_seg path_bcall).

(* after the two set_buffer() calls: both streams were offered the piece d = src[pos .. pos + take) (first in
   object ia, second in ib) and room bytes of output space (objects oa, ob) *)
Definition bc_pre (gv: globals) (va vb: val) (w: Z) (inp: val) (src: list Z) (pos take room flush: Z)
    (ia ib oa ob: val) (za: zfields) (La: live) (zb: zfields) (Lb: live) : environ -> mpred :=
  PROP ()
  LOCAL (temp _out_second ob; temp _out_first oa; temp _in_second ib; temp _in_first ia;
         temp _flush (Vint (Int.repr flush)); temp _out_size (Vlong (Int64.repr room));
         temp _take (Vlong (Int64.repr take));
         temp _window_bits (Vint (Int.repr w));
         temp _input_len (Vlong (Int64.repr (Zlength src))); temp _input inp;
         temp _read (Vlong (Int64.repr pos)); lvar _first t_z va; lvar _second t_z vb; gvars gv)
  SEP (istreamA_opt gv Tsh va (ir_call za ia take oa room) Vundef (Some La); head_opt (is_live va (Some La));
       bufs_opt (Some La) (aid_ib ia take (sublist pos (pos + take) src)) (Some (aid_ob oa room)) [] true true;
       istreamA_opt gv Tsh vb (ir_call zb ib take ob room) Vundef (Some Lb); head_opt (is_live vb (Some Lb));
       bufs_opt (Some Lb) (aid_ib ib take (sublist pos (pos + take) src)) (Some (aid_ob ob room)) [] true true;
       malloc_token Ews (tarray tuchar (Zlength src)) inp; data_at Ews (tarray tuchar (Zlength src)) (bytes_rep src) inp;
       mem_mgr gv; zfuncs gv; tables_rep Ers gv; crc_table_at Ers gv; version_lit gv;
       hversion_at ___stringlit_api_inflate_deterministic_1 gv; ir_msg_lits gv; TT).

Definition bc_facts (J: JT) (w: Z) (inp: val) (src: list Z) (va vb: val) (pos take room flush: Z)
    (ia ib oa ob: val) (za: zfields) (La: live) (zb: zfields) (Lb: live) : Prop :=
  g_facts J w inp src va vb /\
  J w src pos za La zb Lb /\ swfW (l_s La) /\ swfW (l_s Lb) /\
  raw_live (Some La) = (w <? 0) /\ raw_live (Some Lb) = (w <? 0) /\
  0 <= pos /\ 0 <= take <= Int.max_unsigned /\ pos + take <= Zlength src /\ 0 <= room <= Int.max_unsigned /\
  Int.min_signed <= flush <= Int.max_signed /\ zf_ok za /\ zf_ok zb /\ live_ok La /\ live_ok Lb /\
  isptr ia /\ isptr ib /\ isptr oa /\ isptr ob.

(* inflate() on a live stream leaves it live *)
Lemma aid_rel_some flush strmp z L ib inp ob r z' st' ow:
  inflate_rel flush strmp z (Some L) ib inp ob r z' st' ow -> exists L', st' = Some L'.
Proof.
  intros [(_ & _ & _ & E & _) | (_ & L0 & o & res & winp & _ & _ & _ & _ & _ & _ & _ & _ & E)]; eauto.
Qed.

Ltac infeas1 := exfalso; first [ match goal with H: ?a <> ?b |- _ => solve [apply H; reflexivity] end
                               | match goal with H: _ |- _ => solve [discriminate H] end
                               | contradiction | lia ].

(* forward_if whose join adds temp t = v to the current assertion *)
Ltac ifpost1 t v := match goal with |- semax _ (PROPx _ (LOCALx ?Q (SEPx ?R))) _ _ =>
  forward_if (PROPx [] (LOCALx (temp t v :: Q) (SEPx R))) end.

(* `return 0` with both streams given back to the stack frame *)
Ltac a_frame_at v := match goal with |- context [istreamA_opt ?g Tsh v ?z ?a ?s] =>
  sep_apply (a_frame_opt g v z a s); auto end.
Ltac ret_mem va vb := forward; Exists (Int.repr 0); a_frame_at va; a_frame_at vb; entailer!.

Lemma body_call {Espec: OracleKind} J gv va vb w inp src pos take room flush ia ib oa ob za La zb Lb:
  tail_stmt ->
  bc_facts J w inp src va vb pos take room flush ia ib oa ob za La zb Lb ->
  semax Delta_m (bc_pre gv va vb w inp src pos take room flush ia ib oa ob za La zb Lb) seg_bcall
    (dpost J gv va vb w inp src).
Proof.
  intros TAIL HF.
  destruct HF as (GF & HJ & SWa & SWb & Rwa & Rwb & Hpos & Htk & Hpt & Hroom & Hfl & Zoa & Zob & Loa & Lob
                  & Pia & Pib & Poa & Pob).
  pose proof GF as GF0. destruct GF as (AF & Wok & Hw & Hn & Hsb & Pinp & Pva & Pvb).
  unfold bc_pre, seg_bcall, dpost, Delta_m, Gmain, POST_m. simplify_func_tycontext. abbreviate_semax.
  set (d := sublist pos (pos + take) src) in *.
  assert (Hdl: Zlength d = take) by (unfold d; rewrite Zlength_sublist; lia).
  assert (Hdb: bytes_ok d) by (unfold d; apply Forall_sublist; auto).
  assert (INa: in_ok (aid_ib ia take d) d) by (apply aid_in_ok; auto; rep_lia).
  assert (INb: in_ok (aid_ib ib take d) d) by (apply aid_in_ok; auto; rep_lia).
  assert (OUa: out_ok (aid_ob oa room) room) by (apply aid_out_ok; auto; rep_lia).
  assert (OUb: out_ok (aid_ob ob room) room) by (apply aid_out_ok; auto; rep_lia).
  (* code_first = inflate(&first, flush) *)
  forward_call (gv, Tsh, va, ir_call za ia take oa room,
                Vundef, Some La, aid_ib ia take d, d, Some (aid_ob oa room), flush, Ers, Ers, true, true).
  { rewrite (is_live_ptr va) by auto. cancel. }
  { unfold ir_call; simpl zf_ni; simpl zf_no; simpl zf_ai; simpl zf_ao.
    rewrite aid_in_ptr, aid_out_ptr by auto.
    exact (conj eq_refl (conj (conj INa (eq_sym Hdl)) eq_refl)). }
  Intros vret. destruct vret as [[[ra za'] sta'] owa]. cbn [fst snd] in *.
  match goal with H: inflate_rel _ _ _ _ _ _ _ _ _ _ _ |- _ => rename H into RELa end.
  destruct (aid_rel_some _ _ _ _ _ _ _ _ _ _ _ RELa) as [La' ->].
  match goal with H: raw_live (Some La') = _ |- _ => rename H into Rwa' end.
  match goal with H: swfW (l_s La') |- _ => rename H into SWa' end.
  (* code_second = inflate(&second, flush) *)
  forward_call (gv, Tsh, vb, ir_call zb ib take ob room,
                Vundef, Some Lb, aid_ib ib take d, d, Some (aid_ob ob room), flush, Ers, Ers, true, true).
  { rewrite (is_live_ptr vb) by auto. cancel. }
  { unfold ir_call; simpl zf_ni; simpl zf_no; simpl zf_ai; simpl zf_ao.
    rewrite aid_in_ptr, aid_out_ptr by auto.
    exact (conj eq_refl (conj (conj INb (eq_sym Hdl)) eq_refl)). }
  Intros vret. destruct vret as [[[rb zb'] stb'] owb]. cbn [fst snd] in *.
  match goal with H: inflate_rel _ vb _ _ _ _ _ _ _ _ _ |- _ => rename H into RELb end.
  destruct (aid_rel_some _ _ _ _ _ _ _ _ _ _ _ RELb) as [Lb' ->].
  match goal with H: raw_live (Some Lb') = _ |- _ => rename H into Rwb' end.
  match goal with H: swfW (l_s Lb') |- _ => rename H into SWb' end.
  assert (RELa': inflate_rel flush va (ir_call za (in_ptr (aid_ib ia take d) 0) take (out_ptr (aid_ob oa room) 0) room)
                   (Some La) (aid_ib ia take d) d (Some (aid_ob oa room)) ra za' (Some La') owa)
    by (rewrite aid_in_ptr, aid_out_ptr by auto; exact RELa).
  assert (RELb': inflate_rel flush vb (ir_call zb (in_ptr (aid_ib ib take d) 0) take (out_ptr (aid_ob ob room) 0) room)
                   (Some Lb) (aid_ib ib take d) d (Some (aid_ob ob room)) rb zb' (Some Lb') owb)
    by (rewrite aid_in_ptr, aid_out_ptr by auto; exact RELb).
  clear RELa RELb.
  (* if (code_first == Z_MEM_ERROR || code_second == Z_MEM_ERROR) return 0; *)
  destruct (Int.eq_dec (Int.repr ra) (Int.repr Z_MEM_ERROR)) as [Ea | Na].
  { ifpost1 _t'23 (Vint (Int.repr 1)); [forward; entailer! | contradiction | ].
    forward_if; [ret_mem va vb | infeas1]. }
  destruct (Int.eq_dec (Int.repr rb) (Int.repr Z_MEM_ERROR)) as [Eb | Nb].
  { ifpost1 _t'23 (Vint (Int.repr 1)); [contradiction | forward; entailer!; rewrite Eb; reflexivity | ].
    forward_if; [ret_mem va vb | infeas1]. }
  ifpost1 _t'23 (Vint (Int.repr 0));
    [contradiction | forward; entailer!; rewrite (Int.eq_false (Int.repr rb) (Int.repr (-(4))) Nb); reflexivity | ].
  (* the rest of the body keeps the do-while's postcondition (forward would turn it into a sequential one) *)
  match goal with |- semax _ ?P (Ssequence _ _) _ => apply semax_seq with P end;
    [ forward_if; [infeas1 | forward; entailer!] | ].
  assert (Hra: ra <> Z_MEM_ERROR) by (intro E; apply Na; rewrite E; reflexivity).
  assert (Hrb: rb <> Z_MEM_ERROR) by (intro E; apply Nb; rewrite E; reflexivity).
  destruct (df_inflate _ AF w src pos za La zb Lb va vb flush (aid_ib ia take d) (aid_ib ib take d) d
              (aid_ob oa room) (aid_ob ob room) take room ra za' (Some La') owa rb zb' (Some Lb') owb
              HJ Loa Lob Zoa Zob SWa SWb ltac:(destruct va; try contradiction; discriminate)
              ltac:(destruct vb; try contradiction; discriminate) Hpos Htk Hpt Hsb Hroom Hfl
              ltac:(discriminate) ltac:(discriminate) eq_refl RELa' Hra RELb' Hrb)
    as (La'' & Lb'' & Ea' & Eb' & Erab & Eai & Eao & Eow & How & Etin & Etout & Edt & Emsg & Eadl & Hai & Hao & HJ').
  injection Ea' as <-. injection Eb' as <-. subst rb owb.
  destruct (df_head _ AF _ _ _ _ _ _ _ HJ') as [Hha Hhb].
  rewrite !istreamA_opt_ptr, !head_none, !is_live_ptr by auto.
  sep_apply (bufs_post La ia take d oa room owa).
  sep_apply (bufs_post Lb ib take d ob room owa).
  unfold abbreviate in MORE_COMMANDS. subst MORE_COMMANDS.
  eapply semax_pre; [ | apply (TAIL _ J gv va vb w inp src pos take room ia ib oa ob ra za' La' zb' Lb' owa) ].
  { unfold mid_at. entailer!. }
  unfold mid_facts.
  refine (conj GF0 (conj HJ' (conj SWa' (conj SWb' _)))).
  rewrite Rwa', Rwb'.
  repeat match goal with |- _ /\ _ => split end; auto; lia.
Qed.

(* Law api_reset, main: the do-while body in phase 1 from its 11th statement (seg_h1c): inflate(&used),
   code_fresh = code_used, `if (phase == 1) code_fresh = inflate(&fresh)`, the test of Z_MEM_ERROR (return 0),
   then the rest of the body (ARMainKit.tail1_stmt) from mid1_at, with ARFacts.af_inflate1 for the facts.
   The assertion before it (h1c_pre) is the one ARMainHead1.v reaches after the two offer() calls. *)
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

(* the do-while body from its 11th statement, inflate(&used) *)
Definition path_h1c : list nat := path_dbody ++ repeat 1%nat 10.
Definition seg_h1c : statement := ltac:(get_seg path_h1c).

(* after the two offer() calls: both streams were offered the piece d = src[pos .. pos + take) (used in
   object iu, fresh in ifr) and room bytes of output space (objects ou, ofr) *)
Definition h1c_pre (gv: globals) (va vb: val) (w: Z) (inp: val) (src: list Z) (pos take room flush: Z)
    (iu ifr ou ofr: val) (za: zfields) (La: live) (zb: zfields) (Lb: live) : environ -> mpred :=
  PROP ()
  LOCAL (temp _out_fresh ofr; temp _out_used ou; temp _in_fresh ifr; temp _in_used iu;
         temp _flush (Vint (Int.repr flush)); temp _room (Vlong (Int64.repr room));
         temp _take (Vlong (Int64.repr take));
         temp _window_bits (Vint (Int.repr w)); temp _phase (Vint (Int.repr 1));
         temp _input_len (Vlong (Int64.repr (Zlength src))); temp _input inp;
         temp _read (Vlong (Int64.repr pos)); lvar _used t_z va; lvar _fresh t_z vb; gvars gv)
  SEP (istreamA_opt gv Tsh va (ir_call za iu take ou room) Vundef (Some La); head_opt (is_live va (Some La));
       bufs_opt (Some La) (ar_ib iu take (sublist pos (pos + take) src)) (Some (ar_ob ou room)) [] true true;
       istreamA_opt gv Tsh vb (ir_call zb ifr take ofr room) Vundef (Some Lb); head_opt (is_live vb (Some Lb));
       bufs_opt (Some Lb) (ar_ib ifr take (sublist pos (pos + take) src)) (Some (ar_ob ofr room)) [] true true;
       malloc_token Ews (tarray tuchar (Zlength src)) inp; data_at Ews (tarray tuchar (Zlength src)) (bytes_rep src) inp;
       mem_mgr gv; zfuncs gv; tables_rep Ers gv; crc_table_at Ers gv; version_lit gv;
       hversion_at ___stringlit_api_reset_1 gv; ir_msg_lits gv; TT).

Definition h1c_facts (J0: J0T) (J1: J1T) (w: Z) (inp: val) (src: list Z) (va vb: val) (pos take room flush: Z)
    (iu ifr ou ofr: val) (za: zfields) (La: live) (zb: zfields) (Lb: live) : Prop :=
  g_facts J0 J1 w inp src va vb /\
  J1 w src pos za La zb Lb /\ swfW (l_s La) /\ swfW (l_s Lb) /\
  raw_live (Some La) = (w <? 0) /\ raw_live (Some Lb) = (w <? 0) /\
  0 <= pos /\ 0 <= take <= Int.max_unsigned /\ pos + take <= Zlength src /\ 0 <= room <= Int.max_unsigned /\
  Int.min_signed <= flush <= Int.max_signed /\ zf_ok za /\ zf_ok zb /\ live_ok La /\ live_ok Lb /\
  isptr iu /\ isptr ifr /\ isptr ou /\ isptr ofr.

(* inflate() on a live stream leaves it live *)
Lemma ar_rel_some flush strmp z L ib inp ob r z' st' ow:
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

Lemma h1_call {Espec: OracleKind} J0 J1 gv va vb w inp src pos take room flush iu ifr ou ofr za La zb Lb:
  tail1_stmt ->
  h1c_facts J0 J1 w inp src va vb pos take room flush iu ifr ou ofr za La zb Lb ->
  semax Delta_m (h1c_pre gv va vb w inp src pos take room flush iu ifr ou ofr za La zb Lb) seg_h1c
    (dpost J0 J1 gv va vb w 1 inp src).
Proof.
  intros TAIL HF.
  pose proof HF as HF0.
  destruct HF as (GF & HJ & SWa & SWb & Rwa & Rwb & Hpos & Htk & Hpt & Hroom & Hfl & Zoa & Zob & Loa & Lob
                  & Piu & Pifr & Pou & Pofr).
  pose proof GF as GF0. destruct GF as (AF & Wok & Hw & Hn & Hsb & Pinp & Pva & Pvb).
  unfold h1c_pre, seg_h1c, dpost, Delta_m, Gmain, POST_m. simplify_func_tycontext. abbreviate_semax.
  set (d := sublist pos (pos + take) src) in *.
  assert (Hdl: Zlength d = take) by (unfold d; rewrite Zlength_sublist; lia).
  assert (Hdb: bytes_ok d) by (unfold d; apply Forall_sublist; auto).
  assert (INa: in_ok (ar_ib iu take d) d) by (apply ar_in_ok; auto; rep_lia).
  assert (INb: in_ok (ar_ib ifr take d) d) by (apply ar_in_ok; auto; rep_lia).
  assert (OUa: out_ok (ar_ob ou room) room) by (apply ar_out_ok; auto; rep_lia).
  assert (OUb: out_ok (ar_ob ofr room) room) by (apply ar_out_ok; auto; rep_lia).
  (* code_used = inflate(&used, flush) *)
  forward_call (gv, Tsh, va, ir_call za iu take ou room,
                Vundef, Some La, ar_ib iu take d, d, Some (ar_ob ou room), flush, Ers, Ers, true, true).
  { rewrite (is_live_ptr va) by auto. cancel. }
  { unfold ir_call; simpl zf_ni; simpl zf_no; simpl zf_ai; simpl zf_ao.
    rewrite ar_in_ptr, ar_out_ptr by auto.
    exact (conj eq_refl (conj (conj INa (eq_sym Hdl)) eq_refl)). }
  Intros vret. destruct vret as [[[ra za'] sta'] owa]. cbn [fst snd] in *.
  match goal with H: inflate_rel _ _ _ _ _ _ _ _ _ _ _ |- _ => rename H into RELa end.
  destruct (ar_rel_some _ _ _ _ _ _ _ _ _ _ _ RELa) as [La' ->].
  match goal with H: raw_live (Some La') = _ |- _ => rename H into Rwa' end.
  forward.
  (* code_fresh = inflate(&fresh, flush) *)
  forward_if (EX rb: Z, EX zb': zfields, EX Lb': live, EX owb: list Z,
    PROP (inflate_rel flush vb (ir_call zb ifr take ofr room)
            (Some Lb) (ar_ib ifr take d) d (Some (ar_ob ofr room)) rb zb' (Some Lb') owb;
          raw_live (Some Lb') = raw_live (Some Lb); swfW (l_s Lb'))
    LOCAL (temp _code_fresh (Vint (Int.repr rb)); temp _code_used (Vint (Int.repr ra));
           temp _out_fresh ofr; temp _out_used ou; temp _in_fresh ifr; temp _in_used iu;
           temp _flush (Vint (Int.repr flush)); temp _room (Vlong (Int64.repr room));
           temp _take (Vlong (Int64.repr take));
           temp _window_bits (Vint (Int.repr w)); temp _phase (Vint (Int.repr 1));
           temp _input_len (Vlong (Int64.repr (Zlength src))); temp _input inp;
           temp _read (Vlong (Int64.repr pos)); lvar _used t_z va; lvar _fresh t_z vb; gvars gv)
    SEP (istreamA_opt gv Tsh va za' Vundef (Some La'); head_opt (is_live va (Some La'));
         bufs_opt (is_live va (Some La)) (ar_ib iu take d) (Some (ar_ob ou room)) owa true true;
         istreamA_opt gv Tsh vb zb' Vundef (Some Lb'); head_opt (is_live vb (Some Lb'));
         bufs_opt (is_live vb (Some Lb)) (ar_ib ifr take d) (Some (ar_ob ofr room)) owb true true;
         malloc_token Ews (tarray tuchar (Zlength src)) inp;
         data_at Ews (tarray tuchar (Zlength src)) (bytes_rep src) inp;
         mem_mgr gv; zfuncs gv; tables_rep Ers gv; crc_table_at Ers gv; version_lit gv;
         hversion_at ___stringlit_api_reset_1 gv; ir_msg_lits gv; TT)).
  { forward_call (gv, Tsh, vb, ir_call zb ifr take ofr room,
                  Vundef, Some Lb, ar_ib ifr take d, d, Some (ar_ob ofr room), flush, Ers, Ers, true, true).
    { rewrite (is_live_ptr vb) by auto. cancel. }
    { unfold ir_call; simpl zf_ni; simpl zf_no; simpl zf_ai; simpl zf_ao.
      rewrite ar_in_ptr, ar_out_ptr by auto.
      exact (conj eq_refl (conj (conj INb (eq_sym Hdl)) eq_refl)). }
    Intros vret. destruct vret as [[[rb zb'] stb'] owb]. cbn [fst snd] in *.
    match goal with H: inflate_rel _ _ _ _ _ _ _ _ _ _ _ |- _ => rename H into RELb end.
    destruct (ar_rel_some _ _ _ _ _ _ _ _ _ _ _ RELb) as [Lb' ->].
    forward.
    Exists rb zb' Lb' owb. entailer!. }
  { infeas1. }
  Intros rb zb' Lb' owb.
  match goal with H: inflate_rel _ vb _ _ _ _ _ _ _ _ _ |- _ => rename H into RELb end.
  match goal with H: raw_live (Some Lb') = _ |- _ => rename H into Rwb' end.
  assert (RELa': inflate_rel flush va (ir_call za (in_ptr (ar_ib iu take d) 0) take (out_ptr (ar_ob ou room) 0) room)
                   (Some La) (ar_ib iu take d) d (Some (ar_ob ou room)) ra za' (Some La') owa)
    by (rewrite ar_in_ptr, ar_out_ptr by auto; exact RELa).
  assert (RELb': inflate_rel flush vb (ir_call zb (in_ptr (ar_ib ifr take d) 0) take (out_ptr (ar_ob ofr room) 0) room)
                   (Some Lb) (ar_ib ifr take d) d (Some (ar_ob ofr room)) rb zb' (Some Lb') owb)
    by (rewrite ar_in_ptr, ar_out_ptr by auto; exact RELb).
  clear RELa RELb.
  (* if (code_used == Z_MEM_ERROR || code_fresh == Z_MEM_ERROR) return 0; *)
  destruct (Int.eq_dec (Int.repr ra) (Int.repr Z_MEM_ERROR)) as [Ea | Na].
  { ifpost1 _t'19 (Vint (Int.repr 1)); [forward; entailer! | contradiction | ].
    forward_if; [ret_mem va vb | infeas1]. }
  destruct (Int.eq_dec (Int.repr rb) (Int.repr Z_MEM_ERROR)) as [Eb | Nb].
  { ifpost1 _t'19 (Vint (Int.repr 1)); [contradiction | forward; entailer!; rewrite Eb; reflexivity | ].
    forward_if; [ret_mem va vb | infeas1]. }
  ifpost1 _t'19 (Vint (Int.repr 0));
    [contradiction | forward; entailer!; rewrite (Int.eq_false (Int.repr rb) (Int.repr (-(4))) Nb); reflexivity | ].
  (* the rest of the body keeps the do-while's postcondition (forward would turn it into a sequential one) *)
  match goal with |- semax _ ?P (Ssequence _ _) _ => apply semax_seq with P end;
    [ forward_if; [infeas1 | forward; entailer!] | ].
  assert (Hra: ra <> Z_MEM_ERROR) by (intro E; apply Na; rewrite E; reflexivity).
  assert (Hrb: rb <> Z_MEM_ERROR) by (intro E; apply Nb; rewrite E; reflexivity).
  destruct (af_inflate1 _ _ AF w src pos za La zb Lb va vb flush (ar_ib iu take d) (ar_ib ifr take d) d
              (ar_ob ou room) (ar_ob ofr room) take room ra za' (Some La') owa rb zb' (Some Lb') owb
              HJ Loa Lob Zoa Zob SWa SWb ltac:(destruct va; try contradiction; discriminate)
              ltac:(destruct vb; try contradiction; discriminate) Hpos Htk Hpt Hsb Hroom Hfl
              ltac:(discriminate) ltac:(discriminate) eq_refl RELa' Hra RELb' Hrb)
    as (La'' & Lb'' & Ea' & Eb' & Erab & Eai & Eao & Eow & How & Etin & Etout & Edt & Emsg & Eadl & Hai & Hao & HJ').
  injection Ea' as <-. injection Eb' as <-. subst rb owb.
  destruct (af_head1 _ _ AF _ _ _ _ _ _ _ HJ') as [Hha Hhb].
  rewrite !istreamA_opt_ptr, !head_none, !is_live_ptr by auto.
  sep_apply (bufs_post La iu take d ou room owa).
  sep_apply (bufs_post Lb ifr take d ofr room owa).
  unfold abbreviate in MORE_COMMANDS. subst MORE_COMMANDS.
  eapply semax_pre; [ | apply (TAIL _ J0 J1 gv va vb w inp src pos take room iu ifr ou ofr ra za' La' zb' Lb' owa) ].
  { unfold mid1_at. entailer!. }
  unfold mid1_facts.
  refine (conj GF0 (conj HJ' (conj H1 (conj H2 _)))).
  rewrite Rwa', Rwb'.
  repeat match goal with |- _ /\ _ => split end; auto; lia.
Qed.

(* Law rfc_stored, main: statements 32-34, the do-while of inflate() calls (avail_in / avail_out clipped to
   UINT_MAX, any flush, `return 0` on Z_MEM_ERROR, gp_assert of the return code; RSFacts.rf_inflate) and the
   final check next_out == out + data_len && bytes_eq(out, expected, data_len) against the copy of the data. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.EnvBodies.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.SpecW.
Require Zlib.proof.adler32.Spec.
Require Zlib.proof.crc32.Spec.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.rfc_stored.RSLawCS.
Require Import Zlib.proof.harness.rfc_stored.RSGlobals.
Require Import Zlib.proof.harness.rfc_stored.RSFacts.
Require Import Zlib.proof.harness.rfc_stored.RSMainKit.
Require Import Zlib.harness.rfc_stored.code.
Local Open Scope logic.

(* the parts of statements 32-34: the do-while's body, and what follows the loop (the final check, `return 0`) *)
Definition rs_loop_body : statement :=
  ltac:(let x := eval cbv delta [rs_seg32] in rs_seg32 in
        match x with Ssequence (Sloop ?b _) _ => exact b end).
Definition rs_final : statement :=
  ltac:(let x := eval cbv delta [rs_seg32] in rs_seg32 in
        match x with Ssequence (Sloop _ _) ?r => exact r end).

(* the loop's increment: `if (!(code != Z_STREAM_END)) break;` *)
Definition rs_loop_incr : statement :=
  ltac:(let x := eval cbv delta [rs_seg32] in rs_seg32 in
        match x with Ssequence (Sloop _ ?i) _ => exact i end).

Lemma rs_seg32_eq : rs_seg32 = Ssequence (Sloop rs_loop_body rs_loop_incr) rs_final.
Proof. reflexivity. Qed.

(* at the end of the do-while's body: the invariant for the state after the call, with code = the call's return
   code (Z_OK, Z_BUF_ERROR or Z_STREAM_END; at Z_STREAM_END all the data is out) *)
Definition rs_cont (P: list Z -> list Z -> Z -> list Z -> zfields -> live -> Prop) (gv: globals) (vs vwb: val)
    (stp: val) (src: list Z) (dp: val) (d: list Z) (op ep: val) : environ -> mpred :=
  EX pos: Z, EX outv: list Z, EX z: zfields, EX L: live, EX ai: Z, EX ao: Z, EX r: Z,
  PROP (P src d pos outv z L; zf_ok z; swfW (l_s L); 0 <= ai <= Int.max_unsigned; 0 <= ao <= Int.max_unsigned;
        r = Z_OK \/ r = Z_BUF_ERROR \/ r = Z_STREAM_END; r = Z_STREAM_END -> outv = d)
  LOCAL (temp _code (Vint (Int.repr r)); temp _stream stp; temp _stream_len (Vlong (Int64.repr (Zlength src)));
         temp _data dp; temp _data_len (Vlong (Int64.repr (Zlength d))); temp _out op; temp _expected ep;
         lvar _window_bits (tarray tint 3) vwb; lvar _strm (Tstruct _z_stream_s noattr) vs; gvars gv)
  SEP (istreamA gv Tsh vs (rs_set_call z (offset_val pos stp) ai (offset_val (Zlength outv) op) ao) Vundef (Some L);
       data_at_ Tsh (tarray tint 3) vwb;
       mem_mgr gv; zfuncs gv; tables_rep Ers gv; Zlib.proof.crc32.Spec.crc_table_at Ers gv; version_lit gv;
       rs_hversion_lit gv;
       malloc_token Ews (tarray tuchar (Zlength src)) stp;
       data_at Ews (tarray tuchar (Zlength src)) (bytes_rep src) stp;
       malloc_token Ews (tarray tuchar (Zlength d)) dp;
       data_at Ews (tarray tuchar (Zlength d)) (bytes_rep d) dp;
       malloc_token Ews (tarray tuchar (Zlength d)) op;
       data_at Ews (tarray tuchar (Zlength d)) (bytes_rep outv ++ Zrepeat Vundef (Zlength d - Zlength outv)) op;
       rs_copy ep (Zlength d) d).

(* after the loop (inflate() returned Z_STREAM_END): next_out = out + data_len, the output object holds d *)
Definition rs_done (gv: globals) (vs vwb: val) (stp: val) (src: list Z) (dp: val) (d: list Z) (op ep: val)
    : environ -> mpred :=
  EX z: zfields, EX L: live,
  PROP (zf_no z = offset_val (Zlength d) op)
  LOCAL (temp _stream stp; temp _stream_len (Vlong (Int64.repr (Zlength src)));
         temp _data dp; temp _data_len (Vlong (Int64.repr (Zlength d))); temp _out op; temp _expected ep;
         lvar _window_bits (tarray tint 3) vwb; lvar _strm (Tstruct _z_stream_s noattr) vs; gvars gv)
  SEP (istreamA gv Tsh vs z Vundef (Some L);
       data_at_ Tsh (tarray tint 3) vwb;
       mem_mgr gv; zfuncs gv; tables_rep Ers gv; Zlib.proof.crc32.Spec.crc_table_at Ers gv; version_lit gv;
       rs_hversion_lit gv;
       malloc_token Ews (tarray tuchar (Zlength src)) stp;
       data_at Ews (tarray tuchar (Zlength src)) (bytes_rep src) stp;
       malloc_token Ews (tarray tuchar (Zlength d)) dp;
       data_at Ews (tarray tuchar (Zlength d)) (bytes_rep d) dp;
       malloc_token Ews (tarray tuchar (Zlength d)) op;
       data_at Ews (tarray tuchar (Zlength d)) (bytes_rep d) op;
       rs_copy ep (Zlength d) d).

(* the call's buffers: the stream object (all of src, inflate() reads from pos on) and the output object (the
   output so far, then room) as inflate()'s InBuf / OutBuf, at the inflate unit's compspecs *)
Lemma rs_bufs_pre L stp src pos op n (c: list val) k:
  Zlength c = n -> 0 <= k <= n ->
  data_at Ews (tarray tuchar (Zlength src)) (bytes_rep src) stp *
  malloc_token Ews (tarray tuchar (Zlength src)) stp *
  data_at Ews (tarray tuchar n) c op * malloc_token Ews (tarray tuchar n) op
  |-- bufs_opt (Some L) (InBuf Ews stp pos (Zlength src) (bytes_rep src)) (Some (OutBuf Ews op k n c)) [] true true.
Proof.
  unfold bufs_opt, in_rep, out_opt, out_rep, in_tok, out_tok.
  intros Hc Hk. rewrite <- (rs_tok_i Ews n op), <- (rs_tok_i Ews (Zlength src) stp).
  rewrite Zlength_nil, Z.add_0_r. simpl app.
  rewrite <- (sublist_split 0 k n c), sublist_same by lia. cancel.
Qed.

Lemma rs_bufs_post L stp src pos op n (c: list val) k ow:
  bufs_opt (Some L) (InBuf Ews stp pos (Zlength src) (bytes_rep src)) (Some (OutBuf Ews op k n c)) ow true true
  |-- data_at Ews (tarray tuchar (Zlength src)) (bytes_rep src) stp *
      malloc_token Ews (tarray tuchar (Zlength src)) stp *
      data_at Ews (tarray tuchar n) (sublist 0 k c ++ byte_vals ow ++ sublist (k + Zlength ow) n c) op *
      malloc_token Ews (tarray tuchar n) op.
Proof.
  unfold bufs_opt, in_rep, out_opt, out_rep, in_tok, out_tok.
  rewrite (rs_tok_i Ews n op), (rs_tok_i Ews (Zlength src) stp). cancel.
Qed.

(* `len - (size_t) (p - base)` for p = base + k inside the object: len - k *)
Lemma rs_sameblock p k: isptr p -> is_true (sameblock (offset_val k p) p).
Proof. intros Pp. destruct p; try contradiction. simpl. destruct (peq b b); [auto | contradiction]. Qed.

Lemma rs_sub_pp b i k n: 0 <= k <= n -> n < 2 ^ 63 ->
  force_val (sem_sub_default tulong tulong (Vlong (Int64.repr n))
    (force_val (sem_sub_pp tuchar (Vptr b (Ptrofs.add i (Ptrofs.repr k))) (Vptr b i)))) =
  Vlong (Int64.repr (n - k)).
Proof.
  intros Hk Hn. unfold sem_sub_pp. simpl. rewrite if_true by auto.
  rewrite Ptrofs.sub_add_l, Ptrofs.sub_idem, Ptrofs.add_zero_l.
  unfold Ptrofs.divs. rewrite (Ptrofs.signed_repr 1) by rep_lia.
  rewrite (Ptrofs.signed_repr k) by rep_lia. rewrite Z.quot_1_r.
  simpl. unfold sem_sub_default, Cop.sem_binarith; simpl. unfold Ptrofs.to_int64.
  rewrite Ptrofs.unsigned_repr by rep_lia. rewrite sub64_repr. reflexivity.
Qed.

(* the struct after main's four stores, as istreamA *)
Lemma rs_fold_call gv vs z L ni ai no ao av:
  zf_ok (rs_set_call z ni ai no ao) -> live_ok L ->
  data_at Tsh t_zsl (ni, (Vint (Int.repr ai), (Vlong (Int64.repr (zf_tin z)), (no, (Vint (Int.repr ao),
    (Vlong (Int64.repr (zf_tout z)), (msg_val gv (zf_msg z), (l_sp L, (gv Zlib.inflate.code._zcalloc,
    (gv Zlib.inflate.code._zcfree, (nullval, (Vint (Int.repr (zf_dt z)),
    (adler_v (raw_live (Some L)) (rs_set_call z ni ai no ao) av, zf_res z))))))))))))) vs * state_mem gv vs L
  |-- istreamA gv Tsh vs (rs_set_call z ni ai no ao) av (Some L).
Proof.
  intros. eapply derives_trans; [ | apply rs_istreamA_fold; auto]. unfold rs_tup.
  cbn [rs_set_call zf_ni zf_ai zf_tin zf_no zf_ao zf_tout zf_msg zf_dt zf_adler zf_res]. apply derives_refl.
Qed.

(* the input src[pos .. pos + ain) inside the stream object, the room behind outv in the output object *)
Lemma rs_in_ok stp src pos ain: isptr stp -> rs_bytes src -> Zlength src < 2 ^ 63 ->
  0 <= pos -> 0 <= ain -> pos + ain <= Zlength src ->
  in_ok (InBuf Ews stp pos (Zlength src) (bytes_rep src)) (sublist pos (pos + ain) src) /\ Zlength (sublist pos (pos + ain) src) = ain.
Proof.
  intros Pst Bs Hs Hp Ha Hpa.
  assert (Hl: Zlength (sublist pos (pos + ain) src) = ain) by (rewrite Zlength_sublist; lia).
  split; auto. unfold in_ok. rewrite Hl.
  assert (Lb: Zlength (bytes_rep src) = Zlength src) by (unfold bytes_rep; apply Zlength_map).
  repeat split; auto; try lia; try rep_lia.
  - unfold bytes_rep, byte_vals. rewrite sublist_map. reflexivity.
  - apply Forall_sublist. eapply Forall_impl; [ | exact Bs]. intros b Hb. hnf in Hb. rep_lia.
Qed.

Lemma rs_out_ok op (outv d: list Z) aout: isptr op -> Zlength d <= 2 ^ 60 -> 0 <= aout ->
  Zlength outv + aout <= Zlength d ->
  out_ok (OutBuf Ews op (Zlength outv) (Zlength d) (bytes_rep outv ++ Zrepeat Vundef (Zlength d - Zlength outv)))
    aout.
Proof.
  intros Pop Hd Ha Hoa. pose proof (Zlength_nonneg outv).
  unfold out_ok. split; [auto with share | ]. repeat split; auto; try lia; try rep_lia.
  rewrite Zlength_app, Zlength_Zrepeat by lia. unfold bytes_rep. rewrite Zlength_map. lia.
Qed.

Lemma rs_set_call_eta z: rs_set_call z (zf_ni z) (zf_ai z) (zf_no z) (zf_ao z) = z.
Proof. destruct z; reflexivity. Qed.

(* the output object after a call that wrote ow behind outv *)
Lemma rs_out_app (outv ow: list Z) n:
  Zlength outv + Zlength ow <= n ->
  sublist 0 (Zlength outv) (bytes_rep outv ++ Zrepeat Vundef (n - Zlength outv)) ++ byte_vals ow ++
  sublist (Zlength outv + Zlength ow) n (bytes_rep outv ++ Zrepeat Vundef (n - Zlength outv)) =
  bytes_rep (outv ++ ow) ++ Zrepeat Vundef (n - Zlength (outv ++ ow)).
Proof.
  intros Hn. pose proof (Zlength_nonneg outv). pose proof (Zlength_nonneg ow).
  assert (Lb: Zlength (bytes_rep outv) = Zlength outv) by (unfold bytes_rep; apply Zlength_map).
  rewrite sublist_app1 by lia. rewrite sublist_same by lia.
  rewrite sublist_app2 by lia. rewrite Lb.
  rewrite sublist_Zrepeat by lia.
  unfold bytes_rep, byte_vals. rewrite map_app, <- app_assoc, Zlength_app. f_equal. f_equal. f_equal. lia.
Qed.

(* the join of `if (c) t = v1; else t = (tbool) e;`: the temp t holds v *)
Ltac rs_if_tmp t v := match goal with |- semax _ (PROPx _ (LOCALx ?Q (SEPx ?R))) _ _ =>
  forward_if (PROPx [] (LOCALx (temp t (Vint (Int.repr v)) :: Q) (SEPx R))) end.

(* a branch excluded by the value of its test *)
Ltac rs_nob := exfalso; first [ congruence | exact (Int.one_not_zero ltac:(assumption)) | contradiction ].

(* the check of the return code: t'22 = (code == Z_OK || code == Z_BUF_ERROR) is v, then t'23 = 1, gp_assert *)
Ltac rs_chk v :=
  rs_if_tmp _t'23 v; [ first [ rs_nob | forward; entailer! ] | first [ rs_nob | forward; entailer! ] | ];
  rs_if_tmp _t'24 1; [ first [ rs_nob | forward; entailer! ] | first [ rs_nob | forward; entailer! ] | ];
  forward_call (Int.repr 1).

(* one pass of the do-while's body from a given state of the invariant *)
Lemma rs_body_core {Espec: OracleKind} P gv vs vwb stp src dp d op ep Brk pos outv z L ai ao:
  rs_facts P -> rs_bytes src -> rs_bytes d -> Zlength src < 2 ^ 63 -> Zlength d <= 2 ^ 60 ->
  isptr stp -> isptr dp -> isptr op ->
  P src d pos outv z L -> zf_ok z -> swfW (l_s L) -> 0 <= ai <= Int.max_unsigned -> 0 <= ao <= Int.max_unsigned ->
  semax Delta_m
  (PROP ()
   LOCAL (temp _stream stp; temp _stream_len (Vlong (Int64.repr (Zlength src)));
          temp _data dp; temp _data_len (Vlong (Int64.repr (Zlength d))); temp _out op; temp _expected ep;
          lvar _window_bits (tarray tint 3) vwb; lvar _strm (Tstruct _z_stream_s noattr) vs; gvars gv)
   SEP (istreamA gv Tsh vs (rs_set_call z (offset_val pos stp) ai (offset_val (Zlength outv) op) ao) Vundef (Some L);
        data_at_ Tsh (tarray tint 3) vwb;
        mem_mgr gv; zfuncs gv; tables_rep Ers gv; Zlib.proof.crc32.Spec.crc_table_at Ers gv; version_lit gv;
        rs_hversion_lit gv;
        malloc_token Ews (tarray tuchar (Zlength src)) stp;
        data_at Ews (tarray tuchar (Zlength src)) (bytes_rep src) stp;
        malloc_token Ews (tarray tuchar (Zlength d)) dp;
        data_at Ews (tarray tuchar (Zlength d)) (bytes_rep d) dp;
        malloc_token Ews (tarray tuchar (Zlength d)) op;
        data_at Ews (tarray tuchar (Zlength d)) (bytes_rep outv ++ Zrepeat Vundef (Zlength d - Zlength outv)) op;
        rs_copy ep (Zlength d) d))
  rs_loop_body
  (loop1_ret_assert (rs_cont P gv vs vwb stp src dp d op ep) (overridePost Brk POST_B)).
Proof.
  intros PF Bs Bd Hs Hd Pst Pdp Pop HP Zo Hsw Hai Hao.
  destruct (rf_pos P PF _ _ _ _ _ _ HP) as (Hpos & [rest Hrest] & Hhd).
  rewrite rs_istreamA_unfold. Intros.
  assert_PROP (isptr vs) as Pvs by entailer!.
  unfold rs_loop_body, Delta_m, Gmain_k. simplify_func_tycontext. abbreviate_semax.
  set (av0 := adler_v _ _ _). unfold rs_tup.
  cbn [rs_set_call zf_ni zf_ai zf_tin zf_no zf_ao zf_tout zf_msg zf_dt zf_adler zf_res].
  forward.
  forward_call (Zlength src - pos).
  { apply prop_right. apply rs_sameblock; auto. }
  { entailer!. destruct stp; try contradiction. simpl. rewrite rs_sub_pp by lia. reflexivity. }
  forward.
  assert (Hol: Zlength outv <= Zlength d) by (subst d; rewrite Zlength_app; pose proof (Zlength_nonneg rest); lia).
  pose proof (Zlength_nonneg outv) as Hol0.
  forward.
  forward_call (Zlength d - Zlength outv).
  { apply prop_right. apply rs_sameblock; auto. }
  { entailer!. destruct op; try contradiction. simpl. rewrite rs_sub_pp by lia. reflexivity. }
  forward.
  set (ain := Z.min (Zlength src - pos) Int.max_unsigned).
  set (aout := Z.min (Zlength d - Zlength outv) Int.max_unsigned).
  assert (Hain: 0 <= ain <= Int.max_unsigned /\ pos + ain <= Zlength src).
  { pose proof (Z.le_min_l (Zlength src - pos) Int.max_unsigned).
    pose proof (Z.le_min_r (Zlength src - pos) Int.max_unsigned). unfold ain. rep_lia. }
  assert (Haout: 0 <= aout <= Int.max_unsigned /\ Zlength outv + aout <= Zlength d).
  { pose proof (Z.le_min_l (Zlength d - Zlength outv) Int.max_unsigned).
    pose proof (Z.le_min_r (Zlength d - Zlength outv) Int.max_unsigned). unfold aout. rep_lia. }
  set (z1 := rs_set_call z (offset_val pos stp) ain (offset_val (Zlength outv) op) aout).
  assert (Z1ok: zf_ok z1).
  { destruct Zo as (? & ? & ? & ? & ? & ?). unfold z1, rs_set_call, zf_ok; simpl. rep_lia. }
  unfold av0. sep_apply (rs_fold_call gv vs z L (offset_val pos stp) ain (offset_val (Zlength outv) op) aout Vundef).
  fold z1.
  set (inp := sublist pos (pos + ain) src).
  set (ib := InBuf Ews stp pos (Zlength src) (bytes_rep src)).
  set (cout := bytes_rep outv ++ Zrepeat Vundef (Zlength d - Zlength outv)).
  set (o := OutBuf Ews op (Zlength outv) (Zlength d) cout).
  assert (Hcout: Zlength cout = Zlength d).
  { unfold cout. rewrite Zlength_app, Zlength_Zrepeat by lia. unfold bytes_rep. rewrite Zlength_map. lia. }
  sep_apply (rs_bufs_pre L stp src pos op (Zlength d) cout (Zlength outv)); [lia | ].
  fold ib o.
  destruct (rs_in_ok stp src pos ain Pst Bs Hs ltac:(lia) ltac:(lia) ltac:(lia)) as [INOK Hinl]. fold inp ib in INOK, Hinl.
  pose proof (rs_out_ok op outv d aout Pop Hd ltac:(lia) ltac:(lia)) as OUTOK. fold cout o in OUTOK.
  forward_call tt. Intros u.
  assert (Eu: Int.repr u = Int.repr (Int.signed (Int.repr u))) by (rewrite Int.repr_signed; auto).
  rewrite Eu. clear Eu. set (flush := Int.signed (Int.repr u)).
  assert (Hfl: Int.min_signed <= flush <= Int.max_signed) by apply Int.signed_range. clearbody flush.
  rewrite <- (rs_istreamA_opt_ptr gv Tsh vs z1 Vundef (Some L)) by auto.
  forward_call (gv, Tsh, vs, z1, Vundef, Some L, ib, inp, Some o, flush, Ers, Ers, true, true).
  { rewrite (rs_head_none vs L), (rs_is_live_ptr vs) by auto. cancel. }
  { split; [unfold z1, ib, rs_set_call; simpl; rewrite Z.add_0_r; reflexivity | ].
    split; [unfold ib; split; [exact INOK | unfold z1; simpl; auto] | ].
    unfold z1, o, rs_set_call; simpl; rewrite Z.add_0_r; reflexivity. }
  Intros vret. destruct vret as [[[r z'] st'] ow]. simpl fst in *; simpl snd in *.
  match goal with Hx: inflate_rel _ _ _ _ _ _ _ _ _ _ _ |- _ => rename Hx into REL end.
  match goal with Hx: match st' with Some _ => _ | None => _ end |- _ => rename Hx into HSW end.
  assert (REL': inflate_rel flush vs (rs_set_call z (in_ptr ib 0) ain (out_ptr o 0) aout) (Some L) ib
                  (sublist pos (pos + ain) src) (Some o) r z' st' ow).
  { unfold ib, o; simpl. rewrite !Z.add_0_r. exact REL. }
  destruct (rf_inflate P PF src d pos outv z L vs flush ib o ain aout r z' st' ow HP H1 Zo
              ltac:(intro E; subst vs; contradiction) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hfl
              ltac:(discriminate) REL') as (L' & Est & HPOST).
  subst st'. clear REL REL'. cbn match in HSW.
  rewrite (rs_istreamA_opt_ptr gv Tsh vs z' Vundef (Some L')), !(rs_is_live_ptr vs) by auto.
  forward.
  forward_if.
  { forward. Exists (Int.repr 0). sep_apply rs_a_frame. entailer!. }
  assert (Hr: r <> Z_MEM_ERROR) by (intro E; subst r; contradiction).
  specialize (HPOST Hr). unfold rs_post in HPOST. cbv zeta in HPOST.
  destruct HPOST as (Hcode & Hai' & How & Hao' & Hni & Hno & Hob & [rest' Hrest'] & Hend & HP').
  destruct (rf_pos P PF _ _ _ _ _ _ HP') as (Hpos' & _ & Hhd').
  assert (Hlo: Zlength outv + Zlength ow <= Zlength d).
  { rewrite Hrest', !Zlength_app. pose proof (Zlength_nonneg rest'). lia. }
  unfold head_opt, head_mem. rewrite Hhd'.
  unfold ib, o in *. sep_apply (rs_bufs_post L stp src pos op (Zlength d) cout (Zlength outv) ow). Intros.
  unfold cout. rewrite (rs_out_app outv ow (Zlength d) Hlo).
  rewrite rs_istreamA_unfold. Intros.
  sep_apply (rs_istreamA_fold gv Tsh vs z' Vundef L'); auto.
  rewrite <- (rs_set_call_eta z'), Hni, Hno. simpl in_ptr; simpl out_ptr.
  rewrite <- (Zlength_app Z outv ow).
  assert (Hz': zf_ok z') by assumption.
  set (pos' := pos + (ain - zf_ai z')) in *.
  set (outv' := outv ++ ow) in *.
  unfold MORE_COMMANDS, abbreviate.
  (* gp_assert(code == Z_OK || code == Z_BUF_ERROR || code == Z_STREAM_END) *)
  destruct Hcode as [E|[E|E]]; subst r; unfold Z_OK, Z_BUF_ERROR, Z_STREAM_END in *.
  - rs_chk 1. unfold rs_cont. Exists pos' outv' z' L' (zf_ai z') (zf_ao z') 0. entailer!.
  - rs_chk 1. unfold rs_cont. Exists pos' outv' z' L' (zf_ai z') (zf_ao z') (-5). entailer!.
  - rs_chk 0. unfold rs_cont. Exists pos' outv' z' L' (zf_ai z') (zf_ao z') 1. entailer!.
Qed.

(* one pass of the do-while's body: the two clipped avail stores, inflate(&strm, any flush), `return 0` on
   Z_MEM_ERROR, the gp_assert of the return code (it never breaks: Brk is any break assertion) *)
Lemma rs_body_ok {Espec: OracleKind} P gv vs vwb stp src dp d op ep Brk:
  rs_facts P -> rs_bytes src -> rs_bytes d -> Zlength src < 2 ^ 63 -> Zlength d <= 2 ^ 60 ->
  isptr stp -> isptr dp -> isptr op ->
  semax Delta_m (rs_inv P gv vs vwb stp src dp d op ep) rs_loop_body
    (loop1_ret_assert (rs_cont P gv vs vwb stp src dp d op ep) (overridePost Brk POST_B)).
Proof.
  intros PF Bs Bd Hs Hd Pst Pdp Pop.
  unfold rs_inv. Intros pos outv z L ai ao.
  eapply rs_body_core; eauto.
Qed.

(* `next_out == out + data_len` with next_out = out + data_len: the end pointer of the output object (malloc'd,
   so valid even when data_len = 0) may be compared with itself *)
Local Transparent denote_tc_test_eq.
Lemma rs_test_eq_end n (c: list val) op:
  isptr op -> 0 <= n ->
  malloc_token Ews (tarray tuchar n) op * data_at Ews (tarray tuchar n) c op * TT
  |-- denote_tc_test_eq (offset_val n op) (offset_val n op).
Proof.
  intros Pop Hn. destruct op; try contradiction.
  assert (W: malloc_token Ews (tarray tuchar n) (Vptr b i) * data_at Ews (tarray tuchar n) c (Vptr b i)
             |-- weak_valid_pointer (offset_val n (Vptr b i)))
    by (apply (cbuf_weak_valid true); auto; lia).
  simpl in W |- *. unfold test_eq_ptrs.
  unfold sameblock; destruct (peq b b); [ | congruence].
  apply andp_right; (eapply derives_trans; [apply sepcon_derives; [exact W | apply derives_refl] | ]);
    apply extend_weak_valid_pointer.
Qed.
Local Opaque denote_tc_test_eq.

(* the final check next_out == out + data_len && bytes_eq(out, expected, data_len) (expected: the copy of the
   data, rs_copy), then `return 0` *)
Lemma rs_final_ok {Espec: OracleKind} gv vs vwb stp src dp d op ep:
  rs_bytes src -> rs_bytes d -> Zlength src < 2 ^ 63 -> Zlength d <= 2 ^ 60 ->
  isptr stp -> isptr dp -> isptr op ->
  semax Delta_m (rs_done gv vs vwb stp src dp d op ep) rs_final POST_B.
Proof.
  intros Bs Bd Hs Hd Pst Pdp Pop.
  unfold rs_done, rs_final. Intros z L.
  unfold Delta_m, Gmain_k. simplify_func_tycontext.
  rewrite (rs_istreamA_unfold gv Tsh vs z Vundef L). Intros.
  unfold rs_tup.
  forward.
  { rewrite H. entailer!. }
  gather_SEP (data_at Tsh t_zsl _ vs) (state_mem gv vs L).
  replace_SEP 0 (istreamA gv Tsh vs z Vundef (Some L)).
  { go_lower. apply rs_istreamA_fold; auto. }
  rewrite H. apply semax_if_seq.
  forward_if.
  { eapply derives_trans; [ | apply (rs_test_eq_end (Zlength d) (bytes_rep d) op Pop (Zlength_nonneg d))].
    cancel. }
  2: { exfalso. apply H3. destruct op; try contradiction. simpl. do 2 f_equal.
       rewrite Ptrofs.mul_commut, Ptrofs.mul_one. unfold Ptrofs.of_int64.
       rewrite Int64.unsigned_repr; [reflexivity | pose proof (Zlength_nonneg d); rep_lia]. }
  unfold rs_copy. Intros.
  assert_PROP (isptr ep) as Pep by entailer!.
  rewrite <- (rs_bytes_a Ews (Zlength d) (bytes_rep d) op), <- (rs_bytes_a Ews (Zlength d) (bytes_rep d) ep).
  apply seq_assoc1.
  forward_call (op, Ews, op, 0, Zlength d, bytes_rep d, d, ep, Ews, ep, 0, Zlength d, bytes_rep d, d, Zlength d).
  { assert (B: is_bytes d).
    { unfold rs_bytes in Bd. unfold is_bytes. eapply Forall_impl; [ | exact Bd].
      unfold Format.byte_ok. intros a Ha. rep_lia. }
    unfold cbuf_ok.
    rewrite Z.add_0_l, sublist_same by (unfold bytes_rep; rewrite ?Zlength_map; lia).
    split; (split; [rewrite isptr_offset_val_zero; auto | ]); repeat split; auto; lia. }
  destruct (list_eq_dec Z.eq_dec d d); [ | contradiction].
  forward.
  forward_call (Int.repr 1).
  forward. Exists (Int.repr 0). sep_apply (rs_a_frame gv Tsh vs z Vundef L). entailer!.
Qed.

Lemma seg_loop_ok {Espec: OracleKind} P gv vs vwb stp src dp d op ep:
  rs_facts P -> rs_bytes src -> rs_bytes d -> Zlength src < 2 ^ 63 -> Zlength d <= 2 ^ 60 ->
  isptr stp -> isptr dp -> isptr op ->
  semax Delta_m (rs_inv P gv vs vwb stp src dp d op ep) rs_seg32 POST_B.
Proof.
  intros PF Bs Bd Hs Hd Pst Pdp Pop.
  rewrite rs_seg32_eq.
  apply semax_seq with (Q := rs_done gv vs vwb stp src dp d op ep); [ | apply rs_final_ok; auto].
  apply semax_loop with (Q' := rs_cont P gv vs vwb stp src dp d op ep).
  { apply rs_body_ok; auto. }
  unfold rs_cont, rs_loop_incr. Intros pos outv z L ai ao r.
  match goal with Hx: r = Z_OK \/ _ |- _ => rename Hx into Hcode end.
  match goal with Hx: r = Z_STREAM_END -> _ |- _ => rename Hx into Hend end.
  unfold Delta_m, Gmain_k. simplify_func_tycontext.
  forward_if.
  - forward. unfold rs_inv. Exists pos outv z L ai ao. entailer!.
  - match goal with Hx: Int.repr r = _ |- _ => rename Hx into Hne end.
    assert (Er: r = Z_STREAM_END).
    { destruct Hcode as [E|[E|E]]; subst r; auto; unfold Z_OK, Z_BUF_ERROR, Z_STREAM_END in *;
      apply repr_inj_signed in Hne; rep_lia. }
    specialize (Hend Er). subst outv.
    forward. unfold rs_done.
    Exists (rs_set_call z (offset_val pos stp) ai (offset_val (Zlength d) op) ao) L.
    rewrite Z.sub_diag, Zrepeat_0, app_nil_r. entailer!.
Qed.

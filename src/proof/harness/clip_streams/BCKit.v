(* Law rj_bad_checksum, main (MainBC.v): the kit shared by the segment lemmas of main's body proof.
   - Delta_bc (main's type context), POST_bc (main's postcondition after start_function), POST_B (the
     postcondition of every suffix of main's chain of statements: each ends by a return);
   - the segments: main's body is `chain; return 0`, the chain s1; (s2; (s3; ...)); bc_seg k is the suffix of the
     chain from its k-th statement (1-based);
   - the assertions at the cuts.  The deflate half (statements 11-20) is the one of rj_truncated's main
     (RTKit.v: its statements 9-18), with the object [change] of 8 bytes and 8 <= window_bits carried along
     ([bc_chg]).
   Main's statements: 1-3 data_len = upto(PTRDIFF_MAX), data = any_bytes(data_len), out = malloc(data_len), 4 their
   NULL check, 5-8 level, window_bits, mem_level, strategy (nondet_u32), 9 change = any_bytes(8), 10 `if (change ==
   NULL || window_bits < 8) return 0`, 11 new_stream(&compressor), 12 deflateInit2 and its check, 13-15 capacity =
   deflateBound_z, compressed = malloc(capacity) and its check, 16-17 next_in = data, next_out = compressed, 18 the
   do-while of deflate() calls, 19 `if (code != Z_STREAM_END) return 0`, 20 compressed_len, 21 trailer_len = 4,
   22 `if (window_bits > 15) trailer_len = 8`, 23 changed = 0, 24 the for loop changing the trailer,
   25 gp_assume(changed != 0), 26 new_stream(&decompressor), 27 window_bits 8 -> 9, 28 inflateInit2 and its check,
   29-30 next_in, next_out, 31 the do-while of inflate() calls, 32 return 0. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.EnvBodies.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Zlib.proof.deflate.DSpec9.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.SpecW.
Require Zlib.proof.inflate.Callees.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.clip_streams.CS.
Require Import Zlib.proof.harness.clip_streams.Globals.
Require Import Zlib.proof.harness.clip_streams.DFacts.
Require Import Zlib.proof.harness.clip_streams.IFacts.
Require Import Zlib.proof.harness.clip_streams.MainDefs.
Require Import Zlib.harness.rj_bad_checksum.code.
#[local] Existing Instance CS.CS.
Local Open Scope logic.

Definition Delta_bc : tycontext := func_tycontext f_main (QPvarspecs p_bc) Gmain_bc nil.

(* main's postcondition after start_function (main_core_spec) *)
Definition POST_bc : ret_assert :=
  frame_ret_assert (function_body_ret_assert tint (EX r : int, PROP () RETURN (Vint r) SEP (TT))%argsassert)
    (stackframe_of f_main).

(* the postcondition of every suffix of the chain: it never ends normally *)
Definition POST_B : ret_assert := overridePost FF POST_bc.

(* ---------------------------------------------------------------------------------------------- *)
(* The segments of f_main's body                                                                 *)

Fixpoint bc_drop (n : nat) (s : statement) : statement :=
  match n, s with
  | O, _ => s
  | S n', Ssequence _ b => bc_drop n' b
  | _, _ => Sskip
  end.

Definition bc_chain (s : statement) : statement := match s with Ssequence a _ => a | _ => Sskip end.

Ltac bc_get_seg k :=
  let n := eval compute in (k - 1)%nat in
  let x := eval cbv beta iota zeta delta [bc_drop bc_chain f_main fn_body] in
    (bc_drop n (bc_chain (fn_body f_main))) in
  exact x.

Definition bc_seg1 : statement := ltac:(bc_get_seg 1%nat).
Definition bc_seg11 : statement := ltac:(bc_get_seg 11%nat).
Definition bc_seg13 : statement := ltac:(bc_get_seg 13%nat).
Definition bc_seg18 : statement := ltac:(bc_get_seg 18%nat).
Definition bc_seg19 : statement := ltac:(bc_get_seg 19%nat).
Definition bc_seg21 : statement := ltac:(bc_get_seg 21%nat).
Definition bc_seg26 : statement := ltac:(bc_get_seg 26%nat).
Definition bc_seg31 : statement := ltac:(bc_get_seg 31%nat).

Lemma bc_body_eq : fn_body f_main = Ssequence bc_seg1 (Sreturn (Some (Econst_int (Int.repr 0) tint))).
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The assertions of the deflate half                                                            *)

Definition t_zsl : type := Tstruct _z_stream_s noattr.

(* the rest of the local compressor while the deflate API holds its fields: the complement of Ews (the
   specifications' share) and the Ews share of the struct's padding *)
Definition bc_srest (vc : val) : mpred :=
  @data_at_ CS.CS (Share.comp Ews) t_zsl vc * BoundKit.strm_pad vc.

(* the choices: data_len n, the data object dp holding D, the output object op, the four ints *)
Definition bc_cf (n : Z) (D : list Z) (dp op : val) (level wbits mem strategy : Z) : Prop :=
  0 <= n <= max_size /\ Zlength D = n /\ is_bytes D /\ isptr dp /\ isptr op /\
  rs32 level /\ rs32 wbits /\ rs32 mem /\ rs32 strategy.

(* what rj_bad_checksum adds to the deflate half: the 8 bytes C of the object [change] (at chp), and
   8 <= window_bits (a zlib or gzip stream) *)
Definition bc_chg_ok (wbits : Z) (C : list Z) (chp : val) : Prop :=
  8 <= wbits /\ Zlength C = 8 /\ is_bytes C /\ isptr chp.

Definition bc_chg (C : list Z) (chp : val) : mpred :=
  malloc_token Ews (tarray tuchar 8) chp * data_at Ews (tarray tuchar 8) (bytes_rep C) chp.

Section Assertions.
Context (gv : globals) (vc vd : val).

(* after start_function *)
Definition bc_A0 : environ -> mpred :=
  PROP ()
  LOCAL (lvar _compressor t_zsl vc; lvar _decompressor t_zsl vd; gvars gv)
  SEP (data_at_ Tsh t_zsl vc; data_at_ Tsh t_zsl vd; mem_mgr gv; R_bc gv).

(* before statement 11 (new_stream(&compressor)): the inputs drawn, the three objects made *)
Definition bc_A11 (n : Z) (D : list Z) (dp op : val) (level wbits mem strategy : Z) (C : list Z) (chp : val)
    : environ -> mpred :=
  PROP (bc_cf n D dp op level wbits mem strategy; bc_chg_ok wbits C chp)
  LOCAL (temp _data_len (Vlong (Int64.repr n)); temp _data dp; temp _out op;
         temp _level (Vint (Int.repr level)); temp _window_bits (Vint (Int.repr wbits));
         temp _mem_level (Vint (Int.repr mem)); temp _strategy (Vint (Int.repr strategy));
         temp _change chp;
         lvar _compressor t_zsl vc; lvar _decompressor t_zsl vd; gvars gv)
  SEP (data_at_ Tsh t_zsl vc; data_at_ Tsh t_zsl vd; mem_mgr gv; R_bc gv;
       malloc_token Ews (tarray tuchar n) dp; data_at Ews (tarray tuchar n) (bytes_rep D) dp;
       malloc_token Ews (tarray tuchar n) op; data_at_ Ews (tarray tuchar n) op; bc_chg C chp).

(* before statement 13 (capacity = deflateBound_z): deflateInit2 returned Z_OK, the state s and the fields
   (tin, tout, adler, msg) satisfy J0 *)
Definition bc_A13 (J0 : Z -> dstate -> Z -> Z -> Z -> Prop) (n : Z) (D : list Z) (dp op : val) (wbits : Z)
    (s : dstate) (tin tout adler : Z) (msg : option Z) (msgv : val) (C : list Z) (chp : val) : environ -> mpred :=
  PROP (0 <= n <= max_size; Zlength D = n; is_bytes D; isptr dp; isptr op; rs32 wbits;
        J0 wbits s tin tout adler; d_gzhead s = None; msg_ok msg msgv; bc_chg_ok wbits C chp)
  LOCAL (temp _data_len (Vlong (Int64.repr n)); temp _data dp; temp _out op;
         temp _window_bits (Vint (Int.repr wbits)); temp _change chp;
         lvar _compressor t_zsl vc; lvar _decompressor t_zsl vd; gvars gv)
  SEP (dstream 2 (Some s) vc nullval gv; api_fields vc nullval 0 tin nullval 0 tout msgv adler; bc_srest vc;
       data_at_ Tsh t_zsl vd; mem_mgr gv; R_bc gv;
       malloc_token Ews (tarray tuchar n) dp; data_at Ews (tarray tuchar n) (bytes_rep D) dp;
       malloc_token Ews (tarray tuchar n) op; data_at_ Ews (tarray tuchar n) op; bc_chg C chp).

(* the output object of b bytes (malloc(capacity)) after O was produced into it *)
Definition bc_comp (b : Z) (O : list Z) (cp : val) : mpred :=
  malloc_token Ews (tarray tuchar b) cp *
  data_at Ews (tarray tuchar b) (bytes_rep O ++ Zrepeat Vundef (b - Zlength O)) cp.

(* the invariant of the do-while (statement 18) at the head of its body: pos bytes of the data consumed
   (next_in = data + pos), O produced (next_out = compressed + |O|), avail_in / avail_out as the previous call
   left them (ai, ao), J of the state and the fields *)
Definition bc_LI (J : Z -> list Z -> Z -> Z -> list Z -> dstate -> Z -> Z -> Z -> Prop) (n : Z) (D : list Z)
    (dp op : val) (wbits b : Z) (cp : val) (C : list Z) (chp : val) : environ -> mpred :=
  EX pos : Z, EX O : list Z, EX s : dstate, EX tin : Z, EX tout : Z, EX adler : Z, EX ai : Z, EX ao : Z,
  EX msg : option Z, EX msgv : val,
  PROP (Zlength D = n; is_bytes D; isptr dp; isptr op; isptr cp; rs32 wbits;
        J wbits D b pos O s tin tout adler; msg_ok msg msgv; bc_chg_ok wbits C chp)
  LOCAL (temp _data_len (Vlong (Int64.repr n)); temp _data dp; temp _out op;
         temp _window_bits (Vint (Int.repr wbits)); temp _out_size (Vlong (Int64.repr b));
         temp _compressed cp; temp _change chp;
         lvar _compressor t_zsl vc; lvar _decompressor t_zsl vd; gvars gv)
  SEP (dstream 2 (Some s) vc nullval gv;
       api_fields vc (offset_val pos dp) ai tin (offset_val (Zlength O) cp) ao tout msgv adler; bc_srest vc;
       data_at_ Tsh t_zsl vd; mem_mgr gv; R_bc gv;
       malloc_token Ews (tarray tuchar n) dp; data_at Ews (tarray tuchar n) (bytes_rep D) dp;
       malloc_token Ews (tarray tuchar n) op; data_at_ Ews (tarray tuchar n) op; bc_comp b O cp;
       bc_chg C chp).

(* after the do-while (before statement 19): the last call's code; on Z_STREAM_END, O is the deflate stream of
   the data *)
Definition bc_LB (n : Z) (D : list Z) (dp op : val) (wbits b : Z) (cp : val) (C : list Z) (chp : val)
    : environ -> mpred :=
  EX code : Z, EX O : list Z, EX os : option dstate, EX nin : val, EX ai : Z, EX tin : Z, EX ao : Z, EX tout : Z,
  EX adler : Z, EX msgv : val,
  PROP (0 <= n <= max_size; Zlength D = n; is_bytes D; isptr dp; isptr op; isptr cp; rs32 wbits;
        0 <= Zlength O <= b; b <= max_u64; rbytes O;
        rs32 code; code = Z_STREAM_END -> dfinal_of wbits D O; bc_chg_ok wbits C chp)
  LOCAL (temp _code (Vint (Int.repr code));
         temp _data_len (Vlong (Int64.repr n)); temp _data dp; temp _out op;
         temp _window_bits (Vint (Int.repr wbits)); temp _compressed cp; temp _change chp;
         lvar _compressor t_zsl vc; lvar _decompressor t_zsl vd; gvars gv)
  SEP (dstream 2 os vc nullval gv;
       api_fields vc nin ai tin (offset_val (Zlength O) cp) ao tout msgv adler; bc_srest vc;
       data_at_ Tsh t_zsl vd; mem_mgr gv; R_bc gv;
       malloc_token Ews (tarray tuchar n) dp; data_at Ews (tarray tuchar n) (bytes_rep D) dp;
       malloc_token Ews (tarray tuchar n) op; data_at_ Ews (tarray tuchar n) op; bc_comp b O cp;
       bc_chg C chp; TT).

(* after compressed_len (before statement 21): the deflate run ended with Z_STREAM_END, O is the deflate stream
   of the data D (n bytes), at the start of the output object of b bytes; the compressor given back as the
   local's memory (its state's allocations are left in TT) *)
Definition bc_DH (wbits n b : Z) (D O : list Z) (dp op cp : val) (C : list Z) (chp : val) : environ -> mpred :=
  PROP (dfinal_of wbits D O; Zlength D = n; 0 <= n <= max_size; 0 <= Zlength O <= b; b <= Ptrofs.max_unsigned;
        Int.min_signed <= wbits <= Int.max_signed; rbytes D; is_bytes D; rbytes O; isptr dp; isptr op; isptr cp;
        bc_chg_ok wbits C chp)
  LOCAL (temp _data_len (Vlong (Int64.repr n)); temp _data dp; temp _out op;
         temp _window_bits (Vint (Int.repr wbits)); temp _compressed cp;
         temp _compressed_len (Vlong (Int64.repr (Zlength O))); temp _change chp;
         lvar _compressor t_zsl vc; lvar _decompressor t_zsl vd; gvars gv)
  SEP (mem_mgr gv; R_bc gv;
       data_at Ews (tarray tuchar n) (bytes_rep D) dp; malloc_token Ews (tarray tuchar n) dp;
       data_at_ Ews (tarray tuchar n) op; malloc_token Ews (tarray tuchar n) op;
       data_at Ews (tarray tuchar b) (bytes_rep O ++ Zrepeat Vundef (b - Zlength O)) cp;
       malloc_token Ews (tarray tuchar b) cp; bc_chg C chp;
       data_at_ Tsh t_zsl vc; data_at_ Tsh t_zsl vd; TT).

End Assertions.

(* ---------------------------------------------------------------------------------------------- *)
(* Tactic support                                                                                *)

(* Floyd's simplify_remove_localdef_temp (simpl on rlt_ident_eq of the large $"..." identifiers) takes minutes
   after a call that stores into a temp: remove the temp by rewriting instead *)
Lemma bc_rlt_nil i: remove_localdef_temp i [] = [].
Proof. reflexivity. Qed.
Lemma bc_rlt_gvars i g l: remove_localdef_temp i (gvars g :: l) = gvars g :: remove_localdef_temp i l.
Proof. reflexivity. Qed.
Lemma bc_rlt_lvar i j t v l: remove_localdef_temp i (lvar j t v :: l) = lvar j t v :: remove_localdef_temp i l.
Proof. reflexivity. Qed.
Lemma bc_rlt_same i v l: remove_localdef_temp i (temp i v :: l) = remove_localdef_temp i l.
Proof. simpl. unfold rlt_ident_eq. rewrite if_true by auto. reflexivity. Qed.
Lemma bc_rlt_cons i j v l: i <> j -> remove_localdef_temp i (temp j v :: l) = temp j v :: remove_localdef_temp i l.
Proof. intros. simpl. unfold rlt_ident_eq. rewrite if_false by auto. reflexivity. Qed.

Ltac bc_rlt :=
  repeat first [ rewrite bc_rlt_nil | rewrite bc_rlt_gvars | rewrite bc_rlt_lvar | rewrite bc_rlt_same
               | rewrite bc_rlt_cons by (let X := fresh in intro X; discriminate X) ].

(* a branch the test excludes *)
Ltac bc_bad := first [ contradiction
  | match goal with H: Int.repr _ = Int.zero |- _ =>
      apply (f_equal Int.unsigned) in H; rewrite Int.unsigned_repr in H by rep_lia; discriminate H end ].

(* (tbool) (p == NULL) for a pointer p *)
Ltac bc_cmp := try match goal with |- context [sem_cmp_pp Ceq ?p _] =>
  let Hp := fresh in assert (Hp: isptr p) by (first [eapply field_compatible_isptr; eassumption | auto]);
  destruct p; try contradiction Hp; reflexivity end.

(* Moves of byte arrays and malloc tokens from the compspecs of the laws_common.h helpers (adler32's) and of the
   deflate API (DCS.CS) to the law's *)
Lemma bc_bytes_adler sh n (v: list val) q:
  @data_at Zlib.units.Adler32.CS sh (tarray tuchar n) v q = @data_at CS.CS sh (tarray tuchar n) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_adler32); [apply JMeq_refl | reflexivity]. Qed.
Lemma bc_tok_adler sh n q:
  @malloc_token Zlib.units.Adler32.CS sh (tarray tuchar n) q = @malloc_token CS.CS sh (tarray tuchar n) q.
Proof. apply equal_f; apply (@malloc_token_change_composite _ _ CC_adler32). reflexivity. Qed.
Lemma bc_bytes_dcs sh n (v: list val) q:
  @data_at Zlib.proof.deflate.DCS.CS sh (tarray tuchar n) v q = @data_at CS.CS sh (tarray tuchar n) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_dcs); [apply JMeq_refl | reflexivity]. Qed.
Lemma bc_tok_dcs sh n q:
  @malloc_token Zlib.proof.deflate.DCS.CS sh (tarray tuchar n) q = @malloc_token CS.CS sh (tarray tuchar n) q.
Proof. apply equal_f; apply (@malloc_token_change_composite _ _ CC_dcs). reflexivity. Qed.

Ltac bc_law := repeat first [ rewrite bc_bytes_adler | rewrite bc_tok_adler ].

(* ---------------------------------------------------------------------------------------------- *)
(* The changed stream and the inflate half                                                        *)

(* the bytes src of the compressed object after the trailer was changed: what bd_init asks of them *)
Definition bc_src_ok (wbits : Z) (O src : list Z) : Prop :=
  Zlength src = Zlength O /\ bytes_ok src /\
  sublist 0 (Zlength O - trl_of wbits) src = sublist 0 (Zlength O - trl_of wbits) O /\
  sublist (Zlength O - trl_of wbits) (Zlength O) src <> sublist (Zlength O - trl_of wbits) (Zlength O) O.

(* the facts of the inflate half that do not change *)
Definition bc_facts (wbits n b : Z) (D O src : list Z) (dp op cp : val) : Prop :=
  DFacts.dfinal_of wbits D O /\ Zlength D = n /\ 0 <= n <= DFacts.max_size /\ 0 <= Zlength O <= b /\
  b <= Ptrofs.max_unsigned /\ Int.min_signed <= wbits <= Int.max_signed /\ 8 <= wbits /\
  rbytes D /\ is_bytes D /\ rbytes O /\ isptr dp /\ isptr op /\ isptr cp /\ bc_src_ok wbits O src.

(* after gp_assume(changed != 0) (before statement 26): the compressed object holds src, O with its trailer
   changed (and nothing else) *)
Definition bc_TH (wbits n b : Z) (D O src : list Z) (dp op cp vc vd : val) (gv : globals) : environ -> mpred :=
  PROP (bc_facts wbits n b D O src dp op cp)
  LOCAL (temp _data_len (Vlong (Int64.repr n)); temp _data dp; temp _out op;
         temp _window_bits (Vint (Int.repr wbits)); temp _compressed cp;
         temp _compressed_len (Vlong (Int64.repr (Zlength O)));
         lvar _compressor t_zsl vc; lvar _decompressor t_zsl vd; gvars gv)
  SEP (mem_mgr gv; R_bc gv;
       data_at Ews (tarray tuchar n) (bytes_rep D) dp; malloc_token Ews (tarray tuchar n) dp;
       data_at_ Ews (tarray tuchar n) op; malloc_token Ews (tarray tuchar n) op;
       data_at Ews (tarray tuchar b) (bytes_rep src ++ Zrepeat Vundef (b - Zlength O)) cp;
       malloc_token Ews (tarray tuchar b) cp;
       data_at_ Tsh t_zsl vc; data_at_ Tsh t_zsl vd; TT).

(* the invariant of the inflate loop (statement 31), at the head of the do-while's body: the bytes of src
   consumed pos (next_in = compressed + pos), the bytes written out (next_out = out + |out|; the output object
   holds out, then undefined bytes), the stream (z, L) with P wbits D O src pos out z L and the wide state
   invariant swfW that inflate_specW needs *)
Definition bc_inv (P : inv_t) (wbits n b : Z) (D O src : list Z) (dp op cp vc vd : val) (gv : globals)
    : environ -> mpred :=
  EX pos : Z, EX out : list Z, EX z : zfields, EX L : live,
  PROP (P wbits D O src pos out z L; swfW (l_s L);
        zf_ni z = offset_val pos cp; zf_no z = offset_val (Zlength out) op)
  LOCAL (temp _data_len (Vlong (Int64.repr n)); temp _data dp; temp _out op; temp _compressed cp;
         temp _compressed_len (Vlong (Int64.repr (Zlength O)));
         lvar _compressor t_zsl vc; lvar _decompressor t_zsl vd; gvars gv)
  SEP (istreamA gv Tsh vd z Vundef (Some L); Zlib.proof.inflate.Callees.zfuncs gv; mem_mgr gv; R_bc gv;
       data_at Ews (tarray tuchar n) (bytes_rep D) dp; malloc_token Ews (tarray tuchar n) dp;
       data_at Ews (tarray tuchar n) (bytes_rep out ++ Zrepeat Vundef (n - Zlength out)) op;
       malloc_token Ews (tarray tuchar n) op;
       data_at Ews (tarray tuchar b) (bytes_rep src ++ Zrepeat Vundef (b - Zlength O)) cp;
       malloc_token Ews (tarray tuchar b) cp;
       data_at_ Tsh t_zsl vc; TT).

(* ---------------------------------------------------------------------------------------------- *)
(* The segment statements (CPS: each proves its segment from the proof of the next one)          *)

(* statements 1-10: the inputs *)
Definition seg_inputs_stmt : Prop :=
  forall {Espec : OracleKind} gv vc vd,
  (forall n D dp op level wbits mem strategy C chp,
     semax Delta_bc (bc_A11 gv vc vd n D dp op level wbits mem strategy C chp) bc_seg11 POST_B) ->
  semax Delta_bc (bc_A0 gv vc vd) bc_seg1 POST_B.

(* statements 11-12: new_stream, deflateInit2 *)
Definition seg_init_stmt : Prop :=
  forall {Espec : OracleKind} J0 J gv vc vd n D dp op level wbits mem strategy C chp,
  clip_dfacts J0 J ->
  (forall s tin tout adler msg msgv,
     semax Delta_bc (bc_A13 gv vc vd J0 n D dp op wbits s tin tout adler msg msgv C chp) bc_seg13 POST_B) ->
  semax Delta_bc (bc_A11 gv vc vd n D dp op level wbits mem strategy C chp) bc_seg11 POST_B.

(* statements 13-17: deflateBound_z, malloc, next_in, next_out *)
Definition seg_bound_stmt : Prop :=
  forall {Espec : OracleKind} J0 J gv vc vd n D dp op wbits s tin tout adler msg msgv C chp,
  clip_dfacts J0 J ->
  (forall b cp, semax Delta_bc (bc_LI gv vc vd J n D dp op wbits b cp C chp) bc_seg18 POST_B) ->
  semax Delta_bc (bc_A13 gv vc vd J0 n D dp op wbits s tin tout adler msg msgv C chp) bc_seg13 POST_B.

(* statement 18: the deflate loop *)
Definition seg_loop_stmt : Prop :=
  forall {Espec : OracleKind} J0 J gv vc vd n D dp op wbits b cp C chp,
  clip_dfacts J0 J ->
  semax Delta_bc (bc_LB gv vc vd n D dp op wbits b cp C chp) bc_seg19 POST_B ->
  semax Delta_bc (bc_LI gv vc vd J n D dp op wbits b cp C chp) bc_seg18 POST_B.

(* statements 19-20: the check of the last code, compressed_len *)
Definition seg_end_stmt : Prop :=
  forall {Espec : OracleKind} gv vc vd n D dp op wbits b cp C chp,
  (forall O, semax Delta_bc (bc_DH gv vc vd wbits n b D O dp op cp C chp) bc_seg21 POST_B) ->
  semax Delta_bc (bc_LB gv vc vd n D dp op wbits b cp C chp) bc_seg19 POST_B.

(* statements 21-25: the trailer changed by the 8 bytes C, gp_assume(changed != 0) *)
Definition seg_trailer_stmt : Prop :=
  forall {Espec : OracleKind} P gv vc vd wbits n b D O dp op cp C chp,
  bad_facts P ->
  (forall src, bc_facts wbits n b D O src dp op cp ->
     semax Delta_bc (bc_TH wbits n b D O src dp op cp vc vd gv) bc_seg26 POST_B) ->
  semax Delta_bc (bc_DH gv vc vd wbits n b D O dp op cp C chp) bc_seg21 POST_B.

(* statements 26-30: new_stream, window_bits 8 -> 9, inflateInit2_ (any outcome but Z_OK returns), next_in,
   next_out *)
Definition seg_isetup_stmt : Prop :=
  forall {Espec : OracleKind} P wbits n b D O src dp op cp vc vd gv,
  bad_facts P -> bc_facts wbits n b D O src dp op cp ->
  semax Delta_bc (bc_inv P wbits n b D O src dp op cp vc vd gv) bc_seg31 POST_B ->
  semax Delta_bc (bc_TH wbits n b D O src dp op cp vc vd gv) bc_seg26 POST_B.

(* statement 31 (the inflate loop) and the final `return 0` *)
Definition seg_iloop_stmt : Prop :=
  forall {Espec : OracleKind} P wbits n b D O src dp op cp vc vd gv,
  bad_facts P -> bc_facts wbits n b D O src dp op cp ->
  semax Delta_bc (bc_inv P wbits n b D O src dp op cp vc vd gv) bc_seg31 POST_B.

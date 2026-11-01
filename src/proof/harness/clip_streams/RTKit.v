(* Law rj_truncated, main (MainRT.v): the kit shared by the segment lemmas of main's proof.
   - Delta_rt (main's type context), POST_rt (main's postcondition after start_function), POST_B (the
     postcondition of every suffix of main's chain of statements: each ends by a return);
   - the segments: main's body is `chain; return 0`, the chain s1; (s2; (s3; ...)); rt_seg k is the suffix of the
     chain from its k-th statement (1-based);
   - the assertions at the cuts of the deflate half (statements 1-18: the inputs, deflateInit2, deflateBound_z and
     malloc, the deflate loop, compressed_len) and the hand-over to the inflate half (rt_DH, before statement 19).
   Main's statements: 1-3 data_len = upto(PTRDIFF_MAX), data = any_bytes(data_len), out = malloc(data_len), 4 their
   NULL check, 5-8 level, window_bits, mem_level, strategy (nondet_u32), 9 new_stream(&compressor),
   10 deflateInit2 and its check, 11-13 capacity = deflateBound_z, compressed = malloc(capacity) and its check,
   14-15 next_in = data, next_out = compressed, 16 the do-while of deflate() calls, 17 `if (code != Z_STREAM_END)
   return 0`, 18 compressed_len, 19 prefix_len = upto(compressed_len - 1), 20 new_stream(&decompressor),
   21 window_bits 8 -> 9, 22 inflateInit2 and its check, 23-24 next_in, next_out, 25 the while loop of inflate()
   calls. *)
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
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.clip_streams.CS.
Require Import Zlib.proof.harness.clip_streams.Globals.
Require Import Zlib.proof.harness.clip_streams.DFacts.
Require Import Zlib.proof.harness.clip_streams.MainDefs.
Require Import Zlib.harness.rj_truncated.code.
#[local] Existing Instance CS.CS.
Local Open Scope logic.

Definition Delta_rt : tycontext := func_tycontext f_main (QPvarspecs p_rt) Gmain_rt nil.

(* main's postcondition after start_function (main_core_spec) *)
Definition POST_rt : ret_assert :=
  frame_ret_assert (function_body_ret_assert tint (EX r : int, PROP () RETURN (Vint r) SEP (TT))%argsassert)
    (stackframe_of f_main).

(* the postcondition of every suffix of the chain: it never ends normally *)
Definition POST_B : ret_assert := overridePost FF POST_rt.

(* ---------------------------------------------------------------------------------------------- *)
(* The segments of f_main's body                                                                 *)

Fixpoint rt_drop (n : nat) (s : statement) : statement :=
  match n, s with
  | O, _ => s
  | S n', Ssequence _ b => rt_drop n' b
  | _, _ => Sskip
  end.

Definition rt_chain (s : statement) : statement := match s with Ssequence a _ => a | _ => Sskip end.

Ltac rt_get_seg k :=
  let n := eval compute in (k - 1)%nat in
  let x := eval cbv beta iota zeta delta [rt_drop rt_chain f_main fn_body] in
    (rt_drop n (rt_chain (fn_body f_main))) in
  exact x.

Definition rt_seg1 : statement := ltac:(rt_get_seg 1%nat).
Definition rt_seg9 : statement := ltac:(rt_get_seg 9%nat).
Definition rt_seg11 : statement := ltac:(rt_get_seg 11%nat).
Definition rt_seg16 : statement := ltac:(rt_get_seg 16%nat).
Definition rt_seg17 : statement := ltac:(rt_get_seg 17%nat).
Definition rt_seg19 : statement := ltac:(rt_get_seg 19%nat).

Lemma rt_body_eq : fn_body f_main = Ssequence rt_seg1 (Sreturn (Some (Econst_int (Int.repr 0) tint))).
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The assertions                                                                                *)

Definition t_zsl : type := Tstruct _z_stream_s noattr.

(* the rest of the local compressor while the deflate API holds its fields: the complement of Ews (the
   specifications' share) and the Ews share of the struct's padding *)
Definition rt_srest (vc : val) : mpred :=
  @data_at_ CS.CS (Share.comp Ews) t_zsl vc * BoundKit.strm_pad vc.

(* the choices: data_len n, the data object dp holding D, the output object op, the four ints *)
Definition rt_cf (n : Z) (D : list Z) (dp op : val) (level wbits mem strategy : Z) : Prop :=
  0 <= n <= max_size /\ Zlength D = n /\ is_bytes D /\ isptr dp /\ isptr op /\
  rs32 level /\ rs32 wbits /\ rs32 mem /\ rs32 strategy.

Section Assertions.
Context (gv : globals) (vc vd : val).

(* after start_function *)
Definition rt_A0 : environ -> mpred :=
  PROP ()
  LOCAL (lvar _compressor t_zsl vc; lvar _decompressor t_zsl vd; gvars gv)
  SEP (data_at_ Tsh t_zsl vc; data_at_ Tsh t_zsl vd; mem_mgr gv; R_rt gv).

(* before statement 9 (new_stream(&compressor)): the inputs drawn, the two objects made *)
Definition rt_A9 (n : Z) (D : list Z) (dp op : val) (level wbits mem strategy : Z) : environ -> mpred :=
  PROP (rt_cf n D dp op level wbits mem strategy)
  LOCAL (temp _data_len (Vlong (Int64.repr n)); temp _data dp; temp _out op;
         temp _level (Vint (Int.repr level)); temp _window_bits (Vint (Int.repr wbits));
         temp _mem_level (Vint (Int.repr mem)); temp _strategy (Vint (Int.repr strategy));
         lvar _compressor t_zsl vc; lvar _decompressor t_zsl vd; gvars gv)
  SEP (data_at_ Tsh t_zsl vc; data_at_ Tsh t_zsl vd; mem_mgr gv; R_rt gv;
       malloc_token Ews (tarray tuchar n) dp; data_at Ews (tarray tuchar n) (bytes_rep D) dp;
       malloc_token Ews (tarray tuchar n) op; data_at_ Ews (tarray tuchar n) op).

(* before statement 11 (capacity = deflateBound_z): deflateInit2 returned Z_OK, the state s and the fields
   (tin, tout, adler, msg) satisfy J0 *)
Definition rt_A11 (J0 : Z -> dstate -> Z -> Z -> Z -> Prop) (n : Z) (D : list Z) (dp op : val) (wbits : Z)
    (s : dstate) (tin tout adler : Z) (msg : option Z) (msgv : val) : environ -> mpred :=
  PROP (0 <= n <= max_size; Zlength D = n; is_bytes D; isptr dp; isptr op; rs32 wbits;
        J0 wbits s tin tout adler; d_gzhead s = None; msg_ok msg msgv)
  LOCAL (temp _data_len (Vlong (Int64.repr n)); temp _data dp; temp _out op;
         temp _window_bits (Vint (Int.repr wbits));
         lvar _compressor t_zsl vc; lvar _decompressor t_zsl vd; gvars gv)
  SEP (dstream 2 (Some s) vc nullval gv; api_fields vc nullval 0 tin nullval 0 tout msgv adler; rt_srest vc;
       data_at_ Tsh t_zsl vd; mem_mgr gv; R_rt gv;
       malloc_token Ews (tarray tuchar n) dp; data_at Ews (tarray tuchar n) (bytes_rep D) dp;
       malloc_token Ews (tarray tuchar n) op; data_at_ Ews (tarray tuchar n) op).

(* the output object of b bytes (malloc(capacity)) after O was produced into it *)
Definition rt_comp (b : Z) (O : list Z) (cp : val) : mpred :=
  malloc_token Ews (tarray tuchar b) cp *
  data_at Ews (tarray tuchar b) (bytes_rep O ++ Zrepeat Vundef (b - Zlength O)) cp.

(* the invariant of the do-while (statement 16) at the head of its body: pos bytes of the data consumed
   (next_in = data + pos), O produced (next_out = compressed + |O|), avail_in / avail_out as the previous call
   left them (ai, ao), J of the state and the fields *)
Definition rt_LI (J : Z -> list Z -> Z -> Z -> list Z -> dstate -> Z -> Z -> Z -> Prop) (n : Z) (D : list Z)
    (dp op : val) (wbits b : Z) (cp : val) : environ -> mpred :=
  EX pos : Z, EX O : list Z, EX s : dstate, EX tin : Z, EX tout : Z, EX adler : Z, EX ai : Z, EX ao : Z,
  EX msg : option Z, EX msgv : val,
  PROP (Zlength D = n; is_bytes D; isptr dp; isptr op; isptr cp; rs32 wbits;
        J wbits D b pos O s tin tout adler; msg_ok msg msgv)
  LOCAL (temp _data_len (Vlong (Int64.repr n)); temp _data dp; temp _out op;
         temp _window_bits (Vint (Int.repr wbits)); temp _out_size (Vlong (Int64.repr b));
         temp _compressed cp;
         lvar _compressor t_zsl vc; lvar _decompressor t_zsl vd; gvars gv)
  SEP (dstream 2 (Some s) vc nullval gv;
       api_fields vc (offset_val pos dp) ai tin (offset_val (Zlength O) cp) ao tout msgv adler; rt_srest vc;
       data_at_ Tsh t_zsl vd; mem_mgr gv; R_rt gv;
       malloc_token Ews (tarray tuchar n) dp; data_at Ews (tarray tuchar n) (bytes_rep D) dp;
       malloc_token Ews (tarray tuchar n) op; data_at_ Ews (tarray tuchar n) op; rt_comp b O cp).

(* after the do-while (before statement 17): the last call's code; on Z_STREAM_END, O is the deflate stream of
   the data *)
Definition rt_LB (n : Z) (D : list Z) (dp op : val) (wbits b : Z) (cp : val) : environ -> mpred :=
  EX code : Z, EX O : list Z, EX os : option dstate, EX nin : val, EX ai : Z, EX tin : Z, EX ao : Z, EX tout : Z,
  EX adler : Z, EX msgv : val,
  PROP (0 <= n <= max_size; Zlength D = n; is_bytes D; isptr dp; isptr op; isptr cp; rs32 wbits;
        0 <= Zlength O <= b; b <= max_u64; rbytes O; rs32 code;
        code = Z_STREAM_END -> dfinal_of wbits D O)
  LOCAL (temp _code (Vint (Int.repr code));
         temp _data_len (Vlong (Int64.repr n)); temp _data dp; temp _out op;
         temp _window_bits (Vint (Int.repr wbits)); temp _compressed cp;
         lvar _compressor t_zsl vc; lvar _decompressor t_zsl vd; gvars gv)
  SEP (dstream 2 os vc nullval gv;
       api_fields vc nin ai tin (offset_val (Zlength O) cp) ao tout msgv adler; rt_srest vc;
       data_at_ Tsh t_zsl vd; mem_mgr gv; R_rt gv;
       malloc_token Ews (tarray tuchar n) dp; data_at Ews (tarray tuchar n) (bytes_rep D) dp;
       malloc_token Ews (tarray tuchar n) op; data_at_ Ews (tarray tuchar n) op; rt_comp b O cp; TT).

(* the hand-over to the inflate half (before statement 19): the deflate run ended with Z_STREAM_END, O is the
   deflate stream of the data D (n bytes), at the start of the output object of b bytes; the compressor given
   back as the local's memory (its state's allocations are left in TT) *)
Definition rt_DH (wbits n b : Z) (D O : list Z) (dp op cp : val) : environ -> mpred :=
  PROP (dfinal_of wbits D O; Zlength D = n; 0 <= n <= max_size; 0 <= Zlength O <= b; b <= Ptrofs.max_unsigned;
        Int.min_signed <= wbits <= Int.max_signed; rbytes D; is_bytes D; rbytes O; isptr dp; isptr op; isptr cp)
  LOCAL (temp _data_len (Vlong (Int64.repr n)); temp _data dp; temp _out op;
         temp _window_bits (Vint (Int.repr wbits)); temp _compressed cp;
         temp _compressed_len (Vlong (Int64.repr (Zlength O)));
         lvar _compressor t_zsl vc; lvar _decompressor t_zsl vd; gvars gv)
  SEP (mem_mgr gv; R_rt gv;
       data_at Ews (tarray tuchar n) (bytes_rep D) dp; malloc_token Ews (tarray tuchar n) dp;
       data_at_ Ews (tarray tuchar n) op; malloc_token Ews (tarray tuchar n) op;
       data_at Ews (tarray tuchar b) (bytes_rep O ++ Zrepeat Vundef (b - Zlength O)) cp;
       malloc_token Ews (tarray tuchar b) cp;
       data_at_ Tsh t_zsl vc; data_at_ Tsh t_zsl vd; TT).

End Assertions.


(* ---------------------------------------------------------------------------------------------- *)
(* Tactic support                                                                                *)

(* Floyd's simplify_remove_localdef_temp (simpl on rlt_ident_eq of the large $"..." identifiers) takes minutes
   after a call that stores into a temp: remove the temp by rewriting instead *)
Lemma rt_rlt_nil i: remove_localdef_temp i [] = [].
Proof. reflexivity. Qed.
Lemma rt_rlt_gvars i g l: remove_localdef_temp i (gvars g :: l) = gvars g :: remove_localdef_temp i l.
Proof. reflexivity. Qed.
Lemma rt_rlt_lvar i j t v l: remove_localdef_temp i (lvar j t v :: l) = lvar j t v :: remove_localdef_temp i l.
Proof. reflexivity. Qed.
Lemma rt_rlt_same i v l: remove_localdef_temp i (temp i v :: l) = remove_localdef_temp i l.
Proof. simpl. unfold rlt_ident_eq. rewrite if_true by auto. reflexivity. Qed.
Lemma rt_rlt_cons i j v l: i <> j -> remove_localdef_temp i (temp j v :: l) = temp j v :: remove_localdef_temp i l.
Proof. intros. simpl. unfold rlt_ident_eq. rewrite if_false by auto. reflexivity. Qed.

Ltac rt_rlt :=
  repeat first [ rewrite rt_rlt_nil | rewrite rt_rlt_gvars | rewrite rt_rlt_lvar | rewrite rt_rlt_same
               | rewrite rt_rlt_cons by (let X := fresh in intro X; discriminate X) ].

(* a branch the test excludes *)
Ltac rt_bad := first [ contradiction
  | match goal with H: Int.repr _ = Int.zero |- _ =>
      apply (f_equal Int.unsigned) in H; rewrite Int.unsigned_repr in H by rep_lia; discriminate H end ].

(* (tbool) (p == NULL) for a pointer p *)
Ltac rt_cmp := try match goal with |- context [sem_cmp_pp Ceq ?p _] =>
  let Hp := fresh in assert (Hp: isptr p) by (first [eapply field_compatible_isptr; eassumption | auto]);
  destruct p; try contradiction Hp; reflexivity end.

(* Moves of byte arrays and malloc tokens from the compspecs of the laws_common.h helpers (adler32's) and of the
   deflate API (DCS.CS) to the law's *)
Lemma rt_bytes_adler sh n (v: list val) q:
  @data_at Zlib.units.Adler32.CS sh (tarray tuchar n) v q = @data_at CS.CS sh (tarray tuchar n) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_adler32); [apply JMeq_refl | reflexivity]. Qed.
Lemma rt_tok_adler sh n q:
  @malloc_token Zlib.units.Adler32.CS sh (tarray tuchar n) q = @malloc_token CS.CS sh (tarray tuchar n) q.
Proof. apply equal_f; apply (@malloc_token_change_composite _ _ CC_adler32). reflexivity. Qed.
Lemma rt_bytes_dcs sh n (v: list val) q:
  @data_at Zlib.proof.deflate.DCS.CS sh (tarray tuchar n) v q = @data_at CS.CS sh (tarray tuchar n) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_dcs); [apply JMeq_refl | reflexivity]. Qed.
Lemma rt_tok_dcs sh n q:
  @malloc_token Zlib.proof.deflate.DCS.CS sh (tarray tuchar n) q = @malloc_token CS.CS sh (tarray tuchar n) q.
Proof. apply equal_f; apply (@malloc_token_change_composite _ _ CC_dcs). reflexivity. Qed.

Ltac rt_law := repeat first [ rewrite rt_bytes_adler | rewrite rt_tok_adler ].

(* ---------------------------------------------------------------------------------------------- *)
(* The segment statements (CPS: each proves its segment from the proof of the next one)          *)

Definition seg_inputs_stmt : Prop :=
  forall {Espec : OracleKind} gv vc vd,
  (forall n D dp op level wbits mem strategy,
     semax Delta_rt (rt_A9 gv vc vd n D dp op level wbits mem strategy) rt_seg9 POST_B) ->
  semax Delta_rt (rt_A0 gv vc vd) rt_seg1 POST_B.

Definition seg_init_stmt : Prop :=
  forall {Espec : OracleKind} J0 J gv vc vd n D dp op level wbits mem strategy,
  clip_dfacts J0 J ->
  (forall s tin tout adler msg msgv,
     semax Delta_rt (rt_A11 gv vc vd J0 n D dp op wbits s tin tout adler msg msgv) rt_seg11 POST_B) ->
  semax Delta_rt (rt_A9 gv vc vd n D dp op level wbits mem strategy) rt_seg9 POST_B.

Definition seg_bound_stmt : Prop :=
  forall {Espec : OracleKind} J0 J gv vc vd n D dp op wbits s tin tout adler msg msgv,
  clip_dfacts J0 J ->
  (forall b cp, semax Delta_rt (rt_LI gv vc vd J n D dp op wbits b cp) rt_seg16 POST_B) ->
  semax Delta_rt (rt_A11 gv vc vd J0 n D dp op wbits s tin tout adler msg msgv) rt_seg11 POST_B.

Definition seg_loop_stmt : Prop :=
  forall {Espec : OracleKind} J0 J gv vc vd n D dp op wbits b cp,
  clip_dfacts J0 J ->
  semax Delta_rt (rt_LB gv vc vd n D dp op wbits b cp) rt_seg17 POST_B ->
  semax Delta_rt (rt_LI gv vc vd J n D dp op wbits b cp) rt_seg16 POST_B.

Definition seg_end_stmt : Prop :=
  forall {Espec : OracleKind} gv vc vd n D dp op wbits b cp,
  (forall O, semax Delta_rt (rt_DH gv vc vd wbits n b D O dp op cp) rt_seg19 POST_B) ->
  semax Delta_rt (rt_LB gv vc vd n D dp op wbits b cp) rt_seg17 POST_B.

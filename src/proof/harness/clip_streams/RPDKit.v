(* Law rt_partial, main (MainRP.v): the deflate half of main's body (statements 1-20, 1-based: the inputs and the
   copy `expected` of the data, deflateInit2, deflateBound_z and malloc, the deflate loop, compressed_len), cut into
   CPS segments.  The C of this
   half is the same in rj_truncated's main up to the names of the temporaries and the version literal: the
   assertions and segment statements are those of RTKit.v (rj_truncated) for this program, ending at RPKit.rp_DH,
   with the copy (temp _expected ep, an object of n bytes holding the data D) carried as a frame.
   rpd_seg k is the suffix of main's chain from its k-th statement (1-based). *)
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
Require Import Zlib.proof.harness.clip_streams.RPDefs.
Require Import Zlib.proof.harness.clip_streams.RPKit.
Require Import Zlib.harness.rt_partial.code.
#[local] Existing Instance CS.CS.
Local Open Scope logic.

Ltac rpd_get_seg k :=
  let n := eval compute in (k - 1)%nat in
  let x := eval cbv beta iota zeta delta [rp_drop rp_chain f_main fn_body] in
    (rp_drop n (rp_chain (fn_body f_main))) in
  exact x.

Definition rpd_seg1 : statement := ltac:(rpd_get_seg 1%nat).
Definition rpd_seg11 : statement := ltac:(rpd_get_seg 11%nat).
Definition rpd_seg13 : statement := ltac:(rpd_get_seg 13%nat).
Definition rpd_seg18 : statement := ltac:(rpd_get_seg 18%nat).
Definition rpd_seg19 : statement := ltac:(rpd_get_seg 19%nat).
Definition rpd_seg21 : statement := ltac:(rpd_get_seg 21%nat).

Lemma rpd_seg1_eq : rpd_seg1 = rp_seg0.
Proof. reflexivity. Qed.
Lemma rpd_seg21_eq : rpd_seg21 = rp_seg20.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The assertions                                                                                *)

(* the rest of the local compressor while the deflate API holds its fields: the complement of Ews (the
   specifications' share) and the Ews share of the struct's padding *)
Definition rpd_srest (vc : val) : mpred :=
  @data_at_ CS.CS (Share.comp Ews) t_zsl vc * BoundKit.strm_pad vc.

(* the choices: data_len n, the data object dp holding D, its copy ep, the output object op, the four ints *)
Definition rpd_cf (n : Z) (D : list Z) (dp ep op : val) (level wbits mem strategy : Z) : Prop :=
  0 <= n <= max_size /\ Zlength D = n /\ is_bytes D /\ isptr dp /\ isptr ep /\ isptr op /\
  rs32 level /\ rs32 wbits /\ rs32 mem /\ rs32 strategy.

Section Assertions.
Context (gv : globals) (vc vd : val).

(* after start_function *)
Definition rpd_A0 : environ -> mpred :=
  PROP ()
  LOCAL (lvar _compressor t_zsl vc; lvar _decompressor t_zsl vd; gvars gv)
  SEP (data_at_ Tsh t_zsl vc; data_at_ Tsh t_zsl vd; mem_mgr gv; R_rp gv).

(* before statement 11 (new_stream(&compressor)): the inputs drawn, the three objects made *)
Definition rpd_A11 (n : Z) (D : list Z) (dp ep op : val) (level wbits mem strategy : Z) : environ -> mpred :=
  PROP (rpd_cf n D dp ep op level wbits mem strategy)
  LOCAL (temp _data_len (Vlong (Int64.repr n)); temp _data dp; temp _expected ep; temp _out op;
         temp _level (Vint (Int.repr level)); temp _window_bits (Vint (Int.repr wbits));
         temp _mem_level (Vint (Int.repr mem)); temp _strategy (Vint (Int.repr strategy));
         lvar _compressor t_zsl vc; lvar _decompressor t_zsl vd; gvars gv)
  SEP (data_at_ Tsh t_zsl vc; data_at_ Tsh t_zsl vd; mem_mgr gv; R_rp gv;
       malloc_token Ews (tarray tuchar n) dp; data_at Ews (tarray tuchar n) (bytes_rep D) dp;
       malloc_token Ews (tarray tuchar n) op; data_at_ Ews (tarray tuchar n) op; rp_exp n D ep).

(* before statement 13 (out_size = deflateBound_z): deflateInit2 returned Z_OK, the state s and the fields
   (tin, tout, adler, msg) satisfy J0 *)
Definition rpd_A13 (J0 : Z -> dstate -> Z -> Z -> Z -> Prop) (n : Z) (D : list Z) (dp ep op : val) (wbits : Z)
    (s : dstate) (tin tout adler : Z) (msg : option Z) (msgv : val) : environ -> mpred :=
  PROP (0 <= n <= max_size; Zlength D = n; is_bytes D; isptr dp; isptr op; rs32 wbits;
        J0 wbits s tin tout adler; d_gzhead s = None; msg_ok msg msgv; isptr ep)
  LOCAL (temp _data_len (Vlong (Int64.repr n)); temp _data dp; temp _expected ep; temp _out op;
         temp _window_bits (Vint (Int.repr wbits));
         lvar _compressor t_zsl vc; lvar _decompressor t_zsl vd; gvars gv)
  SEP (dstream 2 (Some s) vc nullval gv; api_fields vc nullval 0 tin nullval 0 tout msgv adler; rpd_srest vc;
       data_at_ Tsh t_zsl vd; mem_mgr gv; R_rp gv;
       malloc_token Ews (tarray tuchar n) dp; data_at Ews (tarray tuchar n) (bytes_rep D) dp;
       malloc_token Ews (tarray tuchar n) op; data_at_ Ews (tarray tuchar n) op; rp_exp n D ep).

(* the output object of b bytes (malloc(capacity)) after O was produced into it *)
Definition rpd_comp (b : Z) (O : list Z) (cp : val) : mpred :=
  malloc_token Ews (tarray tuchar b) cp *
  data_at Ews (tarray tuchar b) (bytes_rep O ++ Zrepeat Vundef (b - Zlength O)) cp.

(* the invariant of the do-while (statement 18) at the head of its body: pos bytes of the data consumed
   (next_in = data + pos), O produced (next_out = compressed + |O|), avail_in / avail_out as the previous call
   left them (ai, ao), J of the state and the fields *)
Definition rpd_LI (J : Z -> list Z -> Z -> Z -> list Z -> dstate -> Z -> Z -> Z -> Prop) (n : Z) (D : list Z)
    (dp ep op : val) (wbits b : Z) (cp : val) : environ -> mpred :=
  EX pos : Z, EX O : list Z, EX s : dstate, EX tin : Z, EX tout : Z, EX adler : Z, EX ai : Z, EX ao : Z,
  EX msg : option Z, EX msgv : val,
  PROP (Zlength D = n; is_bytes D; isptr dp; isptr op; isptr cp; rs32 wbits;
        J wbits D b pos O s tin tout adler; msg_ok msg msgv; isptr ep)
  LOCAL (temp _data_len (Vlong (Int64.repr n)); temp _data dp; temp _expected ep; temp _out op;
         temp _window_bits (Vint (Int.repr wbits)); temp _out_size (Vlong (Int64.repr b));
         temp _compressed cp;
         lvar _compressor t_zsl vc; lvar _decompressor t_zsl vd; gvars gv)
  SEP (dstream 2 (Some s) vc nullval gv;
       api_fields vc (offset_val pos dp) ai tin (offset_val (Zlength O) cp) ao tout msgv adler; rpd_srest vc;
       data_at_ Tsh t_zsl vd; mem_mgr gv; R_rp gv;
       malloc_token Ews (tarray tuchar n) dp; data_at Ews (tarray tuchar n) (bytes_rep D) dp;
       malloc_token Ews (tarray tuchar n) op; data_at_ Ews (tarray tuchar n) op; rpd_comp b O cp; rp_exp n D ep).

(* after the do-while (before statement 19): the last call's code; on Z_STREAM_END, O is the deflate stream of
   the data *)
Definition rpd_LB (n : Z) (D : list Z) (dp ep op : val) (wbits b : Z) (cp : val) : environ -> mpred :=
  EX code : Z, EX O : list Z, EX os : option dstate, EX nin : val, EX ai : Z, EX tin : Z, EX ao : Z, EX tout : Z,
  EX adler : Z, EX msgv : val,
  PROP (0 <= n <= max_size; Zlength D = n; is_bytes D; isptr dp; isptr op; isptr cp; rs32 wbits;
        0 <= Zlength O <= b; b <= max_u64; rbytes O; rs32 code;
        code = Z_STREAM_END -> dfinal_of wbits D O; isptr ep)
  LOCAL (temp _code (Vint (Int.repr code));
         temp _data_len (Vlong (Int64.repr n)); temp _data dp; temp _expected ep; temp _out op;
         temp _window_bits (Vint (Int.repr wbits)); temp _compressed cp;
         lvar _compressor t_zsl vc; lvar _decompressor t_zsl vd; gvars gv)
  SEP (dstream 2 os vc nullval gv;
       api_fields vc nin ai tin (offset_val (Zlength O) cp) ao tout msgv adler; rpd_srest vc;
       data_at_ Tsh t_zsl vd; mem_mgr gv; R_rp gv;
       malloc_token Ews (tarray tuchar n) dp; data_at Ews (tarray tuchar n) (bytes_rep D) dp;
       malloc_token Ews (tarray tuchar n) op; data_at_ Ews (tarray tuchar n) op; rpd_comp b O cp; rp_exp n D ep; TT).

(* the hand-over to the inflate half (before statement 21): RPKit.rp_DH *)
Definition rpd_DH (wbits n b : Z) (D O : list Z) (dp ep op cp : val) : environ -> mpred :=
  rp_DH wbits n b D O dp ep op cp vc vd gv.

End Assertions.


(* ---------------------------------------------------------------------------------------------- *)
(* Tactic support                                                                                *)

(* Floyd's simplify_remove_localdef_temp (simpl on rlt_ident_eq of the large $"..." identifiers) takes minutes
   after a call that stores into a temp: remove the temp by rewriting instead *)
Lemma rpd_rlt_nil i: remove_localdef_temp i [] = [].
Proof. reflexivity. Qed.
Lemma rpd_rlt_gvars i g l: remove_localdef_temp i (gvars g :: l) = gvars g :: remove_localdef_temp i l.
Proof. reflexivity. Qed.
Lemma rpd_rlt_lvar i j t v l: remove_localdef_temp i (lvar j t v :: l) = lvar j t v :: remove_localdef_temp i l.
Proof. reflexivity. Qed.
Lemma rpd_rlt_same i v l: remove_localdef_temp i (temp i v :: l) = remove_localdef_temp i l.
Proof. simpl. unfold rlt_ident_eq. rewrite if_true by auto. reflexivity. Qed.
Lemma rpd_rlt_cons i j v l: i <> j -> remove_localdef_temp i (temp j v :: l) = temp j v :: remove_localdef_temp i l.
Proof. intros. simpl. unfold rlt_ident_eq. rewrite if_false by auto. reflexivity. Qed.

Ltac rpd_rlt :=
  repeat first [ rewrite rpd_rlt_nil | rewrite rpd_rlt_gvars | rewrite rpd_rlt_lvar | rewrite rpd_rlt_same
               | rewrite rpd_rlt_cons by (let X := fresh in intro X; discriminate X) ].

(* a branch the test excludes *)
Ltac rpd_bad := first [ contradiction
  | match goal with H: Int.repr _ = Int.zero |- _ =>
      apply (f_equal Int.unsigned) in H; rewrite Int.unsigned_repr in H by rep_lia; discriminate H end ].

(* (tbool) (p == NULL) for a pointer p *)
Ltac rpd_cmp := try match goal with |- context [sem_cmp_pp Ceq ?p _] =>
  let Hp := fresh in assert (Hp: isptr p) by (first [eapply field_compatible_isptr; eassumption | auto]);
  destruct p; try contradiction Hp; reflexivity end.

(* Moves of byte arrays and malloc tokens from the compspecs of the laws_common.h helpers (adler32's) and of the
   deflate API (DCS.CS) to the law's *)
Lemma rpd_bytes_adler sh n (v: list val) q:
  @data_at Zlib.units.Adler32.CS sh (tarray tuchar n) v q = @data_at CS.CS sh (tarray tuchar n) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_adler32); [apply JMeq_refl | reflexivity]. Qed.
Lemma rpd_tok_adler sh n q:
  @malloc_token Zlib.units.Adler32.CS sh (tarray tuchar n) q = @malloc_token CS.CS sh (tarray tuchar n) q.
Proof. apply equal_f; apply (@malloc_token_change_composite _ _ CC_adler32). reflexivity. Qed.
Lemma rpd_bytes_dcs sh n (v: list val) q:
  @data_at Zlib.proof.deflate.DCS.CS sh (tarray tuchar n) v q = @data_at CS.CS sh (tarray tuchar n) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_dcs); [apply JMeq_refl | reflexivity]. Qed.
Lemma rpd_tok_dcs sh n q:
  @malloc_token Zlib.proof.deflate.DCS.CS sh (tarray tuchar n) q = @malloc_token CS.CS sh (tarray tuchar n) q.
Proof. apply equal_f; apply (@malloc_token_change_composite _ _ CC_dcs). reflexivity. Qed.

Ltac rpd_law := repeat first [ rewrite rpd_bytes_adler | rewrite rpd_tok_adler ].

(* ---------------------------------------------------------------------------------------------- *)
(* The segment statements (CPS: each proves its segment from the proof of the next one)          *)

Definition rpd_inputs_stmt : Prop :=
  forall {Espec : OracleKind} gv vc vd,
  (forall n D dp ep op level wbits mem strategy,
     semax Delta_rp (rpd_A11 gv vc vd n D dp ep op level wbits mem strategy) rpd_seg11 POST_B) ->
  semax Delta_rp (rpd_A0 gv vc vd) rpd_seg1 POST_B.

Definition rpd_init_stmt : Prop :=
  forall {Espec : OracleKind} J0 J gv vc vd n D dp ep op level wbits mem strategy,
  clip_dfacts J0 J ->
  (forall s tin tout adler msg msgv,
     semax Delta_rp (rpd_A13 gv vc vd J0 n D dp ep op wbits s tin tout adler msg msgv) rpd_seg13 POST_B) ->
  semax Delta_rp (rpd_A11 gv vc vd n D dp ep op level wbits mem strategy) rpd_seg11 POST_B.

Definition rpd_bound_stmt : Prop :=
  forall {Espec : OracleKind} J0 J gv vc vd n D dp ep op wbits s tin tout adler msg msgv,
  clip_dfacts J0 J ->
  (forall b cp, semax Delta_rp (rpd_LI gv vc vd J n D dp ep op wbits b cp) rpd_seg18 POST_B) ->
  semax Delta_rp (rpd_A13 gv vc vd J0 n D dp ep op wbits s tin tout adler msg msgv) rpd_seg13 POST_B.

Definition rpd_loop_stmt : Prop :=
  forall {Espec : OracleKind} J0 J gv vc vd n D dp ep op wbits b cp,
  clip_dfacts J0 J ->
  semax Delta_rp (rpd_LB gv vc vd n D dp ep op wbits b cp) rpd_seg19 POST_B ->
  semax Delta_rp (rpd_LI gv vc vd J n D dp ep op wbits b cp) rpd_seg18 POST_B.

Definition rpd_end_stmt : Prop :=
  forall {Espec : OracleKind} gv vc vd n D dp ep op wbits b cp,
  (forall O, semax Delta_rp (rpd_DH gv vc vd wbits n b D O dp ep op cp) rpd_seg21 POST_B) ->
  semax Delta_rp (rpd_LB gv vc vd n D dp ep op wbits b cp) rpd_seg19 POST_B.

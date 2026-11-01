(* Law res_memory_deflate: main's body after deflateInit2_ and the check that it returned Z_OK, or Z_MEM_ERROR
   after a failed allocation (MemPrefix.v proves main up to there): the assertion [mid_pre] at that point, the rest of the
   prefix [msuf11] (the return unless Z_OK, w, read = 0, then the loop), and the return when deflateInit2_
   made no state ([mid_fail]).  MemPrefixOk.v continues the case Z_OK to the loop invariant. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.za.deflate.Stmt.
Require Import Zlib.proof.deflate.AnyCalls.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.counted.Spec.
Require Import Zlib.proof.harness.counted.Kit.
Require Import Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.harness.res_alloc_deflate.ACS.
Require Import Zlib.proof.harness.res_alloc_deflate.Specs.
Require Import Zlib.proof.harness.res_alloc_deflate.Gmain.
Require Import Zlib.proof.harness.res_alloc_deflate.InitFacts.
Require Import Zlib.proof.harness.res_alloc_deflate.StrmKit.
Require Import Zlib.proof.harness.res_alloc_deflate.MainKit.
Require Import Zlib.proof.harness.res_memory_deflate.Peak.
Require Import Zlib.proof.harness.res_memory_deflate.PeakExact.
Require Import Zlib.proof.harness.res_memory_deflate.MainStmt.
Require Import Zlib.proof.harness.res_memory_deflate.MemKit.
Require Zlib.proof.deflate.LawFacts Zlib.proof.deflate.LTApiInit Zlib.proof.deflate.LTCInitKit.
Require Zlib.contracts.res_memory_deflate.
Require Import Zlib.harness.res_memory_deflate.code.
Local Open Scope logic.
Local Ltac simplify_remove_localdef_temp ::= mem_simplify_rlt.

(* main's body from the test code != Z_OK on: statements 11 to 16 of main_body, then the loop *)
Definition msuf11 : statement := ltac:(get_msuf 11%nat).

(* after gp_assert(code == Z_OK || (code == Z_MEM_ERROR && count.failed)): deflateInit2_'s outcome (the state [os], the stream
   [z1], the code, the allocator's events [tr]), main's draws and the data, the struct count as main reads it *)
Definition mid_pre (gv : globals) (cp p dp : val) (bs : list Z) (level wbits mem strategy : Z)
    (os : option dstate) (z1 : strm) (code : Z) (tr : list zev) : environ -> mpred :=
  PROP ()
  LOCAL (temp _t'9 (Vint (Int.repr 1)); temp _code (Vint (Int.repr code)); temp _t'8 (vi code);
         temp _data dp; temp _t'7 dp; temp _data_len (Vlong (Int64.repr (Zlength bs)));
         temp _strategy (Vint (Int.repr strategy)); temp _mem_level (Vint (Int.repr mem));
         temp _window_bits (Vint (Int.repr wbits)); temp _level (Vint (Int.repr level));
         lvar _count__1 (Tstruct _count noattr) cp; lvar _strm (Tstruct _z_stream_s noattr) p; gvars gv)
  SEP (match os with
       | Some _ => @dstream_za (kc (mc gv cp)) 2 os p nullval gv
       | None =>
           EX st : val, EX dt' : val,
           !! (code = Z_VERSION_ERROR -> st = Vundef) &&
           (@za_funcs DCS.CS (kc (mc gv cp)) *
            @field_at_ DCS.CS Ews t_strm (DOT Zlib.deflate.code._reserved) p *
            @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._state) st p *
            @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._zalloc) (@za_alloc (kc (mc gv cp))) p *
            @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._zfree) (@za_free (kc (mc gv cp))) p *
            @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._opaque) (@za_opaque (kc (mc gv cp))) p *
            @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._data_type) dt' p)
       end;
       @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._next_in) nullval p;
       EX msgv' : val,
       !! (if code =? Z_VERSION_ERROR then msgv' = Vundef else msg_ok (z_msg z1) msgv') &&
       reset_fields p (rfv (code =? Z_OK) (z_total_in z1) Vundef) (rfv (code =? Z_OK) (z_total_out z1) Vundef)
         msgv' (rfv (code =? Z_OK) (z_adler z1) Vundef);
       @data_at DCS.CS Ers (tarray tschar (Zlength [49; 46; 51; 46; 50; 0])) (map vi [49; 46; 51; 46; 50; 0])
         (gv ___stringlit_res_memory_deflate_1);
       mem_mgr gv;
       @data_at CSa Tsh (Tstruct HC._count noattr)
         (Vlong (Int64.repr (fst (cnt tr))), (Vlong (Int64.repr (snd (cnt tr))), Vint (Int.repr (cnt_failed tr))))
         cp;
       deflate_globals gv;
       @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._avail_in) (Vint (Int.repr 0)) p;
       @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._next_out) nullval p;
       @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._avail_out) (Vint (Int.repr 0)) p;
       strm_pad p; @data_at_ Zlib.units.Compress.CS Ecomp t_zs p;
       @malloc_token Zlib.units.Adler32.CS Ews (tarray tuchar (Zlength bs)) dp;
       @data_at Zlib.units.Adler32.CS Ews (tarray tuchar (Zlength bs)) (bytes_rep bs) dp).

(* main's body from code = _t'8 on: the assignment, then statements 10 to 16 of main_body and the loop *)
Definition s_code : statement := ltac:(let x := eval cbv beta iota zeta delta [suf main_body] in
  (match suf 9 main_body with Ssequence (Ssequence _ a) _ => a | _ => Sskip end) in exact x).
Definition msuf10 : statement := ltac:(get_msuf 10%nat).

(* right after the call of deflateInit2_ (its result in the temporary _t'8): the counting allocator's state as
   deflateInit2_'s specification leaves it *)
Definition call_post (gv : globals) (cp p dp : val) (bs : list Z) (level wbits mem strategy : Z)
    (os : option dstate) (z1 : strm) (code : Z) (tr : list zev) : environ -> mpred :=
  PROP ()
  LOCAL (temp _t'8 (vi code); temp _data dp; temp _t'7 dp; temp _data_len (Vlong (Int64.repr (Zlength bs)));
         temp _strategy (Vint (Int.repr strategy)); temp _mem_level (Vint (Int.repr mem));
         temp _window_bits (Vint (Int.repr wbits)); temp _level (Vint (Int.repr level));
         lvar _count__1 (Tstruct _count noattr) cp; lvar _strm (Tstruct _z_stream_s noattr) p; gvars gv)
  SEP (match os with
       | Some _ => @dstream_za (kc (mc gv cp)) 2 os p nullval gv
       | None =>
           EX st : val, EX dt' : val,
           !! (code = Z_VERSION_ERROR -> st = Vundef) &&
           (@za_funcs DCS.CS (kc (mc gv cp)) *
            @field_at_ DCS.CS Ews t_strm (DOT Zlib.deflate.code._reserved) p *
            @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._state) st p *
            @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._zalloc) (@za_alloc (kc (mc gv cp))) p *
            @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._zfree) (@za_free (kc (mc gv cp))) p *
            @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._opaque) (@za_opaque (kc (mc gv cp))) p *
            @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._data_type) dt' p)
       end;
       @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._next_in) nullval p;
       EX msgv' : val,
       !! (if code =? Z_VERSION_ERROR then msgv' = Vundef else msg_ok (z_msg z1) msgv') &&
       reset_fields p (rfv (code =? Z_OK) (z_total_in z1) Vundef) (rfv (code =? Z_OK) (z_total_out z1) Vundef)
         msgv' (rfv (code =? Z_OK) (z_adler z1) Vundef);
       @data_at DCS.CS Ers (tarray tschar (Zlength [49; 46; 51; 46; 50; 0])) (map vi [49; 46; 51; 46; 50; 0])
         (gv ___stringlit_res_memory_deflate_1);
       @za_res (kc (mc gv cp)) gv tr;
       deflate_globals gv;
       @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._avail_in) (Vint (Int.repr 0)) p;
       @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._next_out) nullval p;
       @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._avail_out) (Vint (Int.repr 0)) p;
       strm_pad p; @data_at_ Zlib.units.Compress.CS Ecomp t_zs p;
       @malloc_token Zlib.units.Adler32.CS Ews (tarray tuchar (Zlength bs)) dp;
       @data_at Zlib.units.Adler32.CS Ews (tarray tuchar (Zlength bs)) (bytes_rep bs) dp).


(* For parameters in zlib.h's ranges, deflateInit2_ returns Z_OK or Z_MEM_ERROR: Z_STREAM_ERROR is its answer to
   rejected parameters only. *)
Lemma init_code_valid level method wbits mem strategy a1 a2 a3 a4 a5 z r :
  Zlib.proof.deflate.LawFacts.params_ok level method wbits mem strategy = true ->
  c_deflateInit2_ true true false level method wbits mem strategy a1 a2 a3 a4 a5 z = Some r ->
  snd r = Z_OK \/ snd r = Z_MEM_ERROR.
Proof.
  intros P H. rewrite Zlib.proof.deflate.LTApiInit.init_shape in H. rewrite P in H.
  destruct a1. 2:{ inversion H; subst r; cbn; auto. }
  destruct (a2 && a3 && a4 && a5)%bool. 2:{ inversion H; subst r; cbn; auto. }
  rewrite (Zlib.proof.deflate.LTCInitKit.init_eq _ _ _ _ _ _ P) in H.
  inversion H; subst r. cbn; auto.
Qed.

(* gp_assert(code == Z_OK || (code == Z_MEM_ERROR && count.failed)) holds: for the parameters main assumed
   (deflate_params_ok), deflateInit2_ returns Z_OK or Z_MEM_ERROR ([init_code_valid]), and Z_MEM_ERROR only after
   a failed allocation, which sets count.failed ([za_failed]); then main goes on at [mid_pre] *)
Lemma mid_check {Espec : OracleKind} (gv : globals) (cp p dp : val) (bs : list Z) (level wbits mem strategy : Z)
    (a1 a2 a3 a4 a5 : bool) (os : option dstate) (z1 : strm) (code : Z) (tr : list zev) :
  Zlib.proof.deflate.LawFacts.params_ok level 8 wbits mem strategy = true ->
  c_deflateInit2_ true true false level 8 wbits mem strategy a1 a2 a3 a4 a5 zrst0 = Some (os, z1, code) ->
  match os with
  | Some s => tr = [] ++ dinit_events s
  | None => za_now tr = za_now [] /\ (code = Z_MEM_ERROR -> za_failed tr = true)
  end ->
  @semax CSa Espec Delta_m (mid_pre gv cp p dp bs level wbits mem strategy os z1 code tr) msuf11 POST_m ->
  @semax CSa Espec Delta_m (call_post gv cp p dp bs level wbits mem strategy os z1 code tr) (Ssequence s_code msuf10)
    POST_m.
Proof.
  intros P HI H0 Hnext.
  pose proof (init_code_valid _ _ _ _ _ _ _ _ _ _ _ _ P HI) as Hcv. cbn [snd] in Hcv.
  unfold Z_OK, Z_MEM_ERROR in Hcv.
  assert (Hf : code = -4 -> cnt_failed tr = 1).
  { intros E. destruct os as [s | ].
    - destruct (init_some _ _ _ _ _ _ _ _ _ _ _ _ _ _ HI) as [Ec _]. subst code. discriminate.
    - destruct H0 as [_ H0]. unfold cnt_failed. rewrite H0 by exact E. reflexivity. }
  clear H0.
  unfold call_post, s_code, msuf10, Delta_m, POST_m. abbreviate_semax.
  forward.
  change (@za_res (kc (mc gv cp)) gv tr) with (count_res cp gv tr).
  unfold count_res. rewrite count_local. Intros.
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp _t'9 (Vint (Int.repr 1)) :: Q) (SEPx R))) end.
  { forward. entailer!. }
  { match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx (temp _t'9 (Vint (Int.repr 1)) :: Q) (SEPx R))) end.
    { rewrite Int.neg_repr in H0. apply repr_inj_signed in H0; [ | rep_lia | rep_lia]. rewrite (Hf H0).
      forward. forward. forward. entailer!. rewrite Hf by reflexivity. cancel. }
    { exfalso.
      destruct Hcv as [E | E]; subst code; [apply H; reflexivity | apply H0; reflexivity]. } }
  abbreviate_semax. forward_call (Int.repr 1).
  exact Hnext.
Qed.

(* deflateInit2_ made no state (its code is not Z_OK): main returns 0, its locals back as it got them *)
Lemma mid_fail {Espec : OracleKind} (gv : globals) (cp p dp : val) (bs : list Z) (level wbits mem strategy : Z)
    (z1 : strm) (code : Z) (tr : list zev) :
  -4 <= code <= 0 -> code <> Z_OK ->
  @semax CSa Espec Delta_m (mid_pre gv cp p dp bs level wbits mem strategy None z1 code tr) msuf11 POST_m.
Proof.
  intros Hcr Hc. unfold mid_pre, msuf11, Delta_m, POST_m. abbreviate_semax.
  Intros st0 dt' msgv'.
  forward_if.
  { forward. Exists (Int.repr 0).
    sep_apply (@init_fail_back (kc (mc gv cp))).
    sep_apply strm_back.
    entailer!. }
  { exfalso. apply Hc. unfold Z_OK in *. lia. }
Qed.

(* Law res_memory_deflate: main's body up to the loop (MemKit.prefix_stmt): the draws of deflateInit2's
   parameters and the assumption that they are in zlib.h's ranges (deflate_params_ok, laws_session.h), data_len =
   upto(PTRDIFF_MAX) and the data, counted_stream and deflateInit2_; then the check that it returned Z_OK, or
   Z_MEM_ERROR after a failed allocation (MemPrefixKit.mid_check), and the two outcomes of deflateInit2_: the
   return when it made no state (MemPrefixKit.mid_fail), and w, read = 0 and the loop invariant on Z_OK
   (MemPrefixOk.mid_ok). *)
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
Require Import Zlib.proof.harness.res_memory_deflate.MemPrefixKit.
Require Import Zlib.proof.harness.res_memory_deflate.MemPrefixOk.
Require Zlib.proof.deflate.LawFacts.
Require Zlib.proof.harness.laws_session.Spec Zlib.proof.harness.laws_session.Facts.
Require Zlib.contracts.res_memory_deflate.
Require Import Zlib.harness.res_memory_deflate.code.
Local Open Scope logic.
Local Ltac simplify_remove_localdef_temp ::= mem_simplify_rlt.

Lemma mem_prefix : prefix_stmt.
Proof.
  intros Espec K cp p gv AC Hk. unfold PRE0, main_body, Delta_m, POST_m. abbreviate_semax.
  forward_call tt. Intros lv.
  abbreviate_semax. forward_call tt. Intros wb.
  abbreviate_semax. forward_call tt. Intros ml.
  abbreviate_semax. forward_call tt. Intros st.
  rewrite (vint_signed lv), (vint_signed wb), (vint_signed ml), (vint_signed st).
  pose proof (Int.signed_range (Int.repr lv)) as Rl. pose proof (Int.signed_range (Int.repr wb)) as Rw.
  pose proof (Int.signed_range (Int.repr ml)) as Rm. pose proof (Int.signed_range (Int.repr st)) as Rs.
  set (level := Int.signed (Int.repr lv)) in *. set (wbits := Int.signed (Int.repr wb)) in *.
  set (mem := Int.signed (Int.repr ml)) in *. set (strategy := Int.signed (Int.repr st)) in *.
  clearbody level wbits mem strategy. clear lv wb ml st H H0 H1 H2.
  (* gp_assume(deflate_params_ok(level, window_bits, mem_level, strategy)): the parameters are accepted *)
  abbreviate_semax. rewrite <- seq_assoc. forward_call (level, wbits, mem, strategy).
  destruct (Zlib.proof.harness.laws_session.Spec.deflate_params_valid level wbits mem strategy) eqn:Ev.
  2:{ forward_call Int.zero. Intros. contradiction. }
  forward_call Int.one. Intros. match goal with Hx : Int.one <> Int.zero |- _ => clear Hx end.
  (* deflate_params_ok's test is deflateInit2_'s parameter check with method Z_DEFLATED *)
  assert (Pok : Zlib.proof.deflate.LawFacts.params_ok level 8 wbits mem strategy = true)
    by (rewrite <- Zlib.proof.harness.laws_session.Facts.deflate_params_valid_ok; exact Ev).
  clear Ev.
  (* the result of deflate_params_ok is not used again *)
  match goal with |- semax _ (PROPx ?P (LOCALx (temp _t'5 _ :: ?Q) (SEPx ?R))) _ _ =>
    apply semax_pre with (PROPx P (LOCALx Q (SEPx R))); [entailer! | ] end.
  abbreviate_semax. forward_call (9223372036854775807). Intros n.
  abbreviate_semax. rewrite <- seq_assoc. forward_call (n, gv). Intros vret. destruct vret as [dp bs]. cbn [fst snd] in *.
  forward.
  destruct (eq_dec dp nullval) as [Ed | Nd].
  { subst dp. forward_if.
    { forward. Exists (Int.repr 0). entailer!. }
    { contradiction. } }
  forward_if.
  { apply (@malloc_test_eq Zlib.units.Adler32.CS _ (Zlength bs)); [rep_lia | ].
    sep_apply (@data_at_data_at_ Zlib.units.Adler32.CS). cancel. }
  { contradiction. }
  rewrite strm_local, count_local_.
  abbreviate_semax.
  forward_call (p, Tsh, cp, gv, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef,
                Vundef, Vundef, Vundef, Vundef, Vundef, Vundef).
  match goal with |- context [@data_at _ Tsh t_zs ?v p] =>
    sep_apply (@data_at_Tsh_split Zlib.units.Compress.CS t_zs v p) end.
  sep_apply zs_init_pre.
  make_func_ptr HC._counted_alloc. make_func_ptr HC._counted_free.
  match goal with |- context [func_ptr' ?f (gv HC._counted_alloc)] =>
    change (func_ptr' f (gv HC._counted_alloc)) with (func_ptr' (snd count_alloc_spec) (gv HC._counted_alloc)) end.
  match goal with |- context [func_ptr' ?f (gv HC._counted_free)] =>
    change (func_ptr' f (gv HC._counted_free)) with (func_ptr' (snd count_free_spec) (gv HC._counted_free)) end.
  assert_PROP (isptr (gv HC._counted_alloc)) as Pza.
  { sep_apply (func_ptr'_isptr (snd count_alloc_spec) (gv HC._counted_alloc)). entailer!. }
  assert_PROP (isptr (gv HC._counted_free)) as Pzf.
  { sep_apply (func_ptr'_isptr (snd count_free_spec) (gv HC._counted_free)). entailer!. }
  sep_apply (counted_pieces cp (gv HC._counted_alloc) (gv HC._counted_free) gv).
  unfold Ra, version_at. Intros.
  assert_PROP (isptr cp) as Pcp by entailer!.
  change (counted cp (gv HC._counted_alloc) (gv HC._counted_free))
    with (kc (cp, gv HC._counted_alloc, gv HC._counted_free)).
  abbreviate_semax. rewrite <- seq_assoc.
  forward_call ((cp, gv HC._counted_alloc, gv HC._counted_free),
    (p, level, 8, wbits, mem, strategy, gv ___stringlit_res_memory_deflate_1, Ers, [49; 46; 51; 46; 50; 0], 112,
     nullval, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, gv, @nil zev)).
  { split; [unfold s32_ok; rep_lia | ]. split; [unfold s32_ok; rep_lia | ].
    split; [rewrite Zlength_correct; simpl; lia | ].
    split; [cbn; lia | ]. split; [intros; apply init_total | ].
    cbn. repeat split;
      first [ intro E; rewrite E in Pza; contradiction | intro E; rewrite E in Pzf; contradiction
            | apply isptr_is_pointer_or_null; auto | lia ]. }
  Intros vret. destruct vret as [[[[[[a1 a2] a3] a4] a5] [[os z1] code]] tr]. cbn [fst snd] in *.
  change (Znth 0 [49; 46; 51; 46; 50; 0] =? 49) with true in *. change (112 =? 112) with true in *.
  match goal with H : c_deflateInit2_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _ |- _ => rename H into HI end.
  pose proof (init_code_range _ _ _ _ _ _ _ _ _ _ _ _ HI) as Hcr. cbn [snd] in Hcr.
  subst n. apply (mid_check gv cp p dp bs level wbits mem strategy a1 a2 a3 a4 a5 os z1 code tr Pok HI H4).
  destruct os as [s | ].
  - destruct (init_some _ _ _ _ _ _ _ _ _ _ _ _ _ _ HI) as [Ec _]. subst code.
    exact (mid_ok K gv cp p dp bs level wbits mem strategy a1 a2 a3 a4 a5 s z1 tr AC Hk H H1 Rl Rw Rm Rs HI H4).
  - apply (mid_fail gv cp p dp bs level wbits mem strategy z1 code tr Hcr).
    exact (init_none_code _ _ _ _ _ _ _ _ _ _ _ _ HI eq_refl).
Qed.

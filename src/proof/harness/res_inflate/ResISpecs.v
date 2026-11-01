(* Laws res_free_inflate and res_memory_inflate: the specifications of main's callees and the statement of
   main's body proofs.

   inflate.c's functions have one specification each in the law's program: the uspecs of
   src/proof/za/inflate_api/USpec.v for the family [Ac] of counting allocators (the struct count, count_alloc,
   count_free: src/proof/harness/counted/Spec.v), an intersection over the index (allocator, adler cell).  For
   main's calls the context holds [zsig] instead: the specification whose WITH is the pair of the index and the
   member's WITH (the caller picks the allocator, main's own struct count, and the adler cell at each call).
   Each uspec is a subspecification of its zsig ([zsig_sub]), from the hypothesis that a uspec gives each of
   its members (USpec.za_uspec_sub_stmt). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.za.inflate_api.USpec.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.counted.Spec.
Require Zlib.proof.harness.laws_session.Spec.
Require Import Zlib.proof.harness.res_inflate.ResICS.
Require Zlib.units.Inflate.
Require Zlib.contracts.res_free_inflate Zlib.contracts.res_memory_inflate.
Require Zlib.harness.res_free_inflate.code Zlib.harness.res_memory_inflate.code.

(* the counting allocators, indexed by (the struct count, count_alloc, count_free) *)
Definition Ac (k : val * val * val) : zallocator :=
  let '(cp, za, zf) := k in counted cp za zf.

(* the index of the counting allocator of main's struct count at cp, and the adler cell (undef: a raw
   stream, whose strm->adler inflateInit2_ leaves undefined) *)
Definition ix (cp za zf : val) (undef : bool) : @zai (val * val * val) := ((cp, za, zf), undef).

Lemma ix_a cp za zf u : zai_a Ac (ix cp za zf u) = counted cp za zf.
Proof. reflexivity. Qed.

(* the specification with WITH (index, the member's WITH) *)
Definition zsig (sig : compcert_rmaps.typesig) (cc : calling_convention) (A : Type)
    (P : @zai (val * val * val) -> A -> argsEnviron -> mpred) (Q : @zai (val * val * val) -> A -> environ -> mpred)
    : funspec :=
  NDmk_funspec sig cc (@zai (val * val * val) * A) (fun x => P (fst x) (snd x)) (fun x => Q (fst x) (snd x)).

Lemma zsig_sub sig cc A P Q (U : funspec) :
  (forall i, funspec_sub U (NDmk_funspec sig cc A (P i) (Q i))) -> funspec_sub U (zsig sig cc A P Q).
Proof.
  intros H. pose proof (H ((nullval, nullval, nullval), false)) as H0.
  destruct U as [sigU ccU AU PU QU PUne QUne]. unfold funspec_sub, zsig, NDmk_funspec in *.
  destruct H0 as [E _]. split; [exact E | ].
  intros ts2 [i x2] gargs. destruct (H i) as [_ Hi]. exact (Hi ts2 x2 gargs).
Qed.

(* [zi_any F H]: the zsig of a family of DECLARE ... WITH specifications [F ZA ZAV], defined by the constant H *)
Ltac zi_any F H :=
  let t0 := eval cbv delta [H] beta in (F za0 av_defined) in
  lazymatch t0 with
  | (?i, NDmk_funspec ?sig ?cc ?A _ _) =>
    exact (i, zsig sig cc A
      (fun j => ltac:(let t := eval cbv delta [H] beta in (F (zai_a Ac j) (zai_v j)) in
                      lazymatch t with (_, NDmk_funspec _ _ _ ?P _) => exact P end))
      (fun j => ltac:(let t := eval cbv delta [H] beta in (F (zai_a Ac j) (zai_v j)) in
                      lazymatch t with (_, NDmk_funspec _ _ _ _ ?Q) => exact Q end)))
  end.

Definition inflateInit2__spec_c : ident * funspec :=
  ltac:(zi_any (fun (ZA : zallocator) (_ : adler_cell) => @inflateInit2__spec_za ZA) @inflateInit2__spec_za).
Definition inflate_spec_c : ident * funspec := ltac:(zi_any (@inflate_spec_za) @inflate_spec_za).
Definition inflateEnd_spec_c : ident * funspec := ltac:(zi_any (@inflateEnd_spec_za) @inflateEnd_spec_za).

(* each uspec is a subspecification of its zsig *)
Section Subs.
Hypothesis HS : za_uspec_sub_stmt Ac.

Lemma inflateInit2__sub : funspec_sub (snd (inflateInit2__uspec Ac)) (snd inflateInit2__spec_c).
Proof. apply zsig_sub. intros i. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (HS i))))))). Qed.
Lemma inflate_sub : funspec_sub (snd (inflate_uspec Ac)) (snd inflate_spec_c).
Proof. apply zsig_sub. intros i. exact (proj1 (HS i)). Qed.
Lemma inflateEnd_sub : funspec_sub (snd (inflateEnd_uspec Ac)) (snd inflateEnd_spec_c).
Proof. apply zsig_sub. intros i. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (HS i)))))))))). Qed.
End Subs.

(* main's callees: res_memory_inflate's main (Gmain, with laws_session.h's inflate_window_ok), and
   res_free_inflate's (Gmain_free: its program has no inflate_window_ok, upto, clip or nondet_u8, which its main
   does not call) *)
Definition Gmain_free : funspecs :=
  [inflateInit2__spec_c; inflate_spec_c; inflateEnd_spec_c;
   any_bytes_spec; offer_spec;
   counted_stream_spec; count_alloc_spec; count_free_spec;
   (_quickproof_malloc, @malloc_spec' CSi); (_quickproof_free, @free_spec' CSi);
   nondet_u32_spec; gp_assert_spec].

Definition Gmain : funspecs :=
  [Zlib.proof.harness.laws_session.Spec.inflate_window_ok_spec;
   inflateInit2__spec_c; inflate_spec_c; inflateEnd_spec_c;
   upto_spec; clip_spec; any_bytes_spec; offer_spec;
   counted_stream_spec; count_alloc_spec; count_free_spec;
   (_quickproof_malloc, @malloc_spec' CSi); (_quickproof_free, @free_spec' CSi);
   nondet_u32_spec; nondet_u8_spec; gp_assert_spec; gp_assume_spec].

(* the harness's "1.3.2" (the version argument of the inflateInit2 macro), at the inflate unit's compspecs (as
   inflateInit2__spec takes the caller's version) *)
Definition hver_vals : list val := map (fun c => Vint (Int.repr c)) [49; 46; 51; 46; 50; 0].

Definition hversion_lit (lit : ident) (gv : globals) : mpred :=
  @data_at Zlib.units.Inflate.CS Ers (tarray tschar (Zlength hver_vals)) hver_vals (gv lit).

(* the globals main gets: inflate()'s read-only tables (fixed codes, order, inftrees' bases and extras),
   crc32's table, inflate.c's ZLIB_VERSION literal and the harness's [lit] *)
Definition Ri (lit : ident) (gv : globals) : mpred :=
  (tables_rep Ers gv * crc_table_at Ers gv * version_lit gv * hversion_lit lit gv)%logic.

(* main's body proofs *)
Definition main_free_stmt : Prop :=
  @semax_body (QPvarspecs Zlib.contracts.res_free_inflate.whole_prog) Gmain_free CSi
    Zlib.harness.res_free_inflate.code.f_main
    (Zlib.harness.res_free_inflate.code._main,
     main_core_spec (Ri Zlib.harness.res_free_inflate.code.___stringlit_res_free_inflate_1)).

Definition main_memory_stmt : Prop :=
  @semax_body (QPvarspecs Zlib.contracts.res_memory_inflate.whole_prog) Gmain CSi
    Zlib.harness.res_memory_inflate.code.f_main
    (Zlib.harness.res_memory_inflate.code._main,
     main_core_spec (Ri Zlib.harness.res_memory_inflate.code.___stringlit_res_memory_inflate_1)).

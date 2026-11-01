(* The allocator-generic specifications of inflate.c (src/proof/za/inflate_api/Stmt.v) as ONE specification
   per function, for the programs that link inflate.c: a program's context has one specification per
   function, while a caller's allocator may depend on the caller's state (the counting allocator of the
   res_* laws has its counters in a local struct of main; zcalloc's resource is mem_mgr gv).

   [uspec phi] is VST's general_intersection of the family phi over the allocator and the adler cell: its
   WITH is the dependent pair of an index (ZA, ZAV) and the WITH of phi (ZA, ZAV); it is a funspec_sub of each
   member (generalintersection_sub) and its body follows from the bodies of all members in one context
   (semax_body_generalintersection).  The contexts GU_* are the generated contexts with every
   allocator-dependent callee replaced by its uspec.

   [za_inflate_ulib_stmt] is what the clients of inflate.c with any allocator use (the res_* inflate laws,
   and, at the zcalloc instance, the wide specifications of src/proof/inflate_api/SpecW.v); it follows from
   the bodies of the port (Stmt.v) by [za_inflate_ulib] (ULib.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Export Zlib.proof.za.inflate_api.Stmt.
Require Import Zlib.proof.inffast.Body.
Require Export Zlib.proof.zutil.ZAlloc.
Require Export Zlib.proof.za.inflate.ZAV.
#[local] Existing Instance Zlib.units.Inflate.CS.

(* some allocator (to name the signature of a family, which does not depend on the allocator) *)
Definition za0 : zallocator := ZAllocator nullval nullval nullval (fun _ _ => emp) (fun _ _ _ => emp) 0.

Section USpecs.
(* The allocators of a client: a family A of allocators indexed by a small type K (an index of
   general_intersection must be small; zallocator holds mpreds): the counting allocator is indexed by the
   struct count and the two functions, zcalloc's by the globals. *)
Context {K : Type} (A : K -> zallocator).

(* the index of the family: the allocator's index and the adler cell (strm->adler undefined or not) *)
Definition zai : Type := (K * bool)%type.
Definition zai_a (i : zai) : zallocator := A (fst i).
Definition zai_v (i : zai) : adler_cell := AdlerCell (snd i).

Definition uspec (phi : zai -> funspec) (sig : compcert_rmaps.typesig) (cc : calling_convention)
  (Hsig : forall i, typesig_of_funspec (phi i) = sig)
  (Hcc : forall i, callingconvention_of_funspec (phi i) = cc) : funspec :=
  general_intersection phi Hsig Hcc.

(* the uspec of each generated specification: its family at the indices, the signature at za0 (the
   signature and calling convention of the members do not depend on the index) *)
Lemma inflate_sig : forall i : zai, typesig_of_funspec (snd (@inflate_spec_za (zai_a i) (zai_v i))) = typesig_of_funspec (snd (@inflate_spec_za za0 av_defined)).
Proof. intros i. unfold inflate_spec_za. simpl. reflexivity. Qed.
Lemma inflate_cc : forall i : zai, callingconvention_of_funspec (snd (@inflate_spec_za (zai_a i) (zai_v i))) = cc_default.
Proof. intros i. unfold inflate_spec_za. simpl. reflexivity. Qed.
Definition inflate_uspec : ident * funspec :=
  (_inflate, uspec (fun i : zai => snd (@inflate_spec_za (zai_a i) (zai_v i))) (typesig_of_funspec (snd (@inflate_spec_za za0 av_defined))) cc_default inflate_sig inflate_cc).
Lemma inflate_fast_sig : forall i : zai, typesig_of_funspec (snd (@inflate_fast_spec3_za (zai_a i) (zai_v i))) = typesig_of_funspec (snd (@inflate_fast_spec3_za za0 av_defined)).
Proof. intros i. unfold inflate_fast_spec3_za. simpl. reflexivity. Qed.
Lemma inflate_fast_cc : forall i : zai, callingconvention_of_funspec (snd (@inflate_fast_spec3_za (zai_a i) (zai_v i))) = cc_default.
Proof. intros i. unfold inflate_fast_spec3_za. simpl. reflexivity. Qed.
Definition inflate_fast_uspec : ident * funspec :=
  (_inflate_fast, uspec (fun i : zai => snd (@inflate_fast_spec3_za (zai_a i) (zai_v i))) (typesig_of_funspec (snd (@inflate_fast_spec3_za za0 av_defined))) cc_default inflate_fast_sig inflate_fast_cc).
Lemma updatewindow_sig : forall i : zai, typesig_of_funspec (snd (@updatewindow_spec3_za (zai_a i))) = typesig_of_funspec (snd (@updatewindow_spec3_za za0)).
Proof. intros i. unfold updatewindow_spec3_za. simpl. reflexivity. Qed.
Lemma updatewindow_cc : forall i : zai, callingconvention_of_funspec (snd (@updatewindow_spec3_za (zai_a i))) = cc_default.
Proof. intros i. unfold updatewindow_spec3_za. simpl. reflexivity. Qed.
Definition updatewindow_uspec : ident * funspec :=
  (_updatewindow, uspec (fun i : zai => snd (@updatewindow_spec3_za (zai_a i))) (typesig_of_funspec (snd (@updatewindow_spec3_za za0))) cc_default updatewindow_sig updatewindow_cc).
Lemma inflateStateCheck_sig : forall i : zai, typesig_of_funspec (snd (@inflateStateCheck_spec_za (zai_a i))) = typesig_of_funspec (snd (@inflateStateCheck_spec_za za0)).
Proof. intros i. unfold inflateStateCheck_spec_za. simpl. reflexivity. Qed.
Lemma inflateStateCheck_cc : forall i : zai, callingconvention_of_funspec (snd (@inflateStateCheck_spec_za (zai_a i))) = cc_default.
Proof. intros i. unfold inflateStateCheck_spec_za. simpl. reflexivity. Qed.
Definition inflateStateCheck_uspec : ident * funspec :=
  (_inflateStateCheck, uspec (fun i : zai => snd (@inflateStateCheck_spec_za (zai_a i))) (typesig_of_funspec (snd (@inflateStateCheck_spec_za za0))) cc_default inflateStateCheck_sig inflateStateCheck_cc).
Lemma inflateSetDictionary_sig : forall i : zai, typesig_of_funspec (snd (@inflateSetDictionary_spec_za (zai_a i) (zai_v i))) = typesig_of_funspec (snd (@inflateSetDictionary_spec_za za0 av_defined)).
Proof. intros i. unfold inflateSetDictionary_spec_za. simpl. reflexivity. Qed.
Lemma inflateSetDictionary_cc : forall i : zai, callingconvention_of_funspec (snd (@inflateSetDictionary_spec_za (zai_a i) (zai_v i))) = cc_default.
Proof. intros i. unfold inflateSetDictionary_spec_za. simpl. reflexivity. Qed.
Definition inflateSetDictionary_uspec : ident * funspec :=
  (_inflateSetDictionary, uspec (fun i : zai => snd (@inflateSetDictionary_spec_za (zai_a i) (zai_v i))) (typesig_of_funspec (snd (@inflateSetDictionary_spec_za za0 av_defined))) cc_default inflateSetDictionary_sig inflateSetDictionary_cc).
Lemma inflateInit2__sig : forall i : zai, typesig_of_funspec (snd (@inflateInit2__spec_za (zai_a i))) = typesig_of_funspec (snd (@inflateInit2__spec_za za0)).
Proof. intros i. unfold inflateInit2__spec_za. simpl. reflexivity. Qed.
Lemma inflateInit2__cc : forall i : zai, callingconvention_of_funspec (snd (@inflateInit2__spec_za (zai_a i))) = cc_default.
Proof. intros i. unfold inflateInit2__spec_za. simpl. reflexivity. Qed.
Definition inflateInit2__uspec : ident * funspec :=
  (_inflateInit2_, uspec (fun i : zai => snd (@inflateInit2__spec_za (zai_a i))) (typesig_of_funspec (snd (@inflateInit2__spec_za za0))) cc_default inflateInit2__sig inflateInit2__cc).
Lemma inflateResetKeep_sig : forall i : zai, typesig_of_funspec (snd (@inflateResetKeep_spec_za (zai_a i) (zai_v i))) = typesig_of_funspec (snd (@inflateResetKeep_spec_za za0 av_defined)).
Proof. intros i. unfold inflateResetKeep_spec_za. simpl. reflexivity. Qed.
Lemma inflateResetKeep_cc : forall i : zai, callingconvention_of_funspec (snd (@inflateResetKeep_spec_za (zai_a i) (zai_v i))) = cc_default.
Proof. intros i. unfold inflateResetKeep_spec_za. simpl. reflexivity. Qed.
Definition inflateResetKeep_uspec : ident * funspec :=
  (_inflateResetKeep, uspec (fun i : zai => snd (@inflateResetKeep_spec_za (zai_a i) (zai_v i))) (typesig_of_funspec (snd (@inflateResetKeep_spec_za za0 av_defined))) cc_default inflateResetKeep_sig inflateResetKeep_cc).
Lemma inflateReset_sig : forall i : zai, typesig_of_funspec (snd (@inflateReset_spec_za (zai_a i) (zai_v i))) = typesig_of_funspec (snd (@inflateReset_spec_za za0 av_defined)).
Proof. intros i. unfold inflateReset_spec_za. simpl. reflexivity. Qed.
Lemma inflateReset_cc : forall i : zai, callingconvention_of_funspec (snd (@inflateReset_spec_za (zai_a i) (zai_v i))) = cc_default.
Proof. intros i. unfold inflateReset_spec_za. simpl. reflexivity. Qed.
Definition inflateReset_uspec : ident * funspec :=
  (_inflateReset, uspec (fun i : zai => snd (@inflateReset_spec_za (zai_a i) (zai_v i))) (typesig_of_funspec (snd (@inflateReset_spec_za za0 av_defined))) cc_default inflateReset_sig inflateReset_cc).
Lemma inflateReset2_sig : forall i : zai, typesig_of_funspec (snd (@inflateReset2_spec_za (zai_a i) (zai_v i))) = typesig_of_funspec (snd (@inflateReset2_spec_za za0 av_defined)).
Proof. intros i. unfold inflateReset2_spec_za. simpl. reflexivity. Qed.
Lemma inflateReset2_cc : forall i : zai, callingconvention_of_funspec (snd (@inflateReset2_spec_za (zai_a i) (zai_v i))) = cc_default.
Proof. intros i. unfold inflateReset2_spec_za. simpl. reflexivity. Qed.
Definition inflateReset2_uspec : ident * funspec :=
  (_inflateReset2, uspec (fun i : zai => snd (@inflateReset2_spec_za (zai_a i) (zai_v i))) (typesig_of_funspec (snd (@inflateReset2_spec_za za0 av_defined))) cc_default inflateReset2_sig inflateReset2_cc).
Lemma inflateEnd_sig : forall i : zai, typesig_of_funspec (snd (@inflateEnd_spec_za (zai_a i) (zai_v i))) = typesig_of_funspec (snd (@inflateEnd_spec_za za0 av_defined)).
Proof. intros i. unfold inflateEnd_spec_za. simpl. reflexivity. Qed.
Lemma inflateEnd_cc : forall i : zai, callingconvention_of_funspec (snd (@inflateEnd_spec_za (zai_a i) (zai_v i))) = cc_default.
Proof. intros i. unfold inflateEnd_spec_za. simpl. reflexivity. Qed.
Definition inflateEnd_uspec : ident * funspec :=
  (_inflateEnd, uspec (fun i : zai => snd (@inflateEnd_spec_za (zai_a i) (zai_v i))) (typesig_of_funspec (snd (@inflateEnd_spec_za za0 av_defined))) cc_default inflateEnd_sig inflateEnd_cc).

(* the contexts (those of Callees3 / Bodies5 / Stmt with the uspecs) *)
Definition GU_inflate : funspecs :=
  [Zlib.proof.adler32.Spec.adler32_spec; Zlib.proof.crc32.Spec.crc32_spec;
   inflate_fast_uspec; inflate_fixed_spec; Zlib.proof.inftrees.spec.inflate_table_spec;
   (_memcpy, snd (@Zlib.proof.zutil.Libc.memcpy_spec Zlib.units.Inflate.CS));
   inflateStateCheck_uspec; updatewindow_uspec].
Definition GU_setdict : funspecs :=
  [inflateStateCheck_uspec; Zlib.proof.adler32.Spec.adler32_spec; updatewindow_uspec].
Definition GU_init2 : funspecs := [inflateReset2_uspec; memset_i].
Definition GU_resetkeep : funspecs := [inflateStateCheck_uspec].
Definition GU_reset : funspecs := [inflateStateCheck_uspec; inflateResetKeep_uspec].
Definition GU_reset2 : funspecs := [inflateStateCheck_uspec; inflateReset_uspec].
Definition GU_end : funspecs := [inflateStateCheck_uspec].

(* the bodies, each with one specification for every allocator and adler cell *)
Definition za_inflate_ulib_stmt : Prop :=
  forall {Espec : OracleKind},
    semax_body Vprog_inflate GU_inflate f_inflate inflate_uspec /\
    semax_body Vprog_fast Gprog_fast Zlib.inffast.code.f_inflate_fast inflate_fast_uspec /\
    semax_body Vprog_inflate Gp_updatewindow_za f_updatewindow updatewindow_uspec /\
    semax_body Vprog_inflate [] f_inflateStateCheck inflateStateCheck_uspec /\
    semax_body Vprog_inflate GU_setdict f_inflateSetDictionary inflateSetDictionary_uspec /\
    semax_body Vprog_inflate GU_init2 f_inflateInit2_ inflateInit2__uspec /\
    semax_body Vprog_inflate GU_resetkeep f_inflateResetKeep inflateResetKeep_uspec /\
    semax_body Vprog_inflate GU_reset f_inflateReset inflateReset_uspec /\
    semax_body Vprog_inflate GU_reset2 f_inflateReset2 inflateReset2_uspec /\
    semax_body Vprog_inflate GU_end f_inflateEnd inflateEnd_uspec.

(* each uspec gives its members *)
Definition za_uspec_sub_stmt : Prop :=
  forall (i : zai), let ZA := zai_a i in let ZAV := zai_v i in
    funspec_sub (snd inflate_uspec) (snd (@inflate_spec_za ZA ZAV)) /\
    funspec_sub (snd inflate_fast_uspec) (snd (@inflate_fast_spec3_za ZA ZAV)) /\
    funspec_sub (snd updatewindow_uspec) (snd (@updatewindow_spec3_za ZA)) /\
    funspec_sub (snd inflateStateCheck_uspec) (snd (@inflateStateCheck_spec_za ZA)) /\
    funspec_sub (snd inflateSetDictionary_uspec) (snd (@inflateSetDictionary_spec_za ZA ZAV)) /\
    funspec_sub (snd inflateInit2__uspec) (snd (@inflateInit2__spec_za ZA)) /\
    funspec_sub (snd inflateResetKeep_uspec) (snd (@inflateResetKeep_spec_za ZA ZAV)) /\
    funspec_sub (snd inflateReset_uspec) (snd (@inflateReset_spec_za ZA ZAV)) /\
    funspec_sub (snd inflateReset2_uspec) (snd (@inflateReset2_spec_za ZA ZAV)) /\
    funspec_sub (snd inflateEnd_uspec) (snd (@inflateEnd_spec_za ZA ZAV)).

End USpecs.

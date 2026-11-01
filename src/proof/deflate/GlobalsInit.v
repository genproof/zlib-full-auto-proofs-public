(** * The global variables of the three deflate law programs, as the shared specifications want them

    For each program (deflate_api, deflate_bound, deflate_bound_split: the harness linked with adler32.c,
    crc32.c, deflate.c, trees.c, zutil.c, libc.c, and compress.c for the two bound laws): the initial
    contents of its global variables ([globvars2pred], what main gets) give [DSpec.deflate_globals gv]
    (trees.c's static trees and tables, zutil.c's z_errmsg, deflate.c's configuration_table (with the
    function pointers deflate_stored / deflate_fast / deflate_slow) and my_version, crc32.c's crc_table) and
    the harness's string literal ZLIB_VERSION ("1.3.2", the version argument of the deflateInit2 macro);
    the rest (x2n_table, deflate_copyright, zutil's message strings, ...) is dropped into TT.
    [gv] is at offset 0 for every global (genviron2globals; MainLib.semax_body_main_core). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Assembly.
Require Import Zlib.proof.deflate.DCS Zlib.proof.deflate.Rep.
Require Import Zlib.proof.deflate.DSpec.
Require Zlib.contracts.x_deflate_api Zlib.contracts.x_deflate_bound Zlib.contracts.x_deflate_bound_split.
Require Zlib.harness.x_deflate_api.code Zlib.harness.x_deflate_bound.code Zlib.harness.x_deflate_bound_split.code.
Require Zlib.proof.deflate.GlobalsFixed.

(** ZLIB_VERSION as the harness's string literal [lit]. *)
Definition version_at (gv : globals) (lit : ident) : mpred :=
  @data_at DCS.CS Ers (tarray tschar 6) (map vi [49; 46; 51; 46; 50; 0]) (gv lit).

(** [gv] as main gets it (genviron2globals): offset 0 at every pointer, and the functions whose addresses
    configuration_table holds (deflate_stored / deflate_fast / deflate_slow, not program variables) at a pointer or
    undefined (without it [gv _deflate_stored = Vint 0] makes the right side FF).  Main's
    subsumption: MainCoreCfg.semax_body_main_core_cfg with [fs = GlobalsFixed.cfg_funs]. *)
Definition globals_of (p : QP.program Clight.function) (lit : ident) : Prop :=
  forall gv, (forall i b o, gv i = Vptr b o -> o = Ptrofs.zero) ->
  (forall f, In f Zlib.proof.deflate.GlobalsFixed.cfg_funs -> gv f = Vundef \/ isptr (gv f)) ->
  globvars2pred gv (QPprog_vars p) |-- deflate_globals gv * version_at gv lit * TT.

Definition globals_ok : Prop :=
  globals_of Zlib.contracts.x_deflate_api.whole_prog Zlib.harness.x_deflate_api.code.___stringlit_x_deflate_api_1 /\
  globals_of Zlib.contracts.x_deflate_bound.whole_prog Zlib.harness.x_deflate_bound.code.___stringlit_x_deflate_bound_1 /\
  globals_of Zlib.contracts.x_deflate_bound_split.whole_prog
    Zlib.harness.x_deflate_bound_split.code.___stringlit_x_deflate_bound_split_1.

Theorem deflate_globals_init : globals_ok.
Proof.
  split; [|split].
  - exact Zlib.proof.deflate.GlobalsFixed.globals_api_fixed.
  - exact Zlib.proof.deflate.GlobalsFixed.globals_bound_fixed.
  - exact Zlib.proof.deflate.GlobalsFixed.globals_split_fixed.
Qed.

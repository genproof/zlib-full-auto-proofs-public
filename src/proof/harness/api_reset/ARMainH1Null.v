(* Law api_reset, main: the test of the four objects of a do-while iteration (in_used, in_fresh: copy_of();
   out_used, out_fresh: malloc()) when one of them is NULL: `return 0`, with both streams given back to the
   stack frame.  Stated on a small assertion (only the four pointers, the two locals and the objects), so that
   each of the four cases is cheap; the body (ARMainHead1.v) weakens its assertion to it. *)
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
Require Import Zlib.proof.harness.api_reset.ARMainH1Call.
Local Open Scope logic.

(* the test `if (in_used == NULL || ... || out_fresh == NULL) return 0;`, the 8th statement of the body *)
Definition path_null : list nat := path_dbody ++ repeat 1%nat 7 ++ [0%nat].
Definition seg_null : statement := ltac:(get_seg path_null).

(* the object of a copy_of(.., n) (at the compspecs of copy_of's specification) and of a malloc(n) *)
Definition copy_obj (q: val) (n: Z) (d: list Z) : mpred :=
  if eq_dec q nullval then emp
  else (@malloc_token Zlib.units.Adler32.CS Ews (tarray tuchar n) q *
        @data_at Zlib.units.Adler32.CS Ews (tarray tuchar n) (bytes_rep d) q).
Definition malloc_obj (q: val) (n: Z) : mpred :=
  if eq_dec q nullval then emp
  else (@malloc_token CS Ews (tarray tuchar n) q * @data_at_ CS Ews (tarray tuchar n) q).

(* a non-NULL object can be compared with NULL (also when it has 0 bytes: then by its malloc token); as hints,
   so that the pointer comparisons of the test find the validity at once *)
Lemma copy_obj_valid q n d: q <> nullval -> copy_obj q n d |-- valid_pointer q.
Proof.
  intros N. unfold copy_obj. rewrite if_false by auto.
  destruct (zlt 0 n).
  - apply sepcon_valid_pointer2. apply data_at_valid_ptr; [auto with share | simpl; rep_lia].
  - apply sepcon_valid_pointer1. apply malloc_token_valid_pointer. simpl. rep_lia.
Qed.
Lemma malloc_obj_valid q n: q <> nullval -> malloc_obj q n |-- valid_pointer q.
Proof.
  intros N. unfold malloc_obj. rewrite if_false by auto.
  destruct (zlt 0 n).
  - apply sepcon_valid_pointer2. apply data_at_valid_ptr; [auto with share | simpl; rep_lia].
  - apply sepcon_valid_pointer1. apply malloc_token_valid_pointer. simpl. rep_lia.
Qed.
#[export] Hint Resolve copy_obj_valid malloc_obj_valid : valid_pointer.

(* `p == NULL` for a pointer that is not NULL *)
Lemma cmp_nn p: is_pointer_or_null p -> p <> nullval ->
  force_val (sem_cast_i2bool (force_val (sem_cmp_pp Ceq p (Vlong (Int64.repr 0))))) = Vint (Int.repr 0).
Proof. intros P N. destruct p; try contradiction; [simpl in P; subst; contradiction | reflexivity]. Qed.
Ltac cmpnn := entailer!; rewrite cmp_nn by auto; reflexivity.

Lemma h1_null {Espec: OracleKind} J0 J1 gv va vb w ph inp src take room d iu ifr ou ofr S:
  (iu = nullval \/ ifr = nullval \/ ou = nullval \/ ofr = nullval) ->
  semax Delta_m
    (PROP ()
     LOCAL (temp _in_used iu; temp _in_fresh ifr; temp _out_used ou; temp _out_fresh ofr;
            lvar _used t_z va; lvar _fresh t_z vb)
     SEP (@data_at_ CS Tsh t_z va; @data_at_ CS Tsh t_z vb; copy_obj iu take d; copy_obj ifr take d;
          malloc_obj ou room; malloc_obj ofr room; TT))
    (Ssequence seg_null S) (dpost J0 J1 gv va vb w ph inp src).
Proof.
  intros Hn.
  unfold seg_null, dpost, Delta_m, Gmain, POST_m. simplify_func_tycontext. abbreviate_semax.
  destruct (eq_dec iu nullval) as [N1 | N1].
  { subst iu.
    ifpost1 _t'14 (Vint (Int.repr 1)); [forward; entailer! | infeas1 | ].
    ifpost1 _t'15 (Vint (Int.repr 1)); [forward; entailer! | infeas1 | ].
    ifpost1 _t'16 (Vint (Int.repr 1)); [forward; entailer! | infeas1 | ].
    forward_if; [forward; Exists (Int.repr 0); entailer! | infeas1]. }
  destruct (eq_dec ifr nullval) as [N2 | N2].
  { subst ifr.
    ifpost1 _t'14 (Vint (Int.repr 1)); [infeas1 | forward; entailer! | ].
    ifpost1 _t'15 (Vint (Int.repr 1)); [forward; entailer! | infeas1 | ].
    ifpost1 _t'16 (Vint (Int.repr 1)); [forward; entailer! | infeas1 | ].
    forward_if; [forward; Exists (Int.repr 0); entailer! | infeas1]. }
  destruct (eq_dec ou nullval) as [N3 | N3].
  { subst ou.
    ifpost1 _t'14 (Vint (Int.repr 0)); [infeas1 | forward; cmpnn | ].
    ifpost1 _t'15 (Vint (Int.repr 1)); [infeas1 | forward; entailer! | ].
    ifpost1 _t'16 (Vint (Int.repr 1)); [forward; entailer! | infeas1 | ].
    forward_if; [forward; Exists (Int.repr 0); entailer! | infeas1]. }
  destruct (eq_dec ofr nullval) as [N4 | N4]; [ | exfalso; tauto].
  subst ofr.
  ifpost1 _t'14 (Vint (Int.repr 0)); [infeas1 | forward; cmpnn | ].
  ifpost1 _t'15 (Vint (Int.repr 0)); [infeas1 | forward; cmpnn | ].
  ifpost1 _t'16 (Vint (Int.repr 1)); [infeas1 | forward; entailer! | ].
  forward_if; [forward; Exists (Int.repr 0); entailer! | infeas1].
Qed.

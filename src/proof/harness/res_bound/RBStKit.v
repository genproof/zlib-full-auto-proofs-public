(* Law res_bound, main: the kit of the eight stores into the local gz_header head (statements 17-24, RBStores.v),
   cut in five segments so that each file stays small: RBSt1 (text, time: msuf 17 -> msuf 19), RBSt2 (os, hcrc:
   msuf 19 -> msuf 21), RBSt3 (extra, extra_len: msuf 21 -> msuf 23), RBSt4 (name: msuf 23 -> msuf 24), RBSt5
   (comment: msuf 24 -> msuf 25). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DCS Zlib.proof.deflate.Rep Zlib.proof.deflate.DSpec Zlib.proof.deflate.DSpec9.
Require Import Zlib.proof.deflate.LawFacts Zlib.proof.deflate.LawFactsW Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.deflate.Obligations.
Require Zlib.proof.harness.bound_common.BoundKit Zlib.proof.harness.deflate_bound.MainKit.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.res_bound.RBCS Zlib.proof.harness.res_bound.RBString Zlib.proof.harness.res_bound.RBKit.
Require Import Zlib.harness.res_bound.code.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.

(* the C test [choice & m] (both bytes): it is non-zero exactly when bit [m] of choice is set *)
Lemma has_and (rs : rsetup) (m : Z) :
  0 <= r_choice rs < 256 -> 0 <= m < 256 ->
  (Int.and (Int.repr (r_choice rs)) (Int.repr m) = Int.zero <-> has rs m = false).
Proof.
  intros Hc Hm. unfold has, Int.and. rewrite !Int.unsigned_repr by rep_lia.
  assert (B : 0 <= Z.land (r_choice rs) m <= Int.max_unsigned).
  { split; [ apply Z.land_nonneg; lia | ].
    assert (E : Z.land (r_choice rs) m = Z.land (r_choice rs) m mod 2 ^ 8).
    { rewrite <- Z.land_ones by lia. rewrite <- Z.land_assoc, (Z.land_comm m), Z.land_assoc.
      rewrite (Z.land_ones (r_choice rs) 8) by lia. rewrite Z.mod_small by (simpl; lia). reflexivity. }
    rewrite E. pose proof (Z.mod_pos_bound (Z.land (r_choice rs) m) (2 ^ 8) ltac:(lia)). rep_lia. }
  destruct (Z.eqb_spec (Z.land (r_choice rs) m) 0) as [E | E]; simpl; split; intros X; try reflexivity.
  - rewrite E. reflexivity.
  - apply (f_equal Int.unsigned) in X. rewrite Int.unsigned_repr in X by exact B. contradiction.
  - discriminate.
Qed.

(* the value of [cond ? q : Z_NULL] *)
Ltac selp_tac :=
  unfold selp; match goal with
  | H : Int.and _ _ = Int.zero |- _ => apply has_and in H; [ rewrite H; reflexivity | lia | lia ]
  | H : Int.and _ _ <> Int.zero |- _ =>
      let E := fresh in destruct (has _ _) eqn:E; [ reflexivity | apply has_and in E; [ contradiction | lia | lia ] ]
  end.

Ltac ifptr t v := match goal with |- semax _ (PROPx _ (LOCALx ?Q (SEPx ?R))) _ _ =>
  forward_if (PROPx [] (LOCALx (temp t v :: Q) (SEPx R))) end.

Definition msuf19 : statement := ltac:(get_msuf 19%nat).
Definition msuf21 : statement := ltac:(get_msuf 21%nat).
Definition msuf23 : statement := ltac:(get_msuf 23%nat).
Definition msuf24 : statement := ltac:(get_msuf 24%nat).

(* head after the stores of text and time *)
Definition hval2 (text time : Z) : reptype t_gzh :=
  (vi text, (vl time, (Vundef, (Vundef, (Vundef, (Vundef,
   (Vundef, (Vundef, (Vundef, (Vundef, (Vundef, (Vundef, Vundef)))))))))))).

(* head after the stores of the four drawn values (text, time, os, hcrc) *)
Definition hval4 (hv : hvals) : reptype t_gzh :=
  (vi (h_text hv), (vl (h_time hv), (Vundef, (vi (h_os hv), (Vundef, (Vundef,
   (Vundef, (Vundef, (Vundef, (Vundef, (Vundef, (vi (h_hcrc hv), Vundef)))))))))))).

(* and of the extra field and its length *)
Definition hval6 (rs : rsetup) (hv : hvals) : reptype t_gzh :=
  (vi (h_text hv), (vl (h_time hv), (Vundef, (vi (h_os hv), (selp rs 2 (r_xp rs), (vi (r_xlen rs),
   (Vundef, (Vundef, (Vundef, (Vundef, (Vundef, (vi (h_hcrc hv), Vundef)))))))))))).

(* and of the name *)
Definition hval7 (rs : rsetup) (hv : hvals) : reptype t_gzh :=
  (vi (h_text hv), (vl (h_time hv), (Vundef, (vi (h_os hv), (selp rs 2 (r_xp rs), (vi (r_xlen rs),
   (Vundef, (selp rs 4 (r_np rs), (Vundef, (Vundef, (Vundef, (vi (h_hcrc hv), Vundef)))))))))))).

Section Kit.
Context (gv : globals) (vh vs : val).

(* the assertion with head [hd] (A1 after some stores) *)
Definition Ahd (rs : rsetup) (hv : hvals) (hd : reptype t_gzh) : environ -> mpred :=
  PROPx [rs_ok rs; hv_ok hv]
  (LOCALx (rs_locals rs ++ [lvar _head t_gzh vh; lvar _strm t_strm vs; gvars gv])
  (SEPx [data_at Tsh t_gzh hd vh; data_at_ Tsh t_strm vs; mem_mgr gv; deflate_globals gv; version_at gv vlit;
         objs rs])).

(* after the stores of text and time *)
Definition Ahd2 (rs : rsetup) (text time : Z) : environ -> mpred :=
  PROPx [rs_ok rs; s32 text; u32r time]
  (LOCALx (rs_locals rs ++ [lvar _head t_gzh vh; lvar _strm t_strm vs; gvars gv])
  (SEPx [data_at Tsh t_gzh (hval2 text time) vh; data_at_ Tsh t_strm vs; mem_mgr gv; deflate_globals gv;
         version_at gv vlit; objs rs])).

End Kit.

Definition st1_stmt : Prop :=
  forall {Espec : OracleKind} (gv : globals) (vh vs : val) (rs : rsetup),
  (forall text time, semax Delta_m (Ahd2 gv vh vs rs text time) msuf19 POST_m) ->
  semax Delta_m (A1 gv vh vs rs) msuf17 POST_m.

Definition st2_stmt : Prop :=
  forall {Espec : OracleKind} (gv : globals) (vh vs : val) (rs : rsetup) (text time : Z),
  (forall hv, semax Delta_m (Ahd gv vh vs rs hv (hval4 hv)) msuf21 POST_m) ->
  semax Delta_m (Ahd2 gv vh vs rs text time) msuf19 POST_m.

Definition st3_stmt : Prop :=
  forall {Espec : OracleKind} (gv : globals) (vh vs : val) (rs : rsetup) (hv : hvals),
  semax Delta_m (Ahd gv vh vs rs hv (hval6 rs hv)) msuf23 POST_m ->
  semax Delta_m (Ahd gv vh vs rs hv (hval4 hv)) msuf21 POST_m.

Definition st4_stmt : Prop :=
  forall {Espec : OracleKind} (gv : globals) (vh vs : val) (rs : rsetup) (hv : hvals),
  semax Delta_m (Ahd gv vh vs rs hv (hval7 rs hv)) msuf24 POST_m ->
  semax Delta_m (Ahd gv vh vs rs hv (hval6 rs hv)) msuf23 POST_m.

Definition st5_stmt : Prop :=
  forall {Espec : OracleKind} (gv : globals) (vh vs : val) (rs : rsetup) (hv : hvals),
  semax Delta_m (A2 gv vh vs rs hv) msuf25 POST_m ->
  semax Delta_m (Ahd gv vh vs rs hv (hval7 rs hv)) msuf24 POST_m.

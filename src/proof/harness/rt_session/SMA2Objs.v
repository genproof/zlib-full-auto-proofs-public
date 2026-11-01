(* Law rt_session, main's statements 24-30: the copies dict_copy, extra_copy, name_copy, comment_copy, expected
   (copy_of) and the objects compressed, out (malloc), each possibly NULL. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.Rep.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.rt_session.SCS.
Require Import Zlib.proof.harness.rt_session.SMainStmt.
Require Import Zlib.proof.harness.rt_session.SMKit.
Require Import Zlib.proof.harness.rt_session.SMA2Kit.
Require Import Zlib.harness.rt_session.code.
#[local] Existing Instance SCS.CS.
Local Open Scope logic.

Lemma a2_objs {Espec : OracleKind} gv vh vg vc va vd u :
  semax Delta_s (A24 gv vh vg vc va vd u)
    (Ssequence S24 (Ssequence S25 (Ssequence S26 (Ssequence S27 (Ssequence S28 (Ssequence S29 S30))))))
    (overridePost (EX dcp : val, EX xcp : val, EX ncp : val, EX ccp : val, EX ep : val, EX cp : val, EX op : val,
                     QH gv vh vg vc va vd u dcp xcp ncp ccp ep cp op h00) POST_s).
Proof.
  unfold A24, lvs, lv_locals, o_locals, d_locals, dictobj, datobj, S24, S25, S26, S27, S28, S29, S30.
  cbn [app].
  unfold Delta_s; simplify_func_tycontext. abbreviate_semax.
  Intros. a2_facts.
  assert_PROP (isptr (su_dictp u)) as I1 by (sep_apply (bobj_isptr (su_dictp u) (su_dict u)); entailer!).
  assert_PROP (isptr (su_xp u)) as I2 by (sep_apply (bobj_isptr (su_xp u) (su_xf u)); entailer!).
  assert_PROP (isptr (su_np u)) as I3 by (sep_apply (bobj_isptr (su_np u) (su_nm u ++ [0])); entailer!).
  assert_PROP (isptr (su_cmp u)) as I4 by (sep_apply (bobj_isptr (su_cmp u) (su_cm u ++ [0])); entailer!).
  assert_PROP (isptr (su_dp u)) as I5 by (sep_apply (bobj_isptr (su_dp u) (su_data u)); entailer!).
  assert (Ln : Zlength (su_nm u ++ [0]) = Zlength (su_nm u) + 1) by apply Zlength_z0.
  assert (Lc : Zlength (su_cm u ++ [0]) = Zlength (su_cm u) + 1) by apply Zlength_z0.
  rewrite (bobj_cs (su_dictp u) (su_dict u) _ eq_refl), (bobj_cs (su_xp u) (su_xf u) _ eq_refl),
    (bobj_cs (su_np u) (su_nm u ++ [0]) _ Ln), (bobj_cs (su_cmp u) (su_cm u ++ [0]) _ Lc),
    (bobj_cs (su_dp u) (su_data u) _ eq_refl).
  flatten_sepcon_in_SEP.
  forward_call (su_dictp u, Ews, su_dictp u, 0, Zlength (su_dict u), map vi (su_dict u), Zlength (su_dict u),
                su_dict u, gv).
  { apply bobj_cbuf; auto using rbytes_is_bytes. }
  Intros dcp. rewrite (obj0_of_copy dcp (su_dict u) _ eq_refl).
  forward_call (su_xp u, Ews, su_xp u, 0, Zlength (su_xf u), map vi (su_xf u), Zlength (su_xf u), su_xf u, gv).
  { apply bobj_cbuf; auto using rbytes_is_bytes. }
  Intros xcp. rewrite (obj0_of_copy xcp (su_xf u) _ eq_refl).
  forward_call (su_np u, Ews, su_np u, 0, Zlength (su_nm u) + 1, map vi (su_nm u ++ [0]), Zlength (su_nm u) + 1,
                su_nm u ++ [0], gv).
  { apply bobj_cbuf; auto using nz_is_bytes. }
  Intros ncp. rewrite (obj0_of_copy ncp (su_nm u ++ [0]) _ Ln).
  forward_call (su_cmp u, Ews, su_cmp u, 0, Zlength (su_cm u) + 1, map vi (su_cm u ++ [0]), Zlength (su_cm u) + 1,
                su_cm u ++ [0], gv).
  { apply bobj_cbuf; auto using nz_is_bytes. }
  Intros ccp. rewrite (obj0_of_copy ccp (su_cm u ++ [0]) _ Lc).
  forward_call (su_dp u, Ews, su_dp u, 0, Zlength (su_data u), map vi (su_data u), Zlength (su_data u),
                su_data u, gv).
  { split; [unfold UDFacts.max_size in *; rep_lia | apply bobj_cbuf; auto using rbytes_is_bytes]. }
  Intros ep. rewrite (obj0_of_copy ep (su_data u) _ eq_refl).
  forward_call (tarray tuchar (su_cap u), gv).
  { simpl. rewrite Z.max_r by lia. unfold UDFacts.max_size in *; rep_lia. } Intros cp.
  forward_call (tarray tuchar (Zlength (su_data u)), gv).
  { simpl. rewrite Z.max_r by (apply Zlength_nonneg). unfold UDFacts.max_size in *; rep_lia. } Intros op.
  forward.
  Exists dcp xcp ncp ccp ep cp op.
  destruct POST_s as [r1 r2 r3 r4]; cbn [tycontext.RA_normal].
  unfold QH, Qs, base, ctemps, cobjs, h00, gw, U, lvs, lv_locals, o_locals, d_locals, dictobj, datobj, new0, cnew.
  cbn [app].
  rewrite <- !data_at_g.
  rewrite (bobj_cs (su_dictp u) (su_dict u) _ eq_refl), (bobj_cs (su_xp u) (su_xf u) _ eq_refl),
    (bobj_cs (su_np u) (su_nm u ++ [0]) _ Ln), (bobj_cs (su_cmp u) (su_cm u ++ [0]) _ Lc),
    (bobj_cs (su_dp u) (su_data u) _ eq_refl).
  entailer!.
Qed.

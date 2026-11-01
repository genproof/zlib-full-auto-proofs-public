(* Law rfc_stored, main: statements 25-31, new_stream, window_bits, inflateInit2_(&strm, window_bits[wrapper],
   "1.3.2", sizeof(z_stream)) (`return 0` unless Z_OK), next_in = stream, next_out = out: the invariant of the
   inflate loop holds at pos 0 with no output (RSFacts.rf_init) (rs_D -> rs_inv). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.EnvBodies.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.SpecW.
Require Zlib.proof.adler32.Spec.
Require Zlib.proof.crc32.Spec.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.rfc_stored.RSLawCS.
Require Import Zlib.proof.harness.rfc_stored.RSGlobals.
Require Import Zlib.proof.harness.rfc_stored.RSFacts.
Require Import Zlib.proof.harness.rfc_stored.RSMainKit.
Require Import Zlib.harness.rfc_stored.code.
Local Open Scope logic.

(* VST's after_forward_call simplifies remove_localdef_temp with `simpl rlt_ident_eq`, which runs away on main's
   identifiers (e.g. _stream against _stream_len); each identifier comparison is decided by vm_compute instead. *)
Ltac rs_rlt_fix u :=
  lazymatch u with
  | context C [rlt_ident_eq ?a ?b] =>
      let v := eval vm_compute in (rlt_ident_eq a b) in
      let u2 := context C [v] in rs_rlt_fix u2
  | _ => u
  end.

Ltac simplify_remove_localdef_temp ::=
  match goal with |- context [remove_localdef_temp ?i ?L] =>
    let u := constr:(remove_localdef_temp i L) in
    let u' := eval lazy delta [remove_localdef_temp] beta iota in u in
    let u' := rs_rlt_fix u' in
    let u' := eval lazy beta iota in u' in
    let u' := eval lazy zeta in u' in
    change u with u'
  end.

(* window_bits[wrapper] after `int window_bits[3] = {-window, window, 16 + window}` is inflateInit2's windowBits *)
Lemma rs_wb_znth wr window: 0 <= wr <= 2 -> 8 <= window <= 15 ->
  Znth wr (upd_Znth 2 (upd_Znth 1 (upd_Znth 0 (default_val (tarray tint 3)) (Vint (Int.repr (- window))))
                        (Vint (Int.repr window))) (Vint (Int.repr (16 + window))))
  = Vint (Int.repr (rs_iw wr window)).
Proof.
  intros Hwr Hw. unfold rs_iw.
  assert (E: wr = 0 \/ wr = 1 \/ wr = 2) by lia.
  destruct E as [-> | [-> | ->]]; reflexivity.
Qed.

(* the local stream after inflateInit2_ returned something else than Z_OK: the variable's memory *)
Lemma rs_init_fail_mem gv vs r m st o ret sp w: isptr vs -> ret <> Z_OK ->
  init_mem gv Tsh vs r m st o ret sp w |-- @data_at_ CS Tsh t_zsl vs.
Proof.
  intros Pv Hr. unfold init_mem.
  destruct (eq_dec vs nullval); [subst; contradiction | ].
  destruct (ret =? Z_VERSION_ERROR); [apply rs_raw_frame | ].
  destruct (ret =? Z_MEM_ERROR); [apply rs_raw_frame | ].
  destruct (Z.eqb_spec ret Z_OK); [contradiction | apply rs_raw_frame].
Qed.

(* ... and when it returned Z_OK: the live stream *)
Lemma rs_init_ok_mem gv vs r m st o sp w: isptr vs ->
  init_mem gv Tsh vs r m st o Z_OK sp w =
  istream_raw gv Tsh vs (raw_after_init r (l_s (init_live sp w))) (init_live sp w).
Proof.
  intros Pv. unfold init_mem. destruct (eq_dec vs nullval); [subst; contradiction | ]. reflexivity.
Qed.

(* after strm.next_in = stream; strm.next_out = out on the stream inflateInit2_ made: the loop's stream at pos 0
   with no output, avail_in = avail_out = 0 *)
Lemma rs_init_set gv vs stp op L: isptr stp -> isptr op -> live_ok L ->
  data_at Tsh t_zsl (stp, (fst (snd (rs_tup gv (rs_z_init L) (adler_v (raw_live (Some L)) (rs_z_init L) Vundef) (l_sp L))),
    (fst (snd (snd (rs_tup gv (rs_z_init L) (adler_v (raw_live (Some L)) (rs_z_init L) Vundef) (l_sp L)))),
     (op, snd (snd (snd (snd (rs_tup gv (rs_z_init L) (adler_v (raw_live (Some L)) (rs_z_init L) Vundef) (l_sp L))))))))) vs *
  state_mem gv vs L
  |-- istreamA gv Tsh vs (rs_set_call (rs_z_init L) (offset_val 0 stp) 0 (offset_val 0 op) 0) Vundef (Some L).
Proof.
  intros Ps Po LOK.
  set (t := rs_tup gv (rs_z_init L) (adler_v (raw_live (Some L)) (rs_z_init L) Vundef) (l_sp L)).
  rewrite !isptr_offset_val_zero by auto.
  pose proof (rs_z_init_ok L) as ZOK.
  set (z := rs_set_call (rs_z_init L) stp 0 op 0).
  assert (E: (stp, (fst (snd t), (fst (snd (snd t)), (op, snd (snd (snd (snd t))))))) =
             rs_tup gv z (adler_v (raw_live (Some L)) z Vundef) (l_sp L)) by reflexivity.
  rewrite E. apply (rs_istreamA_fold gv Tsh vs z Vundef L); auto.
Qed.

(* the output object before any inflate() call: no output, undefined bytes *)
Lemma rs_out_empty sh n q:
  data_at_ sh (tarray tuchar n) q = data_at sh (tarray tuchar n) (bytes_rep [] ++ Zrepeat Vundef (n - Zlength (@nil Z))) q.
Proof. unfold data_at_. rewrite Z.sub_0_r. reflexivity. Qed.

(* a branch excluded by the value of its test *)
Ltac rs_nob := exfalso; first [ congruence | exact (Int.one_not_zero ltac:(assumption)) | contradiction ].

Lemma seg_init_ok {Espec: OracleKind} P gv vs vwb n nb na wr window stp s0 dp d op ep c lens:
  rs_facts P -> rs_A_facts n nb na wr window stp s0 dp d op -> rs_c_ok wr window c -> rs_lens_ok nb n lens ->
  Zlength (rs_src wr c s0 (rs_pads wr s0 lens) lens d) = Zlength s0 ->
  semax Delta_m (rs_inv P gv vs vwb stp (rs_src wr c s0 (rs_pads wr s0 lens) lens d) dp d op ep) rs_seg32 POST_B ->
  semax Delta_m (rs_D gv vs vwb n nb na wr window stp s0 dp d op ep c lens) rs_seg25 POST_B.
Proof.
  intros PF AF CF LF Hlen K.
  unfold rs_D, rs_seg25, Delta_m, Gmain_k, POST_B, POST_m. simplify_func_tycontext. abbreviate_semax.
  pose proof (rs_ok_of _ _ _ _ _ _ _ _ _ _ _ _ AF CF LF) as OK.
  destruct AF as (Hn & Hnb & Hna & Hwr & Hw & Hs0 & Hd & Bs & Bd & Pst & Pdp & Pop).
  subst n.
  set (src := rs_src wr c s0 (rs_pads wr s0 lens) lens d) in *.
  assert_PROP (isptr vs) as Pvs by entailer!.
  change (Tstruct _z_stream_s noattr) with t_zsl.
  rewrite (rs_strm_undef Tsh vs).
  forward_call (vs, Tsh, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef,
                Vundef, Vundef, Vundef).
  rewrite (rs_ns_raw_eq gv).
  forward. { entailer!. change (Int.signed Int.zero) with 0. rep_lia. }
  forward. forward.
  rewrite Int.neg_repr, add_repr.
  forward. { entailer!. rewrite rs_wb_znth by lia. exact I. }
  rewrite rs_wb_znth by lia.
  assert_PROP (isptr (gv ___stringlit_rfc_stored_1)) as Pver by (unfold rs_hversion_lit; entailer!).
  unfold rs_hversion_lit.
  forward_call (gv, Tsh, vs, rs_ns_raw, Vundef, Vundef, nullval, rs_iw wr window, gv ___stringlit_rfc_stored_1, Ers,
                rs_hver_vals, 49, 112).
  { rewrite if_false by (destruct vs; try contradiction; discriminate). cancel. }
  { change (Zlength rs_hver_vals) with 6. unfold rs_iw.
    destruct (wr =? 1); [ | destruct (wr =? 2)]; rep_lia. }
  Intros vret. destruct vret as [alloc_ok sp]. simpl fst in *. simpl snd in *.
  sep_apply (data_at_data_at_ Tsh (tarray tint 3)).
  rewrite (rs_init_ret vs _ alloc_ok Pvs).
  destruct alloc_ok; [destruct (wbits_ok (rs_iw wr window)) eqn:WOK | ].
  2, 3: forward_if; [ match goal with |- context [init_mem _ _ _ _ _ _ _ ?ret _ _] =>
                        sep_apply (rs_init_fail_mem gv vs rs_ns_raw Vundef Vundef nullval ret sp (rs_iw wr window)
                                     Pvs ltac:(discriminate)) end; ret0
                    | rs_nob ].
  forward_if. { rs_nob. }
  rewrite (rs_init_ok_mem gv vs _ _ _ _ sp _ Pvs).
  set (L := init_live sp (rs_iw wr window)).
  assert_PROP (live_ok L) as LOK by (unfold istream_raw; entailer!).
  sep_apply (rs_init_istreamA gv Tsh vs L).
  rewrite rs_istreamA_unfold. Intros.
  forward. forward.
  sep_apply (rs_init_set gv vs stp op L Pst Pop LOK).
  assert (HP: P src d 0 [] (rs_z_init L) L).
  { apply (rf_init P PF); auto.
    assert (0 <= rs_hl wr <= 10 /\ 0 <= rs_tl wr <= 8) by (unfold rs_hl, rs_tl; destruct (wr =? 1);
      [lia | destruct (wr =? 2); lia]).
    rep_lia. }
  unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
  eapply semax_pre; [ | apply K ].
  unfold rs_inv. Exists 0 (@nil Z) (rs_z_init L) L 0 0.
  rewrite Hlen.
  (* fold the harness's version literal back, so that the entailment never compares it with version_lit *)
  match goal with |- context [@data_at ?cs Ers (tarray tschar ?k) ?v ?q] =>
    change (@data_at cs Ers (tarray tschar k) v q) with (rs_hversion_lit gv) end.
  rewrite (rs_out_empty Ews (Zlength d) op).
  rewrite !isptr_offset_val_zero by auto.
  pose proof (rs_z_init_ok L). pose proof (rs_init_swfW sp (rs_iw wr window)).
  entailer!.
Qed.

(* Law inflate_decode, main: the body of the block loop (BFINAL, the stored or Huffman block, isb, the exit after
   the final block), from the part lemmas (IDMainStored, IDMainHuff, IDMainLit, IDMainRef, IDMainEob). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.HarnessRef
               Zlib.proof.adler32.MainLib.
Require Zlib.proof.crc32.HarnessRef.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.inflate_common.HarnessLib.
Require Import Zlib.proof.harness.inflate_common.DRefSpec.
Require Import Zlib.proof.rfc1951.Decode.
Require Import Zlib.proof.harness.inflate_decode.IDLawCS Zlib.proof.harness.inflate_decode.IDGlobals.
Require Import Zlib.harness.x_inflate_decode.code.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.harness.inflate_decode.IDMainKit.
Require Import Zlib.proof.harness.inflate_decode.IDMainStored Zlib.proof.harness.inflate_decode.IDMainHuff
               Zlib.proof.harness.inflate_decode.IDMainLit Zlib.proof.harness.inflate_decode.IDMainRef
               Zlib.proof.harness.inflate_decode.IDMainEob.

(* ---------------------------------------------------------------------------------------------- *)
(* Pure facts of the block sequence                                                               *)

Lemma enc_nf_app p bs b :
  enc_nf p (bs ++ [b]) = enc_nf p bs ++ enc_block (p + Zlength (enc_nf p bs)) false b.
Proof.
  revert p. induction bs as [|c r IH]; intros p; cbn [enc_nf app].
  - rewrite app_nil_r, Zlength_nil, Z.add_0_r. reflexivity.
  - rewrite IH, <- app_assoc, Zlength_app, Z.add_assoc. reflexivity.
Qed.

Lemma enc_blocks_app p bs b :
  enc_blocks p (bs ++ [b]) = enc_nf p bs ++ enc_block (p + Zlength (enc_nf p bs)) true b.
Proof.
  revert p. induction bs as [|c r IH]; intros p.
  - cbn [enc_blocks enc_nf app]. rewrite !app_nil_r, Zlength_nil, Z.add_0_r. reflexivity.
  - change ((c :: r) ++ [b]) with (c :: (r ++ [b])).
    assert (Hne: r ++ [b] <> []) by (destruct r; discriminate).
    transitivity (enc_block p false c ++ enc_blocks (p + Zlength (enc_block p false c)) (r ++ [b])).
    { cbn [enc_blocks]. destruct (r ++ [b]); [contradiction | reflexivity]. }
    rewrite IH. cbn [enc_nf]. rewrite <- app_assoc, Zlength_app, Z.add_assoc. reflexivity.
Qed.

Lemma expand_app hist bs b : expand hist (bs ++ [b]) = block_data (expand hist bs) b.
Proof. unfold expand. rewrite fold_left_app. reflexivity. Qed.

Lemma blocks_ok_app wmax out bs b :
  blocks_ok wmax out bs -> block_ok wmax (fold_left block_data bs out) b -> blocks_ok wmax out (bs ++ [b]).
Proof.
  revert out. induction bs as [|c r IH]; intros out H1 H2; simpl in *.
  - tauto.
  - destruct H1 as [Hc Hr]. split; auto.
Qed.

Lemma removelast_app1 {A} (l: list A) (x: A) : removelast (l ++ [x]) = l.
Proof. apply removelast_last. Qed.

Lemma enc_bits_final W bs b :
  enc_bits W bs ++ enc_block (Zlength (enc_nf 0 bs)) true b = bytes_bits (hdr_bytes W) ++ enc_blocks 0 (bs ++ [b]).
Proof. unfold enc_bits. rewrite enc_blocks_app, <- app_assoc. reflexivity. Qed.

Lemma enc_bits_next W bs b :
  enc_bits W bs ++ enc_block (Zlength (enc_nf 0 bs)) false b = enc_bits W (bs ++ [b]).
Proof. unfold enc_bits. rewrite enc_nf_app, <- app_assoc. reflexivity. Qed.

Lemma isb_vals isbz k : 0 <= k < Zlength isbz ->
  upd_Znth k (bytes_rep isbz) (Vint (Int.zero_ext 8 (Int.repr 1))) = bytes_rep (upd_Znth k isbz 1).
Proof.
  intros. unfold bytes_rep.
  rewrite <- (upd_Znth_map (fun b : Z => Vint (Int.repr b)) k isbz 1). reflexivity.
Qed.

Lemma lz_copy_len n d out : Zlength out <= Zlength (lz_copy n d out).
Proof.
  revert out. induction n as [|n IH]; intros out; simpl; [lia | ].
  specialize (IH (out ++ [Znth (Zlength out - d) out])). rewrite Zlength_app in IH.
  pose proof (Zlength_nonneg [Znth (Zlength out - d) out]). lia.
Qed.

Lemma syms_data_len out syms : Zlength out <= Zlength (syms_data out syms).
Proof.
  unfold syms_data. revert out. induction syms as [|s r IH]; intros out; simpl; [lia | ].
  specialize (IH (sym_data out s)).
  assert (Zlength out <= Zlength (sym_data out s)).
  { destruct s; simpl; [rewrite Zlength_app, Zlength_cons, Zlength_nil; lia | apply lz_copy_len]. }
  lia.
Qed.

Lemma block_data_len out b : Zlength out <= Zlength (block_data out b).
Proof.
  destruct b; simpl; [rewrite Zlength_app; pose proof (Zlength_nonneg bytes); lia | apply syms_data_len ..].
Qed.

Lemma fold_block_len bs out : Zlength out <= Zlength (fold_left block_data bs out).
Proof.
  revert out. induction bs as [|b r IH]; intros out; simpl; [lia | ].
  specialize (IH (block_data out b)). pose proof (block_data_len out b). lia.
Qed.

Lemma expand_firstn_len hist bs k : Zlength (expand hist (firstn k bs)) <= Zlength (expand hist bs).
Proof.
  rewrite <- (firstn_skipn k bs) at 2. unfold expand. rewrite fold_left_app. apply fold_block_len.
Qed.

Lemma isb_ok_app bs b isbz :
  isb_ok bs isbz -> Zlength (block_data (expand [] bs) b) <= 262144 ->
  isb_ok (bs ++ [b]) (upd_Znth (Zlength (block_data (expand [] bs) b)) isbz 1).
Proof.
  intros (Hl & Hb & Hk) Hn.
  assert (Hn0: 0 <= Zlength (block_data (expand [] bs) b)) by apply Zlength_nonneg.
  split; [rewrite upd_Znth_Zlength by lia; lia | ].
  split.
  { unfold is_bytes in *. apply Forall_upd_Znth; auto; rep_lia. }
  intros k Hk'. rewrite Zlength_app, Zlength_cons, Zlength_nil in Hk'.
  destruct (zeq k (Zlength bs + 1)) as [E | E].
  - subst k. rewrite firstn_all2 by (rewrite app_length; simpl; rewrite Zlength_correct in *; lia).
    rewrite expand_app, upd_Znth_same by lia. lia.
  - assert (Hk2: 0 <= k <= Zlength bs) by lia.
    rewrite List.firstn_app, (proj2 (Nat.sub_0_le _ _)) by (rewrite Zlength_correct in Hk2; lia).
    simpl. rewrite app_nil_r.
    destruct (zeq (Zlength (expand [] (firstn (Z.to_nat k) bs))) (Zlength (block_data (expand [] bs) b)))
      as [E2 | E2].
    + rewrite E2, upd_Znth_same by lia. lia.
    + pose proof (expand_firstn_len [] bs (Z.to_nat k)).
      pose proof (block_data_len (expand [] bs) b).
      pose proof (Zlength_nonneg (expand [] (firstn (Z.to_nat k) bs))).
      rewrite upd_Znth_diff by lia. auto.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The bit writer's struct at the law's compspecs                                                 *)

Lemma bw_struct_cs sh (v: val * (val * val)) q :
  @data_at Zlib.contracts.x_inflate_decode.Harness.CS sh t_bw v q = @data_at CS sh (Tstruct _bw noattr) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_harness); [apply JMeq_refl | reflexivity]. Qed.

Lemma bw_at_law sh bsh B cap buf w :
  bw_at sh bsh B cap buf w =
  EX c: list val, !! bw_bytes_ok B cap c &&
    (@data_at CS sh (Tstruct _bw noattr)
       (buf, (Vint (Int.repr (Zlength B / 8)), Vint (Int.repr (Zlength B mod 8)))) w *
     @data_at Zlib.contracts.x_inflate_decode.Harness.CS bsh (tarray tuchar cap) c buf)%logic.
Proof. unfold bw_at, bw_rep. f_equal. extensionality c. rewrite bw_struct_cs. reflexivity. Qed.

Lemma bw_fold sh bsh B cap buf w c : bw_bytes_ok B cap c ->
  (@data_at CS sh (Tstruct _bw noattr)
     (buf, (Vint (Int.repr (Zlength B / 8)), Vint (Int.repr (Zlength B mod 8)))) w *
   @data_at Zlib.contracts.x_inflate_decode.Harness.CS bsh (tarray tuchar cap) c buf)%logic
  |-- bw_at sh bsh B cap buf w.
Proof. intros. rewrite bw_at_law. Exists c. entailer!. Qed.

(* 8 bytes of room (the harness's gp_assume) give room for 57 bits *)
Lemma room8 B cap k : 0 <= k <= 57 -> Zlength B / 8 + 8 <= cap -> cap <= Int.max_unsigned -> bw_room B cap k.
Proof.
  intros Hk Hr Hc. unfold bw_room. split; [lia | split; [ | lia]].
  pose proof (Zlength_nonneg B). pose proof (Z.div_mod (Zlength B) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (Zlength B) 8 ltac:(lia)).
  set (q := Zlength B / 8) in *. set (r := Zlength B mod 8) in *.
  assert ((Zlength B + k + 7) / 8 < q + 9); [ | lia].
  apply Z.div_lt_upper_bound; lia.
Qed.

Lemma pack_len B : Zlength (pack B) = (Zlength B + 7) / 8.
Proof.
  unfold pack. rewrite Zlength_map, Zlength_correct, seq_length.
  apply Z2Nat.id. apply Z.div_pos; [pose proof (Zlength_nonneg B) | ]; lia.
Qed.

Lemma bw_len_bound B cap c :
  bw_bytes_ok B cap c -> 0 <= Zlength B / 8 <= cap /\ (Zlength B + 7) / 8 <= cap.
Proof.
  intros (_ & H & _). rewrite pack_len in H. pose proof (Zlength_nonneg B).
  assert (Zlength B / 8 <= (Zlength B + 7) / 8) by (apply Z.div_le_mono; lia).
  split; [split; [apply Z.div_pos | ] | ]; lia.
Qed.

(* the argument of gp_assume(x + k <= 1 << 19) *)
Ltac room_arg x k m :=
  try change (let (q, _) := Z.div_eucl (Zlength ?B) 8 in q) with (Zlength B / 8);
  try change (Int.shl (Int.repr 1) (Int.repr 19)) with (Int.repr 524288);
  unfold Int.ltu; rewrite ?Int.add_signed, ?Int.unsigned_repr by rep_lia;
  destruct (zlt m (x + k)); destruct (Z.leb_spec (x + k) m); try lia; reflexivity.

(* abstract the big objects' sizes (array loads/stores overflow the stack on the literals), and restore them *)
Ltac abs_sizes :=
  set (N0 := 262144) in *; set (N1 := 262145) in *; set (N2 := 524288) in *;
  assert (HN0: 262144 <= N0 <= 262144) by (unfold N0; lia);
  assert (HN1: 262145 <= N1 <= 262145) by (unfold N1; lia);
  assert (HN2: 524288 <= N2 <= 524288) by (unfold N2; lia);
  clearbody N0 N1 N2.
Ltac rest_sizes :=
  match goal with N0: Z, N1: Z, N2: Z, HN0: 262144 <= ?N0 <= 262144, HN1: 262145 <= ?N1 <= 262145,
                  HN2: 524288 <= ?N2 <= 524288 |- _ =>
    assert (N0 = 262144) by lia; assert (N1 = 262145) by lia; assert (N2 = 524288) by lia; subst N0 N1 N2
  end.

Ltac show := match goal with |- semax _ ?P _ _ => fail 100 "PRE" P | |- ?G => fail 100 "GOAL" G end.
Ltac gpa := forward_call (Int.repr 1); [ solve [entailer!; try reflexivity] .. | ].

(* the symbol loop of a Huffman block and its end-of-block code *)
Lemma id_sym_ok {Espec: OracleKind} gv vw vll vlc vdc vs vosn wrap wb flevel isel datap srcp isbp Fr
    bs ls isbz last hk llc lcc dcc (R: ret_assert) :
  blk_hyps wrap wb flevel isel datap srcp isbp bs ls isbz last -> hk_ok hk -> hk_arrays_ok hk llc lcc dcc ->
  semax Delta_id
    (sym_inv gv vw vll vlc vdc vs vosn wrap wb flevel isel datap srcp isbp Fr bs ls isbz last hk llc lcc dcc)
    S_sym
    (overridePost (blk_done gv vw vll vlc vdc vs vosn wrap wb flevel isel datap srcp isbp Fr bs ls isbz last) R).
Proof.
  intros HH Hk Ha. destruct R as [Rn Rb Rc Rr].
  rewrite S_sym_eq.
  unfold Delta_id, Gmain_k. simplify_func_tycontext.
  forward_loop (sym_inv gv vw vll vlc vdc vs vosn wrap wb flevel isel datap srcp isbp Fr bs ls isbz last hk llc lcc dcc)
    continue: (sym_inv gv vw vll vlc vdc vs vosn wrap wb flevel isel datap srcp isbp Fr bs ls isbz last hk llc lcc dcc)
    break: (sym_post gv vw vll vlc vdc vs vosn wrap wb flevel isel datap srcp isbp Fr bs ls isbz last hk llc lcc dcc).
  { apply andp_left2, derives_refl. }
  { unfold sym_inv at 1, sym_at. Intros syms dcont.
    forward. unfold seg_symb. abbreviate_semax.
    forward_call tt. Intros kind.
    rewrite bw_at_law. Intros c. rename H2 into Hbw.
    forward.
    set (B0 := sym_bits wrap wb flevel bs last hk syms) in *.
    change (enc_bits (id_wrapper wrap wb flevel) bs ++ bits_le last 1 ++ hk_bits hk ++
            flat_map (send_one (hk_ll hk) (hk_dl hk)) syms) with B0 in *.
    destruct (bw_len_bound _ _ _ Hbw) as [HB0 HB1].
    forward_call (Int.repr (if Zlength B0 / 8 + 8 <=? 524288 then 1 else 0)).
    { clearbody B0. entailer!. room_arg (Zlength B0 / 8) 8 524288. }
    assumed. apply Z.leb_le in E.
    sep_apply (bw_fold Tsh Ews B0 524288 srcp vw c Hbw).
    assert (EB0: B0 = sym_bits wrap wb flevel bs last hk syms) by reflexivity. clearbody B0.
    forward_if.
    { forward. unfold sym_post. Exists syms dcont. subst B0. entailer!. apply derives_refl. }
    unfold abbreviate in POSTCONDITION. subst POSTCONDITION.
    forward_if.
    { eapply semax_pre; [ | eapply (id_lit_ok gv vw vll vlc vdc vs vosn wrap wb flevel isel datap srcp isbp Fr
                                     bs ls isbz last hk llc lcc dcc syms dcont kind); auto ].
      unfold kind_at. subst B0. entailer!. apply derives_refl. }
    { eapply semax_pre; [ | eapply (id_ref_ok gv vw vll vlc vdc vs vosn wrap wb flevel isel datap srcp isbp Fr
                                     bs ls isbz last hk llc lcc dcc syms dcont kind); auto; lia ].
      unfold kind_at. subst B0. entailer!. apply derives_refl. } }
  unfold abbreviate in POSTCONDITION. subst POSTCONDITION.
  apply (id_eob_ok gv vw vll vlc vdc vs vosn wrap wb flevel isel datap srcp isbp Fr bs ls isbz last hk llc lcc dcc
           (Build_ret_assert Rn Rb Rc Rr)); auto.
Qed.

Lemma id_blk_ok {Espec: OracleKind} gv vw vll vlc vdc vs vosn wrap wb flevel isel datap srcp isbp Fr
    bs ls dcont isbz llc lcc dcc (Post: ret_assert) :
  par_ok wrap wb flevel isel -> isptr datap -> isptr srcp -> isptr isbp ->
  semax Delta_id
    (enc_at gv vw vll vlc vdc vs vosn wrap wb flevel isel datap srcp isbp Fr bs ls dcont isbz llc lcc dcc)
    seg_blk
    (loop_nocontinue_ret_assert (enc_inv gv vw vll vlc vdc vs vosn wrap wb flevel isel datap srcp isbp Fr)
       (overridePost (enc_post gv vw vll vlc vdc vs vosn wrap wb flevel isel datap srcp isbp Fr) Post)).
Proof.
  intros Hpar Pd Ps Pi. destruct Post as [Pn Pb Pc Pr].
  unfold enc_at. Intros.
  unfold seg_blk, Delta_id, Gmain_k. simplify_func_tycontext. abbreviate_semax.
  forward_call tt. Intros more.
  forward_call tt. Intros btype.
  forward.
  set (last := Z.b2z (zeq more 0)).
  assert (Hlast: last = 0 \/ last = 1) by (unfold last; destruct (zeq more 0); simpl; auto).
  assert (Elast: last = Z.b2z (zeq more 0)) by reflexivity. clearbody last.
  set (ls' := if zeq more 0 then Zlength (expand [] bs) else ls).
  assert (Els: ls' = if zeq more 0 then Zlength (expand [] bs) else ls) by reflexivity. clearbody ls'.
  forward_if (PROP ()
   LOCAL (temp _last (Vint (Int.repr last));
   temp _btype (Vint (Int.repr btype));
   temp _wrap (Vint (Int.repr wrap)); temp _wb (Vint (Int.repr wb));
   temp _flevel (Vint (Int.repr flevel)); temp _isel (Vint (Int.repr isel));
   temp _data datap; temp _src srcp; temp _isb isbp;
   temp _maxd (Vint (Int.repr (2 ^ wb)));
   temp _n (Vint (Int.repr (Zlength (expand [] bs))));
   temp _last_start (Vint (Int.repr ls')); lvar _osnap (tptr tuchar) vosn;
   lvar _s (Tstruct _z_stream_s noattr) vs;
   lvar _dcodes (tarray tushort 30) vdc;
   lvar _lcodes (tarray tushort 286) vlc; lvar _ll (tarray tuchar 316) vll;
   lvar _w (Tstruct _bw noattr) vw; gvars gv)
   SEP (bw_at Tsh Ews (enc_bits (id_wrapper wrap wb flevel) bs) 524288 srcp vw;
   data_at Ews (tarray tuchar 262144) dcont datap;
   data_at Ews (tarray tuchar 262145) (bytes_rep isbz) isbp;
   malloc_token Ews (tarray tuchar 262144) datap;
   malloc_token Ews (tarray tuchar 524288) srcp;
   malloc_token Ews (tarray tuchar 262145) isbp;
   data_at Tsh (tarray tuchar 316) llc vll;
   data_at Tsh (tarray tushort 286) lcc vlc;
   data_at Tsh (tarray tushort 30) dcc vdc; dref_tabs gv Ers id_tabs;
   data_at Ers (tarray tuchar 19) (zvals clorder) (gv _cl_order);
   data_at_ Tsh (Tstruct _z_stream_s noattr) vs;
   data_at_ Tsh (tptr tuchar) vosn; mem_mgr gv; dres gv; Fr)).
  { forward. assert (ls' = Zlength (expand [] bs)) as ->.
    { rewrite Els. destruct (zeq more 0); auto. subst last. simpl in *. contradiction. }
    entailer!. }
  { forward. assert (ls' = ls) as ->.
    { rewrite Els. destruct (zeq more 0); auto. subst last. simpl in *. discriminate. }
    entailer!. }
  forward.
  assert (Ebt0: Int.and (Int.repr btype) (Int.repr 3) = Int.repr (Z.land btype 3)).
  { unfold Int.and. rewrite !Int.unsigned_repr by rep_lia. reflexivity. }
  assert (Ebt: Z.land btype 3 = btype mod 4) by (change 3 with (Z.ones 2); rewrite Z.land_ones by lia; reflexivity).
  set (bt := Z.land btype 3) in *.
  assert (Hbt: 0 <= bt <= 3) by (rewrite Ebt; pose proof (Z.mod_pos_bound btype 4); lia).
  clearbody bt.
  rewrite Ebt0.
  rewrite bw_at_law. Intros c.
  forward.
  set (B0 := enc_bits (id_wrapper wrap wb flevel) bs) in *.
  destruct (bw_len_bound _ _ _ H5) as [HB0 HB1].
  forward_call (Int.repr (if Zlength B0 / 8 + 8 <=? 524288 then 1 else 0)).
  { clearbody B0. entailer!. room_arg (Zlength B0 / 8) 8 524288. }
  assumed. apply Z.leb_le in E.
  sep_apply (bw_fold Tsh Ews B0 524288 srcp vw c H5).
  forward_call (Tsh, Ews, B0, 524288, srcp, vw, last, 1).
  { apply room8; rep_lia. }
  assert (HH: blk_hyps wrap wb flevel isel datap srcp isbp bs ls' isbz last).
  { destruct H0 as (? & ? & ? & ?).
    refine (conj Hpar (conj Pd (conj Ps (conj Pi (conj H (conj _ (conj H1 (conj Hlast _)))))))); [lia | ].
    intros L1. rewrite Els. destruct (zeq more 0); auto. subst last. simpl in L1. discriminate. }
  assert (EB0: B0 = enc_bits (id_wrapper wrap wb flevel) bs) by reflexivity. clearbody B0.
  forward_if (blk_done gv vw vll vlc vdc vs vosn wrap wb flevel isel datap srcp isbp Fr bs ls' isbz last).
  { (* stored *)
    subst bt. unfold abbreviate in POSTCONDITION, MORE_COMMANDS. subst POSTCONDITION MORE_COMMANDS.
    eapply semax_pre; [ | apply (id_stored_ok gv vw vll vlc vdc vs vosn wrap wb flevel isel datap srcp isbp Fr
                                   bs ls' dcont isbz llc lcc dcc last (normal_ret_assert FF)); exact HH ].
    unfold blk_mid. subst B0. entailer!. }
  { (* Huffman *)
    unfold abbreviate in POSTCONDITION, MORE_COMMANDS. subst POSTCONDITION MORE_COMMANDS.
    eapply semax_pre; [ | apply (id_huff_ok gv vw vll vlc vdc vs vosn wrap wb flevel isel datap srcp isbp Fr
                                   bs ls' dcont isbz llc lcc dcc last bt (normal_ret_assert (blk_done gv vw vll vlc vdc vs vosn wrap wb flevel isel datap srcp isbp Fr bs ls' isbz last))); [exact HH | | ] ].
    2: { assert (bt <> 0) by (intro X; subst bt; contradiction). lia. }
    { unfold blk_mid. subst B0. entailer!. }
    intros hk llc' lcc' dcc' Hk Hdyn Harr.
    apply (id_sym_ok gv vw vll vlc vdc vs vosn wrap wb flevel isel datap srcp isbp Fr bs ls' isbz last hk
             llc' lcc' dcc' (normal_ret_assert FF)); auto. }
  (* isb[n] = 1; if (last) break; *)
  unfold blk_done. Intros b dcont' llc' lcc' dcc'.
  set (D' := block_data (expand [] bs) b) in *.
  assert (HD': 0 <= Zlength D' <= 262144) by (destruct H7 as (? & ? & ? & ?); pose proof (Zlength_nonneg D'); lia).
  abs_sizes.
  forward.
  rest_sizes.
  forward_if.
  { (* the final block *)
    forward.
    assert (L1: last = 1) by lia. rewrite L1.
    destruct HH as (_ & _ & _ & _ & _ & _ & _ & _ & Hls).
    pose proof H1 as (Hil & _ & _).
    rewrite isb_vals by lia. rewrite enc_bits_final.
    unfold enc_post. Exists (bs ++ [b]) ls' dcont' (upd_Znth (Zlength D') isbz 1) llc' lcc' dcc'.
    rewrite expand_app. fold D'. rewrite removelast_app1.
    assert (blocks_ok (2 ^ wb) [] (bs ++ [b])) by (apply blocks_ok_app; auto).
    assert (isb_ok (bs ++ [b]) (upd_Znth (Zlength D') isbz 1)) by (apply isb_ok_app; auto; exact (proj2 HD')).
    entailer!. destruct bs; discriminate. }
  { forward.
    assert (L0: last = 0) by (destruct Hlast; auto; subst; discriminate). rewrite L0.
    pose proof H1 as (Hil & _ & _).
    rewrite isb_vals by lia. rewrite enc_bits_next.
    unfold enc_inv, enc_at. Exists (bs ++ [b]) ls' dcont' (upd_Znth (Zlength D') isbz 1) llc' lcc' dcc'.
    rewrite expand_app. fold D'.
    assert (blocks_ok (2 ^ wb) [] (bs ++ [b])) by (apply blocks_ok_app; auto).
    assert (isb_ok (bs ++ [b]) (upd_Znth (Zlength D') isbz 1)) by (apply isb_ok_app; auto; exact (proj2 HD')).
    entailer!. }
Qed.

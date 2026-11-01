(* deflateInit2_ with a caller-supplied allocator, the branch where one of the four buffer allocations returned
   Z_NULL (see InitZKit.v): the state is marked FINISH_STATE, strm->msg is set, deflateEnd gives back every block
   that was allocated, and Z_MEM_ERROR is returned; the failed allocation is among the allocator's events. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DModel3 Zlib.proof.deflate.DCS.
Require Import Zlib.deflate.code.
Require Import Zlib.proof.za.deflate.Stmt.
Require Import Zlib.proof.deflate.ApiKit.
Require Import Zlib.proof.deflate.ZeroBytes Zlib.proof.deflate.InitKit Zlib.proof.deflate.InitKit2.
Require Import Zlib.proof.deflate.InitFacts Zlib.proof.deflate.InitTac.
Require Import Zlib.proof.deflate.InitParts.
Require Import Zlib.proof.za.deflate.InitZParts.
Require Import Zlib.proof.za.deflate.InitZKit.

Arguments zrest : simpl never.
Arguments zpad : simpl never.
Arguments zlate : simpl never.

Section ZA.
Context {ZA : zallocator}.

Lemma iz_fail_part {Espec : OracleKind} (strmp : val) (level wbits mem strategy : Z) (vp : val)
    (vsh : share) (vers : list Z) (ssize : Z) (ni tin tout msgv adler dt st0 : val) (gv : globals) (tr : list zev)
    (sp pw pp ph pb : val) :
  s32_ok level -> s32_ok 8 -> s32_ok wbits -> s32_ok mem -> s32_ok strategy -> s32_ok ssize ->
  readable_share vsh -> 1 <= Zlength vers -> -128 <= Znth 0 vers < 128 ->
  (forall a1 a2 a3 a4 a5 : bool, exists r : option dstate * strm * Z,
     c_deflateInit2_ true true false level 8 wbits mem strategy a1 a2 a3 a4 a5 zrst0 = Some r) ->
  za_alloc <> nullval -> za_free <> nullval -> is_pointer_or_null za_opaque ->
  za_now tr + (5968 + 65536 + 65536 + 131072 + 131072) <= za_cap ->
  (Znth 0 vers =? 49) = true -> (ssize =? 112) = true -> strmp <> nullval -> isptr za_alloc -> isptr za_free ->
  -15 <= wbits -> i_bad level 8 wbits mem strategy = false ->
  1 <= mem <= 9 -> 9 <= i_wb9 wbits <= 15 -> 0 <= i_lv level <= 9 -> 0 <= strategy <= 4 -> 0 <= i_wr wbits <= 2 ->
  512 <= Z.shiftl 1 (i_wb9 wbits) <= 32768 -> 256 <= Z.shiftl 1 (mem + 7) <= 65536 ->
  128 <= Z.shiftl 1 (mem + 6) <= 32768 ->
  sp <> nullval -> field_compatible t_ds [] sp ->
  1 <= Z.shiftl 1 (i_wb9 wbits) <= 65536 -> 1 <= Z.shiftl 1 (mem + 7) <= 65536 ->
  1 <= Z.shiftl 1 (mem + 6) <= 65536 ->
  ((if EqDec_val pw nullval then true else false) || (if EqDec_val pp nullval then true else false) ||
   (if EqDec_val ph nullval then true else false) || (if EqDec_val pb nullval then true else false))%bool = true ->
  semax Delta_iz (iz_pre strmp level wbits mem strategy vp vsh vers ni tin tout adler dt gv tr sp pw pp ph pb)
    (Ssequence IZ_fail IZ_rest) (iz_fpost strmp level wbits mem strategy vp vsh vers ssize ni tin tout msgv adler st0 gv tr).
Proof.
  intros H H0 H1 H2 H3 H4 SH H5 Hv0 H6 Hza Hzf Hop Hcap Hv1 Hs1 H7 Pza Pzf Hwm Hbad Hmem Hwb9 Hlv Hstr Hwr BW BH BL
    Hsp FCs HW HHS HLB Hb21.
  cbv [IZ_fail IZ_rest IZ iz_ssub f_deflateInit2_ fn_body repeat app].
  unfold iz_pre, iz_fpost, Delta_iz. abbreviate_semax.
  forward.
  forward_if (temp _t'17 (Vint (Int.repr 0))).
  { match goal with H: Int.lt _ _ = true |- _ => vm_compute in H; discriminate end. }
  { forward. entailer!. }
  forward_if (temp _t'18 (Vint (Int.repr 6))).
  { match goal with H: ?x <> ?x |- _ => contradiction H; reflexivity end. }
  { forward. entailer!. }
  unfold deflate_globals, errmsg_at. Intros vs.
  forward.
  { entailer!. assert (HZ: is_pointer_or_null (Znth 6 vs)) by (apply Forall_Znth; auto; lia).
    destruct (Znth 6 vs); try contradiction; simpl in *; auto. }
  forward.
  assert (HZ6: is_pointer_or_null (Znth 6 vs)) by (apply Forall_Znth; auto; lia).
  pose proof (init_end_stream_za wbits mem strmp sp pw pp ph pb dt gv
    (Vint (Int.repr (i_wr wbits))) (Vlong (Int64.repr (Int.signed (Int.repr 0))))
    (Vint (Int.repr (i_wb9 wbits))) (Vint (Int.repr (Z.shiftl 1 (i_wb9 wbits))))
    (Vint (Int.repr (Z.shiftl 1 (i_wb9 wbits) - 1))) (Vint (Int.repr (mem + 7)))
    (Vint (Int.repr (Z.shiftl 1 (mem + 7)))) (Vint (Int.repr (Z.shiftl 1 (mem + 7) - 1)))
    (Vint (Int.divu (Int.repr (mem + 7 + 3 - 1)) (Int.repr 3))) (Vlong (Int64.repr (Int.signed (Int.repr 0))))
    (Vint (Int.repr (Z.shiftl 1 (mem + 6))))
    (Vlong (Int64.mul (Int64.repr (Int.unsigned (Int.repr (Z.shiftl 1 (mem + 6))))) (Int64.repr (Int.signed (Int.repr 4)))))
    FCs ltac:(lia) ltac:(lia)) as IES.
  cbv zeta in IES. sep_apply IES. clear IES.
  set (z0 := zrst0).
  set (z1 := set_z_msg (set_z_msg z0 None) (Some Z_MEM_ERROR)).
  match goal with |- context [za_res gv ?TR] =>
    forward_call (Some (i_end_state wbits mem), mkDP strmp sp pw pp ph pb nullval, strmp, ni, z1,
                  (@None dstate, z1, Z_OK), gv, TR) end.
  Intros tr'. cbn [fst snd]. unfold dclosed. Intros dt'.
  forward.
  Exists true (negb (if eq_dec pw nullval then true else false)) (negb (if eq_dec pp nullval then true else false))
    (negb (if eq_dec ph nullval then true else false)) (negb (if eq_dec pb nullval then true else false))
    (@None dstate, z1, Z_MEM_ERROR).
  cbn [fst snd]. Exists tr' nullval dt' (Znth 6 vs).
  change (Z_MEM_ERROR =? Z_OK) with false. change (Z_MEM_ERROR =? Z_VERSION_ERROR) with false.
  unfold rfv. cbv iota.
  unfold zfuncs_za, za_funcs, deflate_globals, errmsg_at, reset_fields. Exists vs.
  entailer!.
  split; [ | split; [ split | intros X; inv X] ].
  - rewrite Hv1, Hs1, init_mem2; auto.
    clear - Hb21. repeat match goal with |- context [eq_dec ?q nullval] => destruct (eq_dec q nullval) | H: context [EqDec_val ?q nullval] |- _ => destruct (EqDec_val q nullval) end; simpl in *; try discriminate; try contradiction; try reflexivity.
  - match goal with E : context [dend_events] |- _ => cbn [fst snd] in E; rewrite E end.
    unfold dend_events. cbn [p_pbuf p_head p_prev p_window].
    change (d_w_size (i_end_state wbits mem)) with (Z.shiftl 1 (i_wb9 wbits)).
    change (d_hash_size (i_end_state wbits mem)) with (Z.shiftl 1 (mem + 7)).
    change (tr_lit_bufsize (d_tr (i_end_state wbits mem))) with (Z.shiftl 1 (mem + 6)).
    rewrite !app_assoc.
    repeat first [ rewrite za_now_free | rewrite za_now_dend_free | rewrite za_now_zalloc_ev | rewrite za_now_alloc ].
    change (sizeof t_ds) with 5968.
    repeat match goal with |- context [eq_dec ?q nullval] => destruct (eq_dec q nullval) end; lia.
  - (* Z_MEM_ERROR: one of the four buffer allocations returned Z_NULL, its event is ZFail *)
    intros _. match goal with E : context [dend_events] |- _ => cbn [fst snd] in E; rewrite E end.
    rewrite !za_failed_app, !za_failed_zalloc_ev.
    clear - Hb21. change (@eq_dec val EqDec_val) with EqDec_val.
    destruct (EqDec_val pw nullval), (EqDec_val pp nullval), (EqDec_val ph nullval), (EqDec_val pb nullval);
      cbn [orb] in Hb21; try discriminate; rewrite ?orb_true_r; reflexivity.
Qed.

End ZA.

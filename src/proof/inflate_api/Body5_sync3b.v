(* Body of inflateSync, segment 3b (Body5_sync_kit.v): after `strm->avail_in -= len`, the updates of next_in and
   total_in and the test state->have != 4 (Z_DATA_ERROR when the pattern is not complete). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.Body5_sync_kit.
#[local] Existing Instance Zlib.units.Inflate.CS.

Local Open Scope logic.

(* from `strm->next_in += len` to the end *)
Definition sync_suf3b : statement := match sync_suf3 with Ssequence _ (Ssequence _ x) => x | _ => Sskip end.

Definition sync_seg3b : Prop :=
  forall (E: OracleKind) (gv: globals) (shs: share) (strmp: val) (z: zfields) (sp winp: val) (s: istate)
    (h: hstate) (headp: val) (hsh: share) (xb nb cb: val) (ish: share) (ip: val) (ilo ilen: Z) (ic: list val)
    (inp: list Z) (v_buf: val) (s1: istate) (bc: list val),
  sync_hyps shs strmp z ish ip ilo ilen ic inp ->
  live_ok (set_l_s (Live sp winp s h headp hsh xb nb cb) s1) -> i_mode s1 = SYNC -> 0 <= i_have s1 <= 320 ->
  sync_s s inp = (if fst (ssearch (i_have s1) inp) =? 4
    then SyncOk (sync_fin (set_i_have s1 (fst (ssearch (i_have s1) inp)))) (snd (ssearch (i_have s1) inp))
    else SyncData (set_i_have s1 (fst (ssearch (i_have s1) inp))) (snd (ssearch (i_have s1) inp))) ->
  semax (func_tycontext f_inflateSync Vprog_inflate Gp_sync nil)
    (sync_B gv shs strmp z sp headp winp v_buf bc s1 (i_wrap s1) (i_wbits s1) (fst (ssearch (i_have s1) inp))
       ish ip ilen ic (zf_ni z) (Zlength inp - snd (ssearch (i_have s1) inp)) (zf_tin z)
       (temp _len (Vint (Int.repr (snd (ssearch (i_have s1) inp))))))
    sync_suf3b
    (sync_post gv shs strmp z (Live sp winp s h headp hsh xb nb cb) (InBuf ish ip ilo ilen ic) inp).

Lemma sync_part3b (NEXT: sync_seg4) : sync_seg3b.
Proof.
  intros E gv shs strmp z sp winp s h headp hsh xb nb cb ish ip ilo ilen ic inp v_buf s1 bc.
  intros HY LOK1 M1 HV1 SG.
  pose proof HY as (HIN & NI & H2 & H0 & H4 & Hn).
  pose proof HIN as (ISH & IP & ILO & ILEN & IC & IMAX & ISUB & IBY).
  pose proof H0 as (ZAI & ZAO & ZTIN & ZTOUT & ZDT & ZADL).
  set (L := Live sp winp s h headp hsh xb nb cb) in LOK1.
  assert (Hsp: isptr sp) by (destruct LOK1 as (X & _); exact X).
  match goal with |- semax _ _ ?c _ =>
    let c' := eval cbv beta iota delta [sync_suf3b sync_suf3 sync_suf2 sync_suf1 f_inflateSync fn_body] in c in
    change c with c' end.
  sync_seg_start.
  remember (gv _zcalloc) as zca eqn:Hzca. remember (gv _zcfree) as zcf eqn:Hzcf.
    set (got := fst (ssearch (i_have s1) inp)) in *. set (len := snd (ssearch (i_have s1) inp)) in *.
    assert (GL: 0 <= got <= 320 /\ 0 <= len <= Zlength inp).
    { pose proof (ssearch_fst_bound (i_have s1) inp ltac:(lia)).
      pose proof (ssearch_range (i_have s1) inp ltac:(rep_lia)). unfold got, len. lia. }
    rewrite NI. forward. forward. forward. forward. forward.
    assert (EP: force_val (sem_add_ptr_int tuchar Unsigned (offset_val ilo ip) (Vint (Int.repr len))) =
                in_ptr (InBuf ish ip ilo ilen ic) len).
    { destruct ip; try contradiction. simpl. f_equal. rewrite Ptrofs.add_assoc. f_equal.
      unfold Ptrofs.of_intu, Ptrofs.of_int. rewrite Int.unsigned_repr by rep_lia.
      rewrite ptrofs_mul_repr, ptrofs_add_repr. f_equal. lia. }
    assert (ET: Int64.add (Int64.repr (zf_tin z)) (Int64.repr (Int.unsigned (Int.repr len))) =
                Int64.repr (u64 (zf_tin z + len))).
    { rewrite Int.unsigned_repr by rep_lia. rewrite add64_repr. unfold u64.
      change (2 ^ 64) with Int64.modulus. rewrite <- Int64.unsigned_repr_eq, Int64.repr_unsigned. reflexivity. }
    rewrite EP, ET.
    forward_if.
    { assert (G4: got <> 4) by (intro X; rewrite X in *; contradiction).
      forward.
      unfold on_live, is_live, fst3, snd3, thd3, sync_f. rewrite if_false by auto. cbn [l_s].
      rewrite SG, (proj2 (Z.eqb_neq _ _) G4). cbn [fst snd].
      unfold istream_opt. rewrite if_false by auto.
      unfold istream, state_mem, zstrm_at, strm_rep, in_rep.
      cbn [set_zf_in zf_ni zf_ai zf_tin zf_no zf_ao zf_tout zf_msg zf_dt zf_adler zf_res l_sp l_winp l_s l_h l_headp set_l_s].
      rewrite state_rep_sync.
      destruct (have_fields s1 got) as (HM & HW & HF & HB & HH & HBI & HG).
      rewrite HM, HW, HF, HB, HH, HBI, HG, U_sync_have, win_rep_have.
      pose proof (live_sync_have (set_l_s L s1) got LOK1 M1 ltac:(lia)) as LOK2.
      entailer!.
      apply zf_ok_in; auto; rep_lia. }
    (* the pattern was found *)
    match goal with X: got = 4 |- _ => rename X into G4 end.
    assert (SS: ssearch (i_have s1) inp = (4, len))
      by (rewrite <- G4; unfold got, len; destruct (ssearch (i_have s1) inp); reflexivity).
    rewrite G4, Z.eqb_refl in SG.
    drop_LOCALs [_t'8; _t'9; _t'10]. subst zca zcf. rewrite G4.
    exact (NEXT E gv shs strmp z sp winp s h headp hsh xb nb cb ish ip ilo ilen ic inp v_buf s1 bc len
             HY LOK1 M1 SS (proj2 GL) SG).
Qed.

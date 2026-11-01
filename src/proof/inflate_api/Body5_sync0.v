(* Body of inflateSync, segment 0 (Body5_sync_kit.v): on a live stream after inflateStateCheck, from
   `state = strm->state` to the test `if (state->mode != SYNC)`: the return Z_BUF_ERROR when
   there is no input and less than a byte in the bit buffer. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.Body5_sync_kit.
#[local] Existing Instance Zlib.units.Inflate.CS.

Local Open Scope logic.

(* from `state = strm->state` to the end *)
Definition sync_suf0 : statement := match fn_body f_inflateSync with Ssequence _ x => x | _ => Sskip end.

(* the state after inflateStateCheck on a live stream: sync_A without the temporary state *)
Definition sync_A0 (gv: globals) (shs: share) (strmp: val) (z: zfields) (sp headp winp v_buf: val) (s: istate)
    (ib: inbuf) : environ -> mpred :=
  PROP () LOCAL (lvar _buf (tarray tuchar 4) v_buf; gvars gv; temp _strm strmp)
  SEP (data_at shs t_strm (sync_strm gv z (zf_ni z) (zf_ai z) (zf_tin z) sp) strmp;
       field_at Ews t_state (DOT _strm) strmp sp;
       field_at Ews t_state (DOT _mode) (Vint (Int.repr (i_mode s))) sp;
       zfuncs gv; data_at_ Tsh (tarray tuchar 4) v_buf; malloc_token Ews t_state sp;
       field_at Ews t_state (DOT _wrap) (Vint (Int.repr (i_wrap s))) sp;
       field_at Ews t_state (DOT _flags) (Vint (Int.repr (i_flags s))) sp;
       field_at Ews t_state (DOT _wbits) (Vint (Int.repr (i_wbits s))) sp;
       field_at Ews t_state (DOT _hold) (Vlong (Int64.repr (i_hold s))) sp;
       field_at Ews t_state (DOT _bits) (Vint (Int.repr (i_bits s))) sp;
       field_at Ews t_state (DOT _have) (Vint (Int.repr (i_have s))) sp;
       U_sync gv sp headp winp s; win_rep winp s; state_pad sp; in_rep ib; mem_mgr gv).

Lemma sync_part0 (NEXT: sync_seg1) :
  forall (E: OracleKind) (gv: globals) (shs: share) (strmp: val) (z: zfields) (sp winp: val) (s: istate)
    (h: hstate) (headp: val) (hsh: share) (xb nb cb: val) (ish: share) (ip: val) (ilo ilen: Z) (ic: list val)
    (inp: list Z) (v_buf: val),
  sync_hyps shs strmp z ish ip ilo ilen ic inp ->
  live_ok (Live sp winp s h headp hsh xb nb cb) -> HEAD <= i_mode s <= SYNC ->
  semax (func_tycontext f_inflateSync Vprog_inflate Gp_sync nil)
    (sync_A0 gv shs strmp z sp headp winp v_buf s (InBuf ish ip ilo ilen ic))
    sync_suf0
    (sync_post gv shs strmp z (Live sp winp s h headp hsh xb nb cb) (InBuf ish ip ilo ilen ic) inp).
Proof.
  intros E gv shs strmp z sp winp s h headp hsh xb nb cb ish ip ilo ilen ic inp v_buf HY LOK HMD.
  pose proof HY as (HIN & NI & H2 & ZOK & H4 & Hn).
  pose proof HIN as (ISH & IP & ILO & ILEN & IC & IMAX & ISUB & IBY).
  pose proof ZOK as (ZAI & ZAO & ZTIN & ZTOUT & ZDT & ZADL).
  pose proof LOK as (Hsp & SW & MW & HW & SW3 & HS & WW).
  cbn [l_sp l_s l_h] in Hsp, SW, MW, HW, SW3, HS, WW.
  pose proof (sw_bits _ SW) as HBITS.
  match goal with |- semax _ _ ?c _ =>
    let c' := eval cbv beta iota delta [sync_suf0 f_inflateSync fn_body] in c in change c with c' end.
  unfold sync_A0, sync_strm, sync_post; simplify_func_tycontext; abbreviate_semax.
  remember (gv _zcalloc) as zca eqn:Hzca. remember (gv _zcfree) as zcf eqn:Hzcf.
    forward. forward. forward.
    forward_if (temp _t'2 (Vint (if andb (Zlength inp =? 0) (i_bits s <? 8) then Int.one else Int.zero))).
    { forward. forward. entailer!.
      assert (Zlength inp = 0) as ->.
      { rewrite <- H2. lia. }
      simpl andb.
      destruct (zlt (i_bits s) 8); [rewrite (proj2 (Z.ltb_lt _ _)) by lia | rewrite (proj2 (Z.ltb_ge _ _)) by lia]; reflexivity. }
    { forward. entailer!.
      destruct (Z.eqb_spec (Zlength inp) 0) as [E0 | E0]; [ | reflexivity].
      exfalso. rewrite <- H2 in E0. rewrite E0 in *. contradiction. }
    destruct (andb (Zlength inp =? 0) (i_bits s <? 8)) eqn:EB.
    { forward_if; [ | match goal with X: Int.one = Int.zero |- _ => inversion X end].
      forward.
      unfold on_live, fst3, snd3, thd3, is_live, istream_opt. rewrite !if_false by auto.
      unfold sync_f. cbn [l_s]. unfold sync_s. rewrite EB. cbn [fst snd].
      unfold istream, state_mem, zstrm_at, strm_rep. cbn [l_sp l_winp l_s l_h l_headp]. rewrite state_rep_sync.
      entailer!. }
    forward_if; [contradiction | ].
    drop_LOCALs [_t'2; _t'23; _t'25]. subst zca zcf.
    exact (NEXT E gv shs strmp z sp winp s h headp hsh xb nb cb ish ip ilo ilen ic inp v_buf HY LOK HMD EB).
Qed.

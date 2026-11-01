(* The prologue of inflate()'s body for calls of any uInt size (RTH9Parts.pro_part9_stmt) is proved in pieces
   (RTH9Pro.v and the files RTH9Pro<X>.v it requires), so that each file checks quickly.  This file holds what
   the pieces share: the statements that remain at the cut points (cut out of inflate_pre), the facts of a call
   with a live stream as one proposition [pro9_ctx], and the tactics that unpack and rebuild it. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.roundtrip.RTHSpec.
Require Import Zlib.proof.roundtrip.RTHCase.
Require Import Zlib.proof.inflate_api.Body5Conv.
Require Import Zlib.proof.inflate_api.Body5Pro.
Require Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Definition sq1 (s: statement) : statement := match s with Ssequence a _ => a | _ => Sskip end.
Definition sq2 (s: statement) : statement := match s with Ssequence _ b => b | _ => Sskip end.

(* inflate_pre = (call; if1; if2; if3); rest, where if1..if3 compute the argument check and rest starts with
   state = strm->state *)
Definition pro9_rest : statement := sq2 inflate_pre.
(* after the call of inflateStateCheck *)
Definition pro9_s1 : statement :=
  let c := sq1 inflate_pre in Ssequence (sq2 (sq1 (sq1 c))) (Ssequence (sq2 (sq1 c)) (Ssequence (sq2 c) pro9_rest)).
(* after the test of next_out *)
Definition pro9_s2 : statement :=
  let c := sq1 inflate_pre in Ssequence (sq2 (sq1 c)) (Ssequence (sq2 c) pro9_rest).
(* from LOAD() on *)
Definition pro9_s4 : statement := sq2 (sq2 pro9_rest).

(* the hypotheses of RTH9Parts.pro_part9_stmt for a live stream L *)
Definition pro9_ctx (gv: globals) (shs: share) (strmp: val) (z: zfields) (L: live) (ib: inbuf) (inp: list Z)
    (ob: option outbuf) (flush: Z) (gsh tsh: share) (itok otok: bool) (vh vl vb: val) (Hd: mpred)
    (Rr: option val -> environ -> mpred) : Prop :=
  Int.min_signed <= flush <= Int.max_signed /\ readable_share gsh /\ readable_share tsh /\
  in_tok_ok itok ib /\ out_tok_ok otok ob /\ zf_ni z = in_ptr ib 0 /\
  match ib with InNull => inp = [] | InBuf _ _ _ _ _ => in_ok ib inp /\ zf_ai z = Zlength inp end /\
  match ob with None => zf_no z = nullval | Some o => zf_no z = out_ptr o 0 /\ out_ok o (zf_ao z) end /\
  (inflate_bad strmp z (Some L) ib ob ->
   ENTAIL Delta_inflate5,
     PROPx [] (LOCALx [lvar _hbuf (tarray tuchar 4) vb; lvar _last t_code vl; lvar _here t_code vh; gvars gv]
       (SEPx [data_at_ Tsh (tarray tuchar 4) vb; data_at_ Tsh t_code vl; data_at_ Tsh t_code vh;
              istream_opt gv shs strmp z (Some L); Hd; htok6 (Some L);
              bufs_opt (Some L) ib ob [] itok otok;
              tables_rep gsh gv; Zlib.proof.crc32.Spec.crc_table_at tsh gv; mem_mgr gv; zfuncs gv]))
     |-- Rr (Some (Vint (Int.repr Z_STREAM_ERROR)))) /\
  strmp <> nullval /\ zf_ok z /\ writable_share shs /\ live_ok L.

(* unpack [pro9_ctx] into the hypotheses the proof script of the whole prologue has at that point *)
Ltac pro9_prelude HC :=
  destruct HC as (HF & HG & HT & HIT & HOT & HNI & HIB & HOB & HBAD & NN & ZOK & WS & LOK);
  match type of LOK with live_ok ?L =>
  match type of NN with ?strmp <> _ =>
  match type of ZOK with zf_ok ?z =>
  match type of HBAD with context [mem_mgr ?gv] =>
    assert (ISL: is_live strmp (Some L) = Some L) by (unfold is_live; rewrite if_false by auto; reflexivity);
    pose proof LOK as (LP & LS & LM & LH & LS3 & LW & LW0 & LHD & LWIN);
    assert (MC: ((HEAD <=? i_mode (l_s L)) && (i_mode (l_s L) <=? SYNC))%bool = true)
      by (pose proof (sw_mode _ LS); apply andb_true_intro; split; apply Z.leb_le; lia);
    remember (gv _zcalloc) as zca eqn:Hzca; remember (gv _zcfree) as zcf eqn:Hzcf
  end end end end.

(* rebuild [pro9_ctx] from those hypotheses *)
Ltac pro9_ctx_ok :=
  unfold pro9_ctx; do 12 (split; [first [assumption | split; assumption] | ]); assumption.

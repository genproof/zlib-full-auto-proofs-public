(* Body of inflateSync, segment 3 (Body5_sync_kit.v): after the search of the input, from `len = (its result)`
   and the update of avail_in (the rest in Body5_sync3b.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.Body5_sync_kit.
Require Import Zlib.proof.inflate_api.Body5_sync3b.
#[local] Existing Instance Zlib.units.Inflate.CS.

Local Open Scope logic.

Lemma sync_part3 (NEXT: sync_seg3b) : sync_seg3.
Proof.
  intros E gv shs strmp z sp winp s h headp hsh xb nb cb ish ip ilo ilen ic inp v_buf s1 bc.
  intros HY LOK1 M1 HV1 SG.
  pose proof HY as (HIN & NI & H2 & H0 & H4 & Hn).
  pose proof HIN as (ISH & IP & ILO & ILEN & IC & IMAX & ISUB & IBY).
  pose proof H0 as (ZAI & ZAO & ZTIN & ZTOUT & ZDT & ZADL).
  set (L := Live sp winp s h headp hsh xb nb cb) in LOK1.
  assert (Hsp: isptr sp) by (destruct LOK1 as (X & _); exact X).
  sync_seg_start.
  remember (gv _zcalloc) as zca eqn:Hzca. remember (gv _zcfree) as zcf eqn:Hzcf.
    set (got := fst (ssearch (i_have s1) inp)) in *. set (len := snd (ssearch (i_have s1) inp)) in *.
    forward. forward. forward.
    assert (EA: Int.sub (Int.repr (zf_ai z)) (Int.repr len) = Int.repr (Zlength inp - len))
      by (rewrite H2, sub_repr; reflexivity).
    rewrite EA.
    drop_LOCALs [_t'11; _t'4]. subst zca zcf.
    exact (NEXT E gv shs strmp z sp winp s h headp hsh xb nb cb ish ip ilo ilen ic inp v_buf s1 bc HY LOK1 M1 HV1 SG).
Qed.

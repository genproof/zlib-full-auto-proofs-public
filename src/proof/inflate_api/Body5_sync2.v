(* Body of inflateSync, segment 2 (Body5_sync_kit.v): after the bit buffer, the call
   syncsearch(&(state->have), strm->next_in, strm->avail_in). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.Body5_sync_kit.
#[local] Existing Instance Zlib.units.Inflate.CS.

Local Open Scope logic.

Lemma sync_part2 (NEXT: sync_seg3) : sync_seg2.
Proof.
  intros E gv shs strmp z sp winp s h headp hsh xb nb cb ish ip ilo ilen ic inp v_buf s1 bc.
  intros HY LOK1 M1 HV1 SG.
  pose proof HY as (HIN & NI & H2 & H0 & H4 & Hn).
  pose proof HIN as (ISH & IP & ILO & ILEN & IC & IMAX & ISUB & IBY).
  pose proof H0 as (ZAI & ZAO & ZTIN & ZTOUT & ZDT & ZADL).
  assert (Hsp: isptr sp) by (destruct LOK1 as (X & _); exact X).
  sync_seg_start.
  remember (gv _zcalloc) as zca eqn:Hzca. remember (gv _zcfree) as zcf eqn:Hzcf.
  forward. { entailer!. rewrite NI. apply isptr_is_pointer_or_null. destruct ip; try contradiction; exact I. }
  forward.
  assert_PROP (field_compatible t_state (DOT _have) sp) as FCH by entailer!.
  rewrite (field_at_data_at Ews t_state (DOT _have)). unfold in_rep.
  forward_call (Ews, field_address t_state (DOT _have) sp, i_have s1, ish, ip, ilo, ilen, ic, inp).
  { entailer!. rewrite NI, H2. simpl. rewrite field_compatible_field_address by auto. reflexivity. }
  change (data_at Ews tuint) with (data_at Ews (nested_field_type t_state (DOT _have))).
  rewrite <- field_at_data_at.
  drop_LOCALs [_t'13; _t'12]. subst zca zcf.
  exact (NEXT E gv shs strmp z sp winp s h headp hsh xb nb cb ish ip ilo ilen ic inp v_buf s1 bc
    HY LOK1 M1 HV1 SG).
Qed.


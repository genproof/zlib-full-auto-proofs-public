(* RT-H: the inflate side of deflate_roundtrip for inflate_spec6 / inflateGetHeader_spec6 (RTHSpec.v).
   inflateGetHeader_spec6's live part is Spec5's (RTIIface.head_live), so RTIIface.ifacts carries over; the
   spec6 inflate call with a gzip header attached also needs
   - [if6_gzpass]: hd6_ok, i.e. the call passes the whole header (RTHSpec.hpass), before the call;
   - [if6_gzend]: at Z_STREAM_END the header fields extra/name/comment are still the application's
     buffers (h_xp/h_np/h_cp) and the mode is past the header (head_mem6 is then Spec5's head_rep:
     RTHSpec.head_mem6_spec5). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Export Zlib.proof.roundtrip.RTIIface.
Require Export Zlib.proof.roundtrip.RTHSpec.
Import ListNotations.
Local Open Scope Z_scope.

Record ifacts6 : Prop := {
  if6_base : ifacts;
  if6_gzpass : forall wb gh x nm cm D O sp z h headp hsh xb nb cb,
    RF.dfinal [] 2 wb (Some gh) D O -> RF.rhdr_ok gh ->
    DS.gz_extra gh = Some x -> DS.gz_name gh = Some nm -> DS.gz_comment gh = Some cm ->
    Zlength D <= 1048576 -> Zlength O <= 4194304 ->
    h_xp h = true -> h_extra_max h = Zlength x -> Zlength (h_xbuf h) = Zlength x ->
    h_np h = true -> h_name_max h = Zlength nm -> Zlength (h_nbuf h) = Zlength nm ->
    h_cp h = true -> h_comm_max h = Zlength cm -> Zlength (h_cbuf h) = Zlength cm ->
    live_ok (head_live (init_live sp 32) h headp hsh xb nb cb) -> zcall_ok z O D ->
    exists n, hpass 4 n (m_init z (head_live (init_live sp 32) h headp hsh xb nb cb) O);
  if6_gzend : forall wb gh x nm cm D O sp z res h headp hsh xb nb cb,
    RF.dfinal [] 2 wb (Some gh) D O -> RF.rhdr_ok gh ->
    DS.gz_extra gh = Some x -> DS.gz_name gh = Some nm -> DS.gz_comment gh = Some cm ->
    Zlength D <= 1048576 -> Zlength O <= 4194304 ->
    h_xp h = true -> h_extra_max h = Zlength x -> Zlength (h_xbuf h) = Zlength x ->
    h_np h = true -> h_name_max h = Zlength nm -> Zlength (h_nbuf h) = Zlength nm ->
    h_cp h = true -> h_comm_max h = Zlength cm -> Zlength (h_cbuf h) = Zlength cm ->
    live_ok (head_live (init_live sp 32) h headp hsh xb nb cb) -> zcall_ok z O D ->
    run2 4 lenfix_list distfix_list (m_init z (head_live (init_live sp 32) h headp hsh xb nb cb) O) res ->
    r_ret res = Z_STREAM_END ->
    h_xp (m_h (r_m res)) = true /\ h_np (m_h (r_m res)) = true /\ h_cp (m_h (r_m res)) = true /\
    hdr_mode (m_mode (r_m res)) = false
}.

(* Law rj_bad_checksum, main: moves of the compressor's memory between the deflate API's compspecs (DCS.CS) and the
   law's (CS.CS): the caller's fields of the z_stream as field_at's at the law's compspecs (for main's own loads
   and stores), and the whole stream given back as the local's memory at a return. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Zlib.proof.deflate.DSpec.
Require Zlib.proof.deflate.Api_toend.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.harness.clip_streams.CS.
Require Import Zlib.proof.harness.clip_streams.BCKit.
Require Import Zlib.harness.rj_bad_checksum.code.
#[local] Existing Instance CS.CS.
Local Open Scope logic.

(* api_fields (DCS.CS) at the law's compspecs *)
Definition api_fieldsL (strmp nextin : val) (ain tin : Z) (nextout : val) (aout tout : Z) (msgv : val)
    (adler : Z) : mpred :=
  !! (u32_ok ain /\ u64_ok tin /\ u32_ok aout /\ u64_ok tout /\ u64_ok adler) &&
  (field_at Ews t_zsl (DOT _next_in) nextin strmp *
   field_at Ews t_zsl (DOT _avail_in) (vi ain) strmp *
   field_at Ews t_zsl (DOT _total_in) (vl tin) strmp *
   field_at Ews t_zsl (DOT _next_out) nextout strmp *
   field_at Ews t_zsl (DOT _avail_out) (vi aout) strmp *
   field_at Ews t_zsl (DOT _total_out) (vl tout) strmp *
   field_at Ews t_zsl (DOT _msg) msgv strmp *
   field_at Ews t_zsl (DOT _adler) (vl adler) strmp).

Ltac bc_fa_cs := match goal with |- context [@field_at Zlib.proof.deflate.DCS.CS ?sh ?t ?g ?v ?q] =>
  rewrite (@field_at_change_composite Zlib.proof.deflate.DCS.CS CS.CS CC_dcs sh t g v v (JMeq_refl _) eq_refl) end.

Lemma bc_api_fields_L strmp nextin ain tin nextout aout tout msgv adler :
  api_fields strmp nextin ain tin nextout aout tout msgv adler =
  api_fieldsL strmp nextin ain tin nextout aout tout msgv adler.
Proof.
  unfold api_fields, api_fieldsL.
  repeat bc_fa_cs. reflexivity.
Qed.

Lemma bc_api_fields_fold strmp nextin ain tin nextout aout tout msgv adler :
  u32_ok ain -> u64_ok tin -> u32_ok aout -> u64_ok tout -> u64_ok adler ->
  field_at Ews t_zsl (DOT _next_in) nextin strmp *
  field_at Ews t_zsl (DOT _avail_in) (vi ain) strmp *
  field_at Ews t_zsl (DOT _total_in) (vl tin) strmp *
  field_at Ews t_zsl (DOT _next_out) nextout strmp *
  field_at Ews t_zsl (DOT _avail_out) (vi aout) strmp *
  field_at Ews t_zsl (DOT _total_out) (vl tout) strmp *
  field_at Ews t_zsl (DOT _msg) msgv strmp *
  field_at Ews t_zsl (DOT _adler) (vl adler) strmp
  |-- api_fields strmp nextin ain tin nextout aout tout msgv adler.
Proof. intros. rewrite bc_api_fields_L. unfold api_fieldsL. entailer!. Qed.

(* a whole struct z_stream at either compspecs *)
Lemma bc_strm_data_at__cs sh q :
  @data_at_ Zlib.proof.deflate.DCS.CS sh t_strm q = @data_at_ CS.CS sh t_zsl q.
Proof.
  unfold data_at_. apply equal_f.
  apply (@data_at_change_composite _ _ CC_dcs); [apply JMeq_refl | reflexivity].
Qed.

(* the compressor, whatever its state, back to the local's memory *)
Lemma bc_strm_ret os vc ghp gv nin ai tin nout ao tout msgv adler :
  dstream 2 os vc ghp gv * api_fields vc nin ai tin nout ao tout msgv adler * bc_srest vc
  |-- data_at_ Tsh t_zsl vc * TT.
Proof.
  unfold bc_srest.
  sep_apply (BoundKit.dstream_data_at_ os vc ghp gv nin ai tin nout ao tout msgv adler
               Zlib.proof.deflate.Api_toend.dstream_to_end).
  rewrite bc_strm_data_at__cs.
  rewrite <- (data_at__share_join Ews (Share.comp Ews) Tsh) by apply join_comp_Tsh.
  cancel.
Qed.

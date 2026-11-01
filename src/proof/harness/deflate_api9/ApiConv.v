(* Law deflate_api: moves between the shared specifications' compspecs (DCS.CS) and the law's (ApiCS.CS), for
   the harness's own accesses: the caller's fields of the z_stream (api_fields <-> api_fieldsL), byte arrays and
   their malloc tokens. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.harness.deflate_api.ApiCS Zlib.proof.harness.deflate_api9.RunSpec.
Require Import Zlib.harness.x_deflate_api.code.
#[local] Existing Instance ApiCS.CS.
Local Open Scope logic.

(* api_fields (DCS.CS) at the law's compspecs *)
Definition api_fieldsL (strmp nextin : val) (ain tin : Z) (nextout : val) (aout tout : Z) (msgv : val)
    (adler : Z) : mpred :=
  !! (u32_ok ain /\ u64_ok tin /\ u32_ok aout /\ u64_ok tout /\ u64_ok adler) &&
  (field_at Ews t_strmL (DOT _next_in) nextin strmp *
   field_at Ews t_strmL (DOT _avail_in) (vi ain) strmp *
   field_at Ews t_strmL (DOT _total_in) (vl tin) strmp *
   field_at Ews t_strmL (DOT _next_out) nextout strmp *
   field_at Ews t_strmL (DOT _avail_out) (vi aout) strmp *
   field_at Ews t_strmL (DOT _total_out) (vl tout) strmp *
   field_at Ews t_strmL (DOT _msg) msgv strmp *
   field_at Ews t_strmL (DOT _adler) (vl adler) strmp).

Ltac fa_cs := match goal with |- context [@field_at DCS.CS ?sh ?t ?g ?v ?q] =>
  rewrite (@field_at_change_composite DCS.CS CS CC_dcs sh t g v v (JMeq_refl _) eq_refl) end.

Lemma api_fields_L strmp nextin ain tin nextout aout tout msgv adler :
  api_fields strmp nextin ain tin nextout aout tout msgv adler =
  api_fieldsL strmp nextin ain tin nextout aout tout msgv adler.
Proof.
  unfold api_fields, api_fieldsL.
  repeat fa_cs. reflexivity.
Qed.

Lemma tok_tuchar_cs sh n q :
  @malloc_token DCS.CS sh (tarray tuchar n) q = @malloc_token CS sh (tarray tuchar n) q.
Proof. apply equal_f. apply (@malloc_token_change_composite _ _ CC_dcs). reflexivity. Qed.

Lemma bytes_cs (cs1 cs2 : compspecs) sh n (v : list val) q :
  @data_at cs1 sh (tarray tuchar n) v q = @data_at cs2 sh (tarray tuchar n) v q.
Proof. apply data_at_tuchar_cs. Qed.

(* a whole struct z_stream at either compspecs *)
Lemma strm_data_at_cs sh (v : reptype t_strmL) q :
  @data_at DCS.CS sh t_strm v q = @data_at CS sh t_strmL v q.
Proof. apply equal_f. apply (@data_at_change_composite _ _ CC_dcs); [apply JMeq_refl | reflexivity]. Qed.

Lemma strm_data_at__cs sh q :
  @data_at_ DCS.CS sh t_strm q = @data_at_ CS sh t_strmL q.
Proof. unfold data_at_. apply strm_data_at_cs. Qed.

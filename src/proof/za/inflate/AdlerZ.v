(* Storing into strm->adler under the adler cell (ZAV.v): the representations of the allocator-generic port
   hold strm->adler as [adler_val adler].  A body that writes the model's value y into the member (inflateResetKeep
   when state->wrap <> 0) ends with the member [Vlong y]; with [av_undef = true] the representation is Vundef,
   any contents, which the written value satisfies. *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate.Rep.
Require Import Zlib.proof.za.inflate.ZAV.
#[local] Existing Instance Zlib.units.Inflate.CS.

Section Adler.
Context {ZAV : adler_cell}.

(* a z_stream whose adler member holds v, the model's value y when the cell is defined, is a z_stream whose
   adler member is the cell's [adler_val y] *)
Lemma data_at_adler_val sh (p: val) a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a14 (v: val) (y: Z) :
  (av_undef = false -> v = Vlong (Int64.repr y)) ->
  data_at sh t_strm (a1, (a2, (a3, (a4, (a5, (a6, (a7, (a8, (a9, (a10, (a11, (a12, (v, a14))))))))))))) p
  |-- data_at sh t_strm (a1, (a2, (a3, (a4, (a5, (a6, (a7, (a8, (a9, (a10, (a11, (a12,
        (adler_val y, a14))))))))))))) p.
Proof.
  intros Hv. unfold adler_val. destruct av_undef eqn:E; [ | rewrite Hv by reflexivity; apply derives_refl].
  (* take the member out (the ramification of a store), weaken it to any contents, put it back *)
  unfold data_at.
  eapply derives_trans;
    [eapply (nested_field_ramif' sh t_strm [] (DOT _adler)); [apply JMeq_refl | split; [reflexivity | cbv; tauto]] | ].
  eapply derives_trans; [apply sepcon_derives; [apply field_at_field_at_ | apply derives_refl] | ].
  unfold field_at_.
  eapply derives_trans; [apply sepcon_derives; [apply derives_refl | ] | ].
  { apply (allp_left _ (default_val _)); apply (allp_left _ (default_val _)).
    rewrite prop_imp by apply JMeq_refl. apply derives_refl. }
  eapply derives_trans; [apply modus_ponens_wand | ].
  apply derives_refl'. f_equal.
Qed.

End Adler.

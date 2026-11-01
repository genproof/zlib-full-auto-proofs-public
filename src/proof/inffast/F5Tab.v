(* inflate_fast (BodyF5.v): a table entry apart (F5Kit.tab_focus_stmt). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inffast.code.
Require Import Zlib.proof.inffast.F5Kit.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* element j of an array apart, with the wand back *)
Lemma f5_arr_focus: forall {cs: compspecs} sh t n (al: list (reptype t)) p j,
  0 <= j < n -> Zlength al = n ->
  data_at sh (tarray t n) al p |--
    data_at sh t (Znth j al) (offset_val (sizeof t * j) p) *
    (data_at sh t (Znth j al) (offset_val (sizeof t * j) p) -* data_at sh (tarray t n) al p).
Proof.
  intros cs sh t n al p j Hj Hl.
  rewrite (wand_slice_array j (j+1) n sh t al p) by lia.
  normalize.
  rewrite arr_field_address0 by (auto; lia).
  rewrite sublist_len_1 by lia.
  replace (j + 1 - j) with 1 by lia.
  rewrite (data_at_singleton_array_eq sh t (Znth j al) [Znth j al]) by auto.
  apply sepcon_derives; [apply derives_refl|].
  apply wand_sepcon_adjoint.
  rewrite sepcon_comm. apply derives_refl.
Qed.

(* the same for a table of codes *)
Lemma f5_ent_focus: forall sh n (l: list entry) p j,
  0 <= j < n -> Zlength l = n ->
  data_at sh (tarray t_code n) (map ent l) p |--
    data_at sh t_code (ent (Znth j l)) (offset_val ((4 * j)%Z) p) *
    (data_at sh t_code (ent (Znth j l)) (offset_val ((4 * j)%Z) p) -* data_at sh (tarray t_code n) (map ent l) p).
Proof.
  intros sh n l p j Hj Hl.
  rewrite <- (Znth_map j ent l) by lia.
  replace ((4 * j)%Z) with ((sizeof t_code * j)%Z) by reflexivity.
  pose proof (f5_arr_focus sh t_code n (map ent l) p j) as H.
  apply H; [lia | rewrite Zlength_map; exact Hl].
Qed.

(* framing a focus *)
Lemma f5_focus_frame: forall (B R e: mpred), B |-- e * (e -* B) -> B * R |-- e * (e -* B * R).
Proof.
  intros B R e H.
  eapply derives_trans; [apply sepcon_derives; [exact H | apply derives_refl]|].
  rewrite sepcon_assoc. apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint.
  rewrite sepcon_assoc, (sepcon_comm R e), <- sepcon_assoc.
  apply sepcon_derives; [rewrite sepcon_comm; apply modus_ponens_wand | apply derives_refl].
Qed.

Lemma f5_focus_prop: forall (P: Prop) (B e: mpred), B |-- !! P -> (P -> B |-- e * (e -* B)) -> B |-- e * (e -* B).
Proof.
  intros P B e H1 H2.
  eapply derives_trans; [apply andp_right; [exact H1 | apply derives_refl]|].
  apply derives_extract_prop; intros HP. apply H2; auto.
Qed.

(* &state->codes[k] *)
Lemma f5_codes_at: forall sp k, field_compatible t_state (DOT _codes) sp -> 0 <= k <= ENOUGH_CODES ->
  codes_at sp k = offset_val ((4 * k)%Z) (field_address t_state (DOT _codes) sp).
Proof.
  intros sp k H Hk. unfold codes_at. unfold ENOUGH_CODES in Hk.
  assert (H0: field_compatible0 t_state (DOT _codes SUB k) sp).
  { eapply field_compatible0_cons_Tarray; [reflexivity | exact H | lia]. }
  rewrite field_address0_offset by exact H0. rewrite field_address_offset by exact H.
  simpl. rewrite offset_offset_val. f_equal.
Qed.

Lemma f5_lenfix_len: Zlength lenfix_list = 512.
Proof. vm_compute. reflexivity. Qed.

Lemma f5_distfix_len: Zlength distfix_list = 32.
Proof. vm_compute. reflexivity. Qed.

Lemma f5_tab_focus : tab_focus_stmt.
Proof.
  intros F s t j Ht Hc Hj.
  unfold tab_mem.
  destruct t as [| |k]; simpl in Hj, Ht; unfold tab_sh, tab_entry, entry_ptr, tref_val.
  - (* lenfix *)
    rewrite (sepcon_comm (field_at _ _ _ _ _) (data_at _ _ _ (f_gv F g_lenfix))).
    rewrite sepcon_assoc. apply f5_focus_frame.
    apply f5_ent_focus; [lia | apply f5_lenfix_len].
  - (* distfix *)
    rewrite sepcon_comm. apply f5_focus_frame.
    apply f5_ent_focus; [lia | apply f5_distfix_len].
  - (* state->codes *)
    rewrite sepcon_assoc. apply f5_focus_frame.
    apply (f5_focus_prop (field_compatible t_state (DOT _codes) (f_sp F))).
    { entailer!. }
    intros Hfc.
    rewrite (f5_codes_at (f_sp F) k Hfc) by (unfold ENOUGH_CODES in *; lia).
    rewrite offset_offset_val. replace ((4 * k + 4 * j)%Z) with ((4 * (k + j))%Z) by lia.
    rewrite field_at_data_at.
    apply f5_ent_focus; [unfold ENOUGH_CODES in *; lia | exact Hc].
Qed.

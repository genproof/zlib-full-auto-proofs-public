(* The laws rt_dictionary and api_dict_id: the zlib stream O that deflate wrote with the dictionary dict
   (DWFacts.dfinal_dict) as a decode context of any length (Decode7.dctx_ok7).

   O is [CMF; FLG] ++ DICTID ++ T (T the deflate bytes and the Adler-32 trailer).  Its context [dw_ctx] (DWISet.v)
   has the history dict and Format's header (FLEVEL 0, which may differ from O's FLG; inflate reads the header
   only in the first call): from byte 6 on, the context's input and O agree, and the inflate calls after the
   dictionary start at byte 6. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.rfc1951.Decode7.
Require Import Zlib.proof.harness.dictionary_w.DWFacts.
Require Import Zlib.proof.harness.clip_streams.IFacts.
Require Import Zlib.proof.roundtrip.RTIZDictDefs.
Require Import Zlib.proof.roundtrip.RTIZDictKit.
Require Import Zlib.proof.roundtrip.RTIZDict.
Require Import Zlib.proof.harness.dictionary_w.DWISet.
Import ListNotations.
Local Open Scope Z_scope.

(* what the theory keeps of the context G of O *)
Definition dw_gok (wbits: Z) (dict D O: list Z) (G: dctx) : Prop :=
  dctx_ok7 G /\ dc_hist G = dict /\ dc_iw G = iwb wbits /\ 9 <= iwb wbits <= 15 /\
  full G = dict ++ D /\ slen G = Zlength O /\ Zlength (dc_src G) = Zlength O /\
  sublist 6 (Zlength O) (dc_src G) = sublist 6 (Zlength O) O /\ 6 < Zlength O.

(* deflateInit2's windowBits 8..15: deflate's window bits are inflateInit2's (8 read as 9) *)
Lemma dwi_rwbe wbits : 8 <= wbits <= 15 -> RTDIface.rwbe wbits = iwb wbits /\ 9 <= iwb wbits <= 15.
Proof.
  intros H. unfold RTDIface.rwbe, RTDIface.rwb_of, iwb.
  replace (wbits <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (wbits >? 15) with false by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_ge; lia).
  destruct (Z.eqb_spec wbits 8); lia.
Qed.

Lemma dwi_stream wbits dict D O :
  dfinal_dict wbits dict D O -> dict <> [] -> Zlength O <= 2 ^ 64 - 1 ->
  exists flg T, RF.zflg_ok (iwb wbits) true flg /\
    O = [RF.zcmf (iwb wbits); flg] ++ be_bytes (Zlib.proof.adler32.Model.ref_adler32 1 dict) 4 ++ T /\
    4 <= Zlength T /\
    exists bs, wf (2 ^ iwb wbits) dict bs /\ dw_gok wbits dict D O (dw_ctx (iwb wbits) dict bs).
Proof.
  intros (Hw8 & DF) Hne HO64.
  destruct (dwi_rwbe wbits Hw8) as (EW & Hwb).
  rewrite EW in DF. set (wb := iwb wbits) in *.
  destruct DF as (_ & bs & WF & Hdata & DW).
  destruct DW as (_ & flg & FL & HOeq).
  assert (EM : negb (match dict with [] => true | _ => false end) = true) by (destruct dict; [congruence|reflexivity]).
  assert (EB : match dict with [] => [] | _ => be_bytes (Zlib.proof.adler32.Model.ref_adler32 1 dict) 4 end =
               be_bytes (Zlib.proof.adler32.Model.ref_adler32 1 dict) 4) by (destruct dict; [congruence|reflexivity]).
  rewrite EM in FL. rewrite EB in HOeq. clear EM EB.
  set (id := Zlib.proof.adler32.Model.ref_adler32 1 dict) in *.
  set (T := deflate_bytes bs ++ be_bytes (Zlib.proof.adler32.Model.ref_adler32 1 D) 4) in *.
  assert (HT : 4 <= Zlength T).
  { unfold T. rewrite Zlength_app. unfold be_bytes, le_bytes. rewrite Zlength_rev, Zlength_map.
    pose proof (Zlength_nonneg (deflate_bytes bs)). cbn. lia. }
  assert (HBE : Zlength (be_bytes id 4) = 4) by (unfold be_bytes, le_bytes; rewrite Zlength_rev, Zlength_map; reflexivity).
  assert (HOL : Zlength O = 6 + Zlength T).
  { rewrite HOeq, !Zlength_app, HBE. cbn. lia. }
  exists flg, T. split; [exact FL|]. split; [exact HOeq|]. split; [exact HT|].
  set (G := dw_ctx wb dict bs).
  set (src := stream_bytes (zd_w dict wb) dict bs).
  assert (Esrc : src = zlib_hdr wb 0 true ++ be_bytes id 4 ++ T).
  { unfold src, stream_bytes, zd_w. cbv zeta. rewrite Hdata. reflexivity. }
  assert (HSL : Zlength src = 6 + Zlength T).
  { rewrite Esrc, !Zlength_app, HBE, rtzk_len_hdr. lia. }
  exists bs. split; [exact WF|]. change (dw_ctx wb dict bs) with G.
  assert (Hslen : slen G = 6 + Zlength T) by (unfold slen; exact HSL).
  unfold dw_gok. split; [|split; [reflexivity|split; [reflexivity|split; [exact Hwb|]]]].
  - unfold dctx_ok7, G, dw_ctx. cbn [dc_w dc_wb dc_hist dc_bs dc_iw dc_src]. fold src.
    split; [unfold stream_ok, zd_w; cbn; split; [lia|]; split; [split; [lia|split; [lia|reflexivity]]|];
            split; [reflexivity|exact WF]|].
    split; [unfold accepts; cbn; left; reflexivity|].
    split; [intros h E; discriminate E|].
    split; [intros wb' fl did E; inversion E; right; reflexivity|].
    split; [unfold slen; cbn [dc_w dc_hist dc_bs]; fold src; apply Z.le_refl|].
    split; [lia|]. split.
    + rewrite Esrc. apply Forall_app; split; [apply rtzk_hdr; lia|].
      apply Forall_app; split; [apply rtzk_be_bytes|]. unfold T.
      apply Forall_app; split; [unfold deflate_bytes; apply rtzk_pack | apply rtzk_be_bytes].
    + unfold slen; cbn [dc_w dc_hist dc_bs]; fold src. apply sublist_same; reflexivity.
  - split; [unfold full, G, dw_ctx; cbn [dc_hist dc_bs]; rewrite rtzk_expand_data, Hdata; reflexivity|].
    split; [lia|]. split; [change (dc_src G) with src; lia|]. split; [|lia].
    change (dc_src G) with src. rewrite HOL, <- HSL.
    rewrite Esrc at 2. rewrite HOeq.
    pose proof (rtzk_len_hdr wb 0 true) as L2.
    rewrite (sublist_app2 6 _ (zlib_hdr wb 0 true)) by (rewrite L2; lia).
    rewrite (sublist_app2 6 _ [RF.zcmf wb; flg]) by (cbn; lia).
    rewrite L2. reflexivity.
Qed.

(* the input of a call at pos >= 6 is the same in O and in the context *)
Lemma dwi_inp wbits dict D O G pos inp :
  dw_gok wbits dict D O G -> 6 <= pos -> pos + Zlength inp <= Zlength O ->
  inp = sublist pos (pos + Zlength inp) O -> inp = sublist pos (pos + Zlength inp) (dc_src G).
Proof.
  intros (_ & _ & _ & _ & _ & _ & LS & SB & _) P6 PL E.
  rewrite E at 1.
  assert (A: forall l : list Z, Zlength l = Zlength O ->
             sublist pos (pos + Zlength inp) l = sublist (pos - 6) (pos + Zlength inp - 6) (sublist 6 (Zlength O) l)).
  { intros l Hl. pose proof (Zlength_nonneg inp). rewrite sublist_sublist by lia. f_equal; lia. }
  rewrite (A O eq_refl), (A (dc_src G) LS), SB. reflexivity.
Qed.

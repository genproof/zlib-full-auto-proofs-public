(* Law rt_gzip_header on the round-2 harness, main's body around deflateSetHeader: the memory lemmas of segment 3
   (G2MainSeg3.v) and of the paths of later segments that give the compressor and head back.  Round 1's
   MainSeg4Kit.v adapted to G2MainKit: head as deflateSetHeader's gzh_at and back, the compressor's caller fields
   (st_raw with ranges is st_fields), the compressor back as the local's memory. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.harness.rt_gzip_header.CS.
Require Import Zlib.proof.harness.rt_gzip_header.G2MainDefs.
Require Import Zlib.proof.deflate.Rep.
Require Import Zlib.proof.deflate.DSpec.
Require Zlib.proof.deflate.DSpec9.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Zlib.proof.deflate.Api_toend.
Require Import Zlib.proof.harness.rt_gzip_header.G2DFacts.
Require Import Zlib.proof.harness.rt_gzip_header.G2MainKit.
Require Import Zlib.harness.rt_gzip_header.code.
#[local] Existing Instance Zlib.proof.harness.rt_gzip_header.CS.CS.
Local Open Scope logic.

(** ** The header main gives deflateSetHeader *)

Lemma nz_bytes0 (l : list Z) : nzbytes l -> Forall (fun x => 0 <= x < 256) (l ++ [0]).
Proof.
  intros H. apply Forall_app. split; [ | constructor; [lia | constructor]].
  eapply Forall_impl; [ | exact H]. intros; simpl in *; lia.
Qed.

(* the header main builds is one gzh_at can hold *)
Lemma gh_of_gzh (g : gsetup) : gs_ok g -> gzh_ok (gh_of g).
Proof.
  intros (Hxl & _ & _ & _ & Htx & Htm & Hos & Hhc & _).
  unfold gzh_ok, gh_of, rs32 in *; cbn. rep_lia.
Qed.

(** ** head's memory as deflate.c sees it *)

(* the objects at main's compspecs are deflate's objects *)
Lemma cobj_obj (q : val) (l : list Z) : cobj q l = BoundKit.obj q l.
Proof.
  unfold cobj, BoundKit.obj.
  erewrite (@malloc_token_change_composite DCS.CS CS CC_dcs) by reflexivity.
  erewrite (@data_at_change_composite DCS.CS CS CC_dcs); [ reflexivity | apply JMeq_refl | reflexivity ].
Qed.

(* what the selected object of head does not hand to deflate: its token, or the whole object if the field
   is absent *)
Definition sel_rest (g : gsetup) (m : Z) (q : val) (l : list Z) : mpred :=
  if has g m then BoundKit.obj_rest q l else cobj q l.

Lemma cobj_sel (g : gsetup) (m : Z) (q : val) (l : list Z) :
  Forall (fun x => 0 <= x < 256) l -> cobj q l = opt_obj Ews (selo g m l) (selp g m q) * sel_rest g m q l.
Proof.
  intros HB. unfold selo, selp, sel_rest. destruct (has g m).
  - rewrite cobj_obj. apply BoundKit.obj_opt_obj. exact HB.
  - unfold opt_obj. apply pred_ext; entailer!.
Qed.

(* what deflate does not hold of head's objects, and the copies *)
Definition hrest (g : gsetup) : mpred :=
  sel_rest g 1 (g_xp g) (g_xf g) * sel_rest g 2 (g_np g) (g_nm g ++ [0]) * sel_rest g 4 (g_cp g) (g_cm g ++ [0]) *
  hcopies g.

(* head's Ews part at deflate's compspecs *)
Definition hval_d (g : gsetup) : @reptype DCS.CS t_gzh :=
  (vi (g_text g), (vl (g_time g), (Vundef, (vi (g_os g), (selp g 1 (g_xp g), (vi (g_xl g), (Vundef,
   (selp g 2 (g_np g), (Vundef, (selp g 4 (g_cp g), (Vundef, (vi (g_hcrc g), Vundef)))))))))))).

Lemma head_cs (g : gsetup) (vh : val) : data_at Ews t_g (hvals g) vh = @data_at DCS.CS Ews t_gzh (hval_d g) vh.
Proof.
  erewrite (@data_at_change_composite DCS.CS CS CC_dcs Ews t_gzh (hval_d g));
    [ reflexivity | apply JMeq_refl | reflexivity ].
Qed.

(* head's Ews part and its three objects hold the header gh_of g (the absent objects stay with main) *)
Lemma head_to_gzh (g : gsetup) (vh : val) : gs_ok g ->
  @data_at DCS.CS Ews t_gzh (hval_d g) vh * hobjs g
  |-- gzh_at Ews (gh_of g) vh (selp g 1 (g_xp g)) (selp g 2 (g_np g)) (selp g 4 (g_cp g)) *
      BoundKit.gzh_pad vh * hrest g.
Proof.
  intros OK. pose proof OK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Bx & _ & Bn & _ & Bc & _).
  unfold hobjs, hrest.
  rewrite (cobj_sel g 1 (g_xp g) (g_xf g) Bx), (cobj_sel g 2 (g_np g) _ (nz_bytes0 _ Bn)),
    (cobj_sel g 4 (g_cp g) _ (nz_bytes0 _ Bc)).
  sep_apply (BoundKit.gzh_of_stores (gh_of g) vh (selp g 1 (g_xp g)) (selp g 2 (g_np g)) (selp g 4 (g_cp g))
    Vundef Vundef Vundef Vundef Vundef (gh_of_gzh g OK)).
  cancel.
Qed.

(* and back, whatever deflate left in the fields gzh_at does not fix (main never wrote them) *)
Lemma gzh_to_head (g : gsetup) (vh : val) : gs_ok g ->
  gzh_at Ews (gh_of g) vh (selp g 1 (g_xp g)) (selp g 2 (g_np g)) (selp g 4 (g_cp g)) *
  BoundKit.gzh_pad vh * hrest g
  |-- @data_at DCS.CS Ews t_gzh (hval_d g) vh * hobjs g.
Proof.
  intros OK. pose proof OK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Bx & _ & Bn & _ & Bc & _).
  unfold hobjs, hrest.
  rewrite (cobj_sel g 1 (g_xp g) (g_xf g) Bx), (cobj_sel g 2 (g_np g) _ (nz_bytes0 _ Bn)),
    (cobj_sel g 4 (g_cp g) _ (nz_bytes0 _ Bc)).
  unfold gzh_at, BoundKit.gzh_pad. Intros v1 v2 v3 v4 v5.
  unfold_data_at (@data_at DCS.CS _ _ _ vh). unfold hval_d. cbn [fst snd].
  cancel. apply derives_refl.
Qed.

(* head while deflate holds it: the complement of Ews of the struct, its padding and what deflate does not hold
   of the three objects *)
Definition Hr_of (g : gsetup) (vh : val) : mpred :=
  data_at BoundKit.Ecomp t_g (hvals g) vh * BoundKit.gzh_pad vh * hrest g.

Definition hx_of (g : gsetup) : share * val * val * val :=
  (Ews, selp g 1 (g_xp g), selp g 2 (g_np g), selp g 4 (g_cp g)).

(* head (Tsh) and its objects: what deflateSetHeader takes, and the rest *)
Lemma head_open (g : gsetup) (vh : val) : gs_ok g ->
  data_at Tsh t_g (hvals g) vh * hobjs g
  |-- gzh_at Ews (gh_of g) vh (selp g 1 (g_xp g)) (selp g 2 (g_np g)) (selp g 4 (g_cp g)) * Hr_of g vh.
Proof.
  intros OK. rewrite <- (data_at_share_join Ews BoundKit.Ecomp Tsh _ _ _ BoundKit.join_Ews_Ecomp).
  rewrite head_cs. unfold Hr_of. sep_apply (head_to_gzh g vh OK). cancel.
Qed.

(* A32's hclose for these: head comes back while the state keeps the header *)
Lemma head_close (g : gsetup) (vh : val) (s : dstate) : gs_ok g -> d_gzhead s = Some (gh_of g) ->
  hclose vh g s (hx_of g) (Hr_of g vh).
Proof.
  intros OK E s' E'. unfold hdr_at, hx_of. rewrite E', E.
  unfold Hr_of. sep_apply (gzh_to_head g vh OK). rewrite <- head_cs.
  rewrite <- (data_at_share_join Ews BoundKit.Ecomp Tsh _ _ _ BoundKit.join_Ews_Ecomp). cancel.
Qed.

(** ** The compressor's caller fields *)

(* right after deflateInit2_ (st_raw), with the ranges the loop invariant gives (G2DFacts.gd_range), they are
   the fields the specifications of deflate.c take (st_fields) *)
Lemma raw_fields (vc : val) (st : dside) :
  0 <= st_tin st <= max_u64 -> 0 <= st_tout st <= max_u64 -> 0 <= st_adler st <= max_u64 ->
  st_raw vc st |-- st_fields vc st.
Proof.
  intros. unfold st_raw, st_fields, api_fields, DSpec9.reset_fields, u32_ok, u64_ok, max_u64 in *.
  entailer!.
Qed.

(* deflateSetHeader and deflateBound_z take strm->next_in apart from the caller's other fields *)
Definition af_rest (sp : val) (ain tin : Z) (nout : val) (aout tout : Z) (msgv : val) (adler : Z) : mpred :=
  !! (u32_ok ain /\ u64_ok tin /\ u32_ok aout /\ u64_ok tout /\ u64_ok adler) &&
  (@field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._avail_in) (vi ain) sp *
   @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._total_in) (vl tin) sp *
   @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._next_out) nout sp *
   @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._avail_out) (vi aout) sp *
   @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._total_out) (vl tout) sp *
   @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._msg) msgv sp *
   @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._adler) (vl adler) sp).

Lemma af_split (sp nin : val) (ain tin : Z) (nout : val) (aout tout : Z) (msgv : val) (adler : Z) :
  api_fields sp nin ain tin nout aout tout msgv adler =
  @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._next_in) nin sp * af_rest sp ain tin nout aout tout msgv adler.
Proof.
  unfold api_fields, af_rest. apply pred_ext; entailer!.
Qed.

Lemma af_join (sp nin : val) (ain tin : Z) (nout : val) (aout tout : Z) (msgv : val) (adler : Z) :
  @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._next_in) nin sp * af_rest sp ain tin nout aout tout msgv adler
  |-- api_fields sp nin ain tin nout aout tout msgv adler.
Proof. rewrite af_split. apply derives_refl. Qed.

(* the compressor, whatever its state, gives back the local's memory *)
Lemma comp_back (vc : val) (gv : globals) (os : option dstate) (ghp nin : val) (ain tin : Z) (nout : val)
    (aout tout : Z) (msgv : val) (adler : Z) :
  dstream 2 os vc ghp gv * api_fields vc nin ain tin nout aout tout msgv adler * srest vc
  |-- data_at_ Tsh t_z vc * TT.
Proof.
  unfold srest.
  sep_apply (BoundKit.dstream_data_at_ os vc ghp gv nin ain tin nout aout tout msgv adler
               Zlib.proof.deflate.Api_toend.dstream_to_end).
  rewrite (@data_at__change_composite DCS.CS CS CC_dcs Ews Zlib.proof.deflate.Rep.t_strm) by reflexivity.
  rewrite (BoundKit.data_at__Tsh_split t_z vc). cancel.
Qed.

(* forward_call hands back the callee's next_in field at main's compspecs *)
Lemma ni_cs (v p : val) :
  @field_at CS Ews t_strm (DOT Zlib.deflate.code._next_in) v p =
  @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._next_in) v p.
Proof.
  erewrite (@field_at_change_composite DCS.CS CS CC_dcs Ews t_strm (DOT Zlib.deflate.code._next_in) v);
    [ reflexivity | apply JMeq_refl | reflexivity ].
Qed.

Lemma gz_set (s : dstate) (x : option DS.gzh) : d_gzhead (set_d_gzhead s x) = x.
Proof. reflexivity. Qed.

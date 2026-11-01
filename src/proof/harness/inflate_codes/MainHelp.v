(* Law inflate_codes, main (Main.v): helpers of the init part (stream_defaults, inflateInit2_ on &s or Z_NULL,
   the version string) and of the loop (the stream at the law's compspecs). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessRef Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.inflate_common.HarnessLib.
Require Import Zlib.proof.harness.inflate_codes.LawCS Zlib.proof.harness.inflate_codes.Globals
               Zlib.proof.harness.inflate_codes.Facts Zlib.proof.harness.inflate_codes.MainKit.
Require Import Zlib.harness.x_inflate_codes.code.
Require Import Zlib.proof.crc32.Spec.
Local Open Scope logic.

Definition strm_tuple : Type :=
  (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * val)))))))))))))%type.

Lemma strm_cs sh (v: strm_tuple) q:
  @data_at Zlib.units.Inflate.CS sh Rep.t_strm v q = @data_at CS sh (Tstruct _z_stream_s noattr) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_inflate); [apply JMeq_refl | reflexivity]. Qed.

Definition strm_undef : strm_tuple :=
  (Vundef, (Vundef, (Vundef, (Vundef, (Vundef, (Vundef, (Vundef, (Vundef,
   (Vundef, (Vundef, (Vundef, (Vundef, (Vundef, Vundef))))))))))))).

Lemma strm_undef_cs sh q:
  @data_at_ CS sh (Tstruct _z_stream_s noattr) q = @data_at Zlib.units.Inflate.CS sh Rep.t_strm strm_undef q.
Proof. unfold data_at_. rewrite strm_cs. reflexivity. Qed.

(* any stream contents (at the inflate unit's CS) give back the local variable's memory *)
Lemma strm_to_undef sh (v: strm_tuple) q:
  @data_at Zlib.units.Inflate.CS sh Rep.t_strm v q |-- @data_at_ CS sh (Tstruct _z_stream_s noattr) q.
Proof. rewrite strm_undef_cs. apply (@data_at_data_at_ Zlib.units.Inflate.CS). Qed.

Lemma tschar_cs sh n (v: list val) q:
  @data_at Zlib.units.Inflate.CS sh (tarray tschar n) v q = @data_at CS sh (tarray tschar n) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_inflate); [apply JMeq_refl | reflexivity]. Qed.

(* the version strings *)
Definition other_vals (vbyte: Z) : list val := [Vint (Int.sign_ext 8 (Int.repr vbyte)); Vint (Int.repr 0)].
Definition hver_vals : list val := map (fun c => Vint (Int.repr c)) [49; 46; 51; 46; 50; 0].

Definition ver_vc (vsel vbyte: Z) : list val := if zeq vsel 0 then other_vals vbyte else hver_vals.
Definition ver_p (gv: globals) (vo: val) (vsel: Z) : val :=
  if zeq vsel 0 then vo else gv ___stringlit_x_inflate_codes_1.
Definition ver_sh (vsel: Z) : share := if zeq vsel 0 then Tsh else Ers.
Definition ver_c (vsel vbyte: Z) : Z := if zeq vsel 0 then Int.signed (Int.sign_ext 8 (Int.repr vbyte)) else 49.
Definition ver_rest (gv: globals) (vo: val) (vsel vbyte: Z) : mpred :=
  if zeq vsel 0 then hversion_lit gv else data_at Tsh (tarray tschar 2) (other_vals vbyte) vo.

Lemma ver_split gv vo vsel vbyte:
  data_at Tsh (tarray tschar 2) (other_vals vbyte) vo * hversion_lit gv =
  data_at (ver_sh vsel) (tarray tschar (Zlength (ver_vc vsel vbyte))) (ver_vc vsel vbyte) (ver_p gv vo vsel) *
  ver_rest gv vo vsel vbyte.
Proof.
  unfold ver_sh, ver_vc, ver_p, ver_rest, hversion_lit. destruct (zeq vsel 0); [reflexivity | ].
  rewrite sepcon_comm. reflexivity.
Qed.

Lemma ver_c_range vsel vbyte: -128 <= ver_c vsel vbyte <= 127.
Proof.
  unfold ver_c. destruct (zeq vsel 0); [ | lia].
  assert (R: - two_p (8 - 1) <= Int.signed (Int.sign_ext 8 (Int.repr vbyte)) < two_p (8 - 1))
    by (apply Int.sign_ext_range; cbv; split; reflexivity).
  change (two_p (8 - 1)) with 128 in R. lia.
Qed.

Lemma ver_vc_0 vsel vbyte: Znth 0 (ver_vc vsel vbyte) = Vint (Int.repr (ver_c vsel vbyte)).
Proof.
  unfold ver_vc, ver_c. destruct (zeq vsel 0); [ | reflexivity].
  simpl. rewrite Int.repr_signed. reflexivity.
Qed.

Lemma ver_vc_len vsel vbyte: 1 <= Zlength (ver_vc vsel vbyte) <= 6.
Proof. unfold ver_vc. destruct (zeq vsel 0); simpl; reflexivity || (split; discriminate). Qed.

(* the stream argument of inflateInit2_: &s, or Z_NULL with s kept aside *)
Definition strm_arg (vs: val) (nullstrm: Z) : val := if zeq nullstrm 0 then nullval else vs.

Lemma strm_split gv vs nullstrm r msgv stv opq:
  isptr vs ->
  raw_strm gv Tsh vs r msgv stv nullval nullval opq =
  (if eq_dec (strm_arg vs nullstrm) nullval then emp
   else raw_strm gv Tsh (strm_arg vs nullstrm) r msgv stv nullval nullval opq) *
  (if eq_dec (strm_arg vs nullstrm) nullval then raw_strm gv Tsh vs r msgv stv nullval nullval opq else emp).
Proof.
  intros P. unfold strm_arg. destruct (zeq nullstrm 0).
  - rewrite if_true by auto. rewrite emp_sepcon. reflexivity.
  - destruct (eq_dec vs nullval); [subst; contradiction | ]. rewrite sepcon_emp. reflexivity.
Qed.

(* a stream left by a failed inflateInit2_ (or never passed) is the local variable's memory *)
Lemma init_fail_mem gv vs nullstrm r msgv stv opq ret sp w:
  isptr vs -> ret <> Z_OK ->
  init_mem gv Tsh (strm_arg vs nullstrm) r msgv stv opq ret sp w *
  (if eq_dec (strm_arg vs nullstrm) nullval then raw_strm gv Tsh vs r msgv stv nullval nullval opq else emp)
  |-- @data_at_ CS Tsh (Tstruct _z_stream_s noattr) vs.
Proof.
  intros P Hr. unfold init_mem, strm_arg. destruct (zeq nullstrm 0).
  - rewrite !if_true by auto. rewrite emp_sepcon. unfold raw_strm. apply strm_to_undef.
  - destruct (eq_dec vs nullval); [subst; contradiction | ]. rewrite sepcon_emp.
    destruct (ret =? Z_VERSION_ERROR); [unfold raw_strm; apply strm_to_undef | ].
    destruct (ret =? Z_MEM_ERROR); [unfold raw_strm; apply strm_to_undef | ].
    destruct (Z.eqb_spec ret Z_OK); [contradiction | ].
    unfold raw_strm; apply strm_to_undef.
Qed.

(* the five outcomes of inflateInit2_ *)
Lemma init_cases vs nullstrm c ss w a: isptr vs ->
  ((negb (c =? 49) || negb (ss =? 112))%bool = true /\ init_ret (strm_arg vs nullstrm) c ss w a = -6) \/
  ((negb (c =? 49) || negb (ss =? 112))%bool = false /\ nullstrm = 0 /\
     init_ret (strm_arg vs nullstrm) c ss w a = -2) \/
  ((negb (c =? 49) || negb (ss =? 112))%bool = false /\ nullstrm <> 0 /\ a = false /\
     init_ret (strm_arg vs nullstrm) c ss w a = -4) \/
  ((negb (c =? 49) || negb (ss =? 112))%bool = false /\ nullstrm <> 0 /\ a = true /\ wbits_ok w = false /\
     init_ret (strm_arg vs nullstrm) c ss w a = -2) \/
  ((negb (c =? 49) || negb (ss =? 112))%bool = false /\ nullstrm <> 0 /\ a = true /\ wbits_ok w = true /\
     init_ret (strm_arg vs nullstrm) c ss w a = 0).
Proof.
  intros P. unfold init_ret, sizeof_z_stream, strm_arg.
  destruct (negb (c =? 49) || negb (ss =? 112))%bool; [left; auto | right].
  destruct (zeq nullstrm 0).
  - left. rewrite if_true by auto. auto.
  - right. destruct (eq_dec vs nullval); [subst; contradiction | ].
    destruct a; simpl.
    + right. destruct (wbits_ok w); [right | left]; auto.
    + left. auto.
Qed.

(* the version strings back: `other` (the local variable) and the harness's literal *)
Lemma ver_back gv vo vsel vbyte:
  @data_at Zlib.units.Inflate.CS (ver_sh vsel) (tarray tschar (Zlength (ver_vc vsel vbyte))) (ver_vc vsel vbyte)
    (ver_p gv vo vsel) * ver_rest gv vo vsel vbyte
  |-- @data_at_ CS Tsh (tarray tschar 2) vo * hversion_lit gv.
Proof.
  unfold ver_sh, ver_vc, ver_p, ver_rest, hversion_lit. rewrite tschar_cs.
  destruct (zeq vsel 0).
  - cancel; try apply data_at_data_at_.
  - rewrite sepcon_comm. cancel; try apply data_at_data_at_.
Qed.

(* the stream after a successful inflateInit2_ *)
Definition z_init (adl rs: Z) (L: live) : zfields :=
  ZF nullval 0 0 nullval 0 0 None 0 (if i_wrap (l_s L) =? 0 then adl else Z.land (i_wrap (l_s L)) 1)
     (Vlong (Int64.repr rs)).

Lemma init_istream gv vs tin tout adl dt rs L:
  0 <= adl <= Int64.max_unsigned ->
  istream_raw gv Tsh vs
    (raw_after_init (RF nullval (Vint (Int.repr 0)) (Vlong (Int64.repr tin)) nullval (Vint (Int.repr 0))
       (Vlong (Int64.repr tout)) (Vint (Int.repr dt)) (Vlong (Int64.repr adl)) (Vlong (Int64.repr rs))) (l_s L)) L
  = istream gv Tsh vs (z_init adl rs L) (Some L).
Proof.
  intros A. rewrite <- istream_raw_istream.
  - unfold raw_after_init, z_init; simpl. f_equal. f_equal. destruct (i_wrap (l_s L) =? 0); reflexivity.
  - unfold zf_ok, z_init; simpl. split; [rep_lia | ]. split; [rep_lia | ]. split; [rep_lia | ].
    split; [rep_lia | ]. split; [rep_lia | ].
    destruct (i_wrap (l_s L) =? 0); [auto | ].
    assert (M: Z.land (i_wrap (l_s L)) 1 = i_wrap (l_s L) mod 2) by (apply (Z.land_ones _ 1); lia).
    rewrite M. pose proof (Z.mod_pos_bound (i_wrap (l_s L)) 2 ltac:(lia)). rep_lia.
  - reflexivity.
Qed.

(* a stream (live or not) gives back the local variable's memory *)
Lemma istream_to_undef gv vs z st:
  istream gv Tsh vs z st |-- @data_at_ CS Tsh (Tstruct _z_stream_s noattr) vs * TT.
Proof.
  unfold istream, zstrm_at, strm_rep. destruct st as [L | ]; Intros.
  - sep_apply strm_to_undef. cancel.
  - sep_apply strm_to_undef. cancel.
Qed.

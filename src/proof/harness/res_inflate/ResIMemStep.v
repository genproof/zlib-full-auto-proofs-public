(* Law res_memory_inflate: one inflate() call of main's loop keeps the counters invariant [mem_ok]
   (ResIMemTheory.v) and gives both assertions of the loop: Z_MEM_ERROR only with count.failed set, and
   count.peak within (1 << w) + 7160.  The allocator sees at most one event per call (ZEvents.win_ev): the window
   allocated, or its allocation failed (the call entered the mode MEM); the model facts of res_call_stmt
   (ModelStmt.v) say which. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.za.inflate_api.USpec.
Require Import Zlib.proof.za.inflate.ZEvents.
Require Import Zlib.proof.harness.counted.Spec.
Require Import Zlib.proof.harness.res_inflate.ModelStmt.
Require Import Zlib.proof.harness.res_inflate.ResIMemTheory.

(* a failed allocation leaves the counters as they are *)
Lemma cnt_fail_ev (tr : list zev) : cnt (tr ++ [ZFail]) = cnt tr.
Proof. unfold cnt. rewrite fold_left_app. reflexivity. Qed.

(* one inflate() call on the live stream L (the model's run res): the next state keeps res_inv and mem_ok with
   the call's events, Z_MEM_ERROR comes with count.failed, and count.peak is within the law's bound *)
Lemma mem_call (MODEL : res_call_stmt) (hw flush : Z) (z : zfields) (L : live) (inp : list Z) (res : result)
    (tr : list zev) :
  8 <= hw <= 15 ->
  res_inv hw (l_s L) -> Zlib.proof.inflate.InvW.swfW (l_s L) -> live_ok L -> zf_ok z ->
  bytes_ok inp -> Zlength inp <= Int.max_unsigned ->
  Zlib.proof.inflate.Model2.run2 flush lenfix_list distfix_list (m_init z L inp) res ->
  mem_ok hw (l_s L) tr ->
  res_inv hw (m_s (r_m res)) /\
  mem_ok hw (m_s (r_m res)) (tr ++ win_ev (l_s L) (m_s (r_m res))) /\
  (r_ret res = Z_MEM_ERROR -> za_failed (tr ++ win_ev (l_s L) (m_s (r_m res))) = true) /\
  snd (cnt (tr ++ win_ev (l_s L) (m_s (r_m res)))) <= 2 ^ hw + 7160.
Proof.
  intros Hhw Hinv Hsw Hlive Hz Hb Hlen Hrun Hok.
  destruct (MODEL hw flush z L inp res Hinv Hsw Hlive Hz Hb Hlen Hrun) as (Hinv' & Hwin & Hmem & Hent & Hret).
  set (s := l_s L) in *. set (s' := m_s (r_m res)) in *.
  assert (Hok' : mem_ok hw s' (tr ++ win_ev s s')).
  { destruct Hok as (N & EN & EC & EW & EB & EM).
    unfold win_ev.
    destruct (i_win s) eqn:W; simpl.
    - (* the window was there: no event *)
      rewrite app_nil_r. exists N. repeat split; try lia; auto.
      + intros W'. rewrite (Hwin eq_refl) in W'. discriminate.
      + intros M'. destruct (Z.eq_dec (i_mode s) MEM) as [M|M]; auto.
        specialize (Hent M M'). rewrite (Hwin eq_refl) in Hent. discriminate.
    - specialize (EW eq_refl). rewrite EW in EN, EC, EB. clear EW.
      destruct (i_win s') eqn:W'; simpl.
      + (* the window allocated: 2^wbits bytes more *)
        destruct Hinv' as (_ & _ & Hwb & _).
        assert (Hk : 0 <= 2 ^ i_wbits s' <= 2 ^ hw).
        { destruct (Z.ltb_spec (i_wbits s') 0).
          - rewrite Z.pow_neg_r by lia. split; [lia|]. apply Z.pow_nonneg; lia.
          - split; [apply Z.pow_nonneg; lia|]. apply Z.pow_le_mono_r; lia. }
        assert (2 ^ hw <= 2 ^ 15) by (apply Z.pow_le_mono_r; lia).
        exists (state_size + 2 ^ i_wbits s'). rewrite za_now_alloc, EN. repeat split; try lia.
        * unfold cnt. rewrite fold_left_app. fold (cnt tr). rewrite EC. cbn [fold_left cnt_step fst snd].
          rewrite Z.mod_small by (unfold state_size in *; lia).
          destruct (Z.ltb_spec state_size (state_size + 2 ^ i_wbits s')); f_equal; lia.
        * intros E; congruence.
        * intros M'. exfalso. destruct (Z.eq_dec (i_mode s) MEM) as [M|M].
          -- rewrite (Hmem M) in W'. fold s in W'. congruence.
          -- specialize (Hent M M'). congruence.
      + destruct ((i_mode s' =? MEM) && negb (i_mode s =? MEM))%bool eqn:F; simpl.
        * (* the allocation of the window failed *)
          exists state_size. rewrite za_now_fail, cnt_fail_ev, za_failed_fail. repeat split; auto; lia.
        * rewrite app_nil_r. exists state_size. repeat split; auto; try lia.
          intros M'. rewrite M' in F. simpl in F.
          destruct (Z.eq_dec (i_mode s) MEM) as [M|M]; auto.
          rewrite (proj2 (Z.eqb_neq _ _) M) in F. discriminate. }
  split; [exact Hinv'|]. split; [exact Hok'|].
  destruct Hok' as (N & EN & EC & EW & EB & EM). split.
  - intros R. apply EM, Hret, R.
  - rewrite EC. simpl. unfold state_size in EB. lia.
Qed.

(* Round-trip laws, part RT-X: the conjunction of the deflate laws' invariant (LawFacts.api_facts) and
   the round trip's (RTDIface.kfacts) satisfies api_facts and RTXFacts.rt_extra (pure Coq). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.roundtrip.RTXFacts.
Import ListNotations.
Local Open Scope Z_scope.

Theorem rt_ik_facts : rt_ik_stmt.
Proof.
  intros I Iend K HA HK.
  destruct HA as [Ainit Atune Adict Ahead Adefl Aparams Aef Aeo Aeb Aee].
  destruct HK as [Kinit Ktune Kdict Khead Kdefl Kparams].
  split.
  - constructor.
    + (* init *)
      intros level method wbits mem strategy a1 a2 a3 a4 a5 z H1 H2 H3 H4 H5.
      destruct (Ainit level method wbits mem strategy a1 a2 a3 a4 a5 z H1 H2 H3 H4 H5) as [Hex Hall].
      split; [exact Hex|].
      intros os z' code Hc.
      destruct (Hall os z' code Hc) as (Hcodes & Herr & Hok).
      split; [exact Hcodes|]. split; [exact Herr|].
      intros ->. destruct (Hok eq_refl) as (s & -> & Hg & HI).
      exists s. split; [reflexivity|]. split; [exact Hg|]. split; [exact HI|].
      destruct (Kinit level method wbits mem strategy a1 a2 a3 a4 a5 z s z' H1 H2 H3 H4 H5 Hc) as (_ & _ & HKs).
      exact HKs.
    + (* tune *)
      intros wrap s tin tout adler good lazy nice chain z [HI HKs] H1 H2 H3 H4.
      destruct (Atune wrap s tin tout adler good lazy nice chain z HI H1 H2 H3 H4) as (s' & Hc & Hg & HI').
      exists s'. split; [exact Hc|]. split; [exact Hg|]. split; [exact HI'|].
      destruct (Ktune wrap s tin tout adler good lazy nice chain z s' z Z_OK HKs H1 H2 H3 H4 Hc) as (_ & _ & HK').
      exact HK'.
    + (* dict *)
      intros wrap s tin tout adler d ain aout msg [HI HKs] Hd Hdl Hain Haout.
      destruct (Adict wrap s tin tout adler d ain aout msg HI Hd Hdl Hain Haout)
        as (s' & z' & code & Hc & Hg & Hcodes & Herr & HI').
      exists s', z', code. split; [exact Hc|]. split; [exact Hg|]. split; [exact Hcodes|]. split; [exact Herr|].
      split; [exact HI'|].
      destruct (Kdict wrap s tin tout adler d ain aout msg s' z' code HKs Hd Hdl Hain Haout Hc Hcodes Herr)
        as (_ & _ & HK').
      exact HK'.
    + (* head *)
      intros dict wrap s tin tout adler h z [HI HKs] Hh.
      destruct (Ahead dict wrap s tin tout adler h z HI Hh) as [Hw2 Hn2].
      split; [|exact Hn2].
      intros Hw. destruct (Hw2 Hw) as [Hc HI']. split; [exact Hc|]. split; [exact HI'|].
      subst wrap. exact (Khead dict s tin tout adler h HKs Hh).
    + (* deflate *)
      intros dict wrap D O fin s tin tout adler inb aout flush msg [HI HKs] Hf Hb HD Ha HO Hfin.
      destruct (Adefl dict wrap D O fin s tin tout adler inb aout flush msg HI Hf Hb HD Ha HO Hfin)
        as (s' & z' & code & Hc & Hg & Hcall & Hcodes & Hend & Hbuf & Hpost).
      exists s', z', code.
      split; [exact Hc|]. split; [exact Hg|]. split; [exact Hcall|]. split; [exact Hcodes|].
      split; [exact Hend|]. split; [exact Hbuf|].
      assert (Ha' : 0 <= aout <= 2097152) by lia.
      destruct (Kdefl dict wrap D O fin s tin tout adler inb aout flush msg s' z' code HKs Hf Hb HD Ha' HO Hfin
                  Hc Hg Hcall Hcodes Hend Hbuf) as (_ & HK').
      cbv zeta in *.
      destruct (code =? Z_STREAM_END); [exact Hpost|].
      split; [exact Hpost|exact HK'].
    + (* params *)
      intros dict wrap D O s tin tout adler inb aout level strategy msg [HI HKs] H1 H2 Hb HD Ha HO.
      destruct (Aparams dict wrap D O s tin tout adler inb aout level strategy msg HI H1 H2 Hb HD Ha HO)
        as (s' & z' & code & Hc & Hg & Hcall & Hcodes & Herr & HI').
      exists s', z', code.
      split; [exact Hc|]. split; [exact Hg|]. split; [exact Hcall|]. split; [exact Hcodes|].
      split; [exact Herr|].
      assert (Ha' : 0 <= aout <= 2097152) by lia.
      destruct (Kparams dict wrap D O s tin tout adler inb aout level strategy msg s' z' code HKs H1 H2 Hb HD Ha'
                  HO Hc Hg Hcall Hcodes Herr) as (_ & HK').
      split; [exact HI'|exact HK'].
    + exact Aef.
    + exact Aeo.
    + exact Aeb.
    + exact Aee.
  - constructor.
    + (* init *)
      intros level method wbits mem strategy a1 a2 a3 a4 a5 z s z' H1 H2 H3 H4 H5 Hc.
      destruct (Kinit level method wbits mem strategy a1 a2 a3 a4 a5 z s z' H1 H2 H3 H4 H5 Hc) as (Hw & _ & _).
      split; [exact Hw|].
      intros Hraw.
      destruct (Ainit level method wbits mem strategy a1 a2 a3 a4 a5 z H1 H2 H3 H4 H5) as [_ Hall].
      destruct (Hall _ _ _ Hc) as (_ & Herr & _).
      assert (Hp : params_ok level method wbits mem strategy = true).
      { destruct (params_ok level method wbits mem strategy) eqn:E; [reflexivity|].
        destruct Herr as [_ Herr]. specialize (Herr eq_refl). discriminate Herr. }
      unfold params_ok in Hp. rewrite Hraw in Hp. simpl in Hp.
      rewrite !andb_true_iff in Hp. destruct Hp as [_ Hp]. rewrite orb_false_r in Hp.
      apply negb_true_iff, Z.eqb_neq in Hp.
      unfold rwbe, rwb_of. fold (wb_of wbits).
      destruct (wb_of wbits =? 8) eqn:E; [apply Z.eqb_eq in E; contradiction|reflexivity].
    + (* tune *)
      intros wrap s tin tout adler good lazy nice chain z s' z' code [_ HKs] H1 H2 H3 H4 Hc.
      destruct (Ktune wrap s tin tout adler good lazy nice chain z s' z' code HKs H1 H2 H3 H4 Hc) as (Hw & _).
      exact Hw.
    + (* dict *)
      intros wrap s tin tout adler d ain aout msg s' z' code [HI HKs] Hd Hdl Hain Haout Hc.
      destruct (Adict wrap s tin tout adler d ain aout msg HI Hd Hdl Hain Haout)
        as (s2 & z2 & code2 & Hc2 & _ & Hcodes & Herr & _).
      rewrite Hc in Hc2. injection Hc2 as <- <- <-.
      destruct (Kdict wrap s tin tout adler d ain aout msg s' z' code HKs Hd Hdl Hain Haout Hc Hcodes Herr)
        as (Hw & _).
      exact Hw.
    + (* deflate *)
      intros dict wrap D O fin s tin tout adler inb aout flush msg s' z' code [HI HKs] Hf Hb HD Ha HO Hfin Hc.
      destruct (Adefl dict wrap D O fin s tin tout adler inb aout flush msg HI Hf Hb HD Ha HO Hfin)
        as (s2 & z2 & code2 & Hc2 & Hg & Hcall & Hcodes & Hend & Hbuf & _).
      rewrite Hc in Hc2. injection Hc2 as <- <- <-.
      assert (Ha' : 0 <= aout <= 2097152) by lia.
      destruct (Kdefl dict wrap D O fin s tin tout adler inb aout flush msg s' z' code HKs Hf Hb HD Ha' HO Hfin
                  Hc Hg Hcall Hcodes Hend Hbuf) as (Hw & HK').
      split; [exact Hw|].
      intros ->. cbv zeta in HK'. rewrite Z.eqb_refl in HK'. exact HK'.
    + (* params *)
      intros dict wrap D O s tin tout adler inb aout level strategy msg s' z' code [HI HKs] H1 H2 Hb HD Ha HO Hc.
      destruct (Aparams dict wrap D O s tin tout adler inb aout level strategy msg HI H1 H2 Hb HD Ha HO)
        as (s2 & z2 & code2 & Hc2 & Hg & Hcall & Hcodes & Herr & _).
      rewrite Hc in Hc2. injection Hc2 as <- <- <-.
      assert (Ha' : 0 <= aout <= 2097152) by lia.
      destruct (Kparams dict wrap D O s tin tout adler inb aout level strategy msg s' z' code HKs H1 H2 Hb HD Ha'
                  HO Hc Hg Hcall Hcodes Herr) as (Hw & _).
      exact Hw.
Qed.

"""fill_window: the ported proofs run unchanged (fill_window reaches next_in only through read_buf); the two
lemmas that split dfull_in into the fields the loop reads and the rest, and join them back, get a faster proof.
With `cancel`/`entailer!` on the concrete field_at atoms their Qed takes about 18 s each in the kernel.  Abstracting first every atom of the left side that occurs
syntactically on the right side leaves a permutation of variables, whose proof the kernel checks in about 2 s."""

M = 'Zlib.proof.deflate.Body_fill_window'
GEN_LEAVES = (
    "(* Generalize every separating conjunct of `t` that occurs syntactically in `r` (the other side of the entailment):\n"
    "   the cancellation is then a permutation of variables, cheap for the kernel. *)\n"
    "Ltac fw_gen_leaves r t := lazymatch t with\n"
    "  | (?a * ?b)%logic => fw_gen_leaves r a; fw_gen_leaves r b\n"
    "  | _ => lazymatch r with\n"
    "         | context [t] => let x := fresh \"A\" in generalize t as x; intros x\n"
    "         | _ => idtac\n"
    "         end\n"
    "  end.\n\n")
PATCHES = [
    (M, "Lemma dfull_in_open s z p pin ish msgv gv :", GEN_LEAVES + "Lemma dfull_in_open s z p pin ish msgv gv :"),
    (M, "  cbn [fst snd d_trm]. Intros. apply andp_right; [apply prop_right; tauto|]. cancel.\n",
     "  cbn [fst snd d_trm]. Intros. apply andp_right; [apply prop_right; tauto|].\n"
     "  match goal with |- ?l |-- ?r => fw_gen_leaves r l end. cancel.\n"),
    (M, "  cbn [fst snd d_trm]. entailer!.\n",
     "  cbn [fst snd d_trm].\n"
     "  match goal with |- ?l |-- ?r => fw_gen_leaves r l end. entailer!.\n"),
]

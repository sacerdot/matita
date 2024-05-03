(*

lemma nat_ind_lt_le (Q:predicate …):
      (∀n. (∀m. m < n → Q m) → Q n) → ∀n,m. m ≤ n → Q m.
#Q #H1 #n @(nat_ind_succ … n) -n
[ #m #H <(nle_inv_zero_dx … H) -m
  @H1 -H1 #o #H elim (nlt_inv_zero_dx … H)
| /5 width=3 by nlt_nle_trans, nle_inv_succ_bi/
]
qed-.

(*** nat_elim1 *)
lemma nat_ind_lt (Q:predicate …):
      (∀n. (∀m. m < n → Q m) → Q n) → ∀n. Q n.
/4 width=2 by nat_ind_lt_le/ qed-.
*)

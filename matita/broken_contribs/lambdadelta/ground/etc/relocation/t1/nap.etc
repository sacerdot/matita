include "ground/relocation/t1/tr_uni_pap.ma".
include "ground/relocation/t1/tr_compose_pap.ma".
include "ground/relocation/t1/tr_pap_eq.ma".
include "ground/relocation/t1/tr_pap_hdtl_eq.ma".
include "ground/notation/functions/atsection_2.ma".
include "ground/arith/nat_lt.ma".
include "ground/arith/nat_plus_pplus.ma".
include "ground/arith/nat_pred_succ.ma".

lemma nlt_npsucc_bi (n1) (n2):
      n1 < n2 → npsucc n1 < npsucc n2.
#n1 #n2 #Hn elim Hn -n2 //
#n2 #_ #IH /2 width=1 by plt_succ_dx_trans/
qed.

definition tr_nap (f) (l:ℕ): ℕ ≝
           ↓(f＠⧣❨↑l❩).

interpretation
  "functional non-negative application (total relocation maps)"
  'AtSection f l = (tr_nap f l).

lemma tr_nap_unfold (f) (l):
      ↓(f＠⧣❨↑l❩) = f＠§❨l❩.
// qed.

lemma tr_pap_succ_nap (f) (l):
      ↑(f＠§❨l❩) = f＠⧣❨↑l❩.
// qed.

lemma tr_compose_nap (f2) (f1) (l):
      f2＠§❨f1＠§❨l❩❩ = (f2•f1)＠§❨l❩.
#f2 #f1 #l
<tr_nap_unfold <tr_nap_unfold <tr_nap_unfold
<tr_compose_pap <npsucc_pnpred //
qed.

lemma tr_uni_nap (n) (m):
      m + n = 𝐮❨n❩＠§❨m❩.
#n #m
<tr_nap_unfold
<tr_uni_pap <nrplus_npsucc_sn //
qed.

lemma tr_nap_push (f) (l):
      (⁤↑(f＠§❨l❩)) = (⫯f)＠§❨⁤↑l❩.
#f #l
<tr_nap_unfold <tr_nap_unfold
<tr_pap_push <npsucc_pnpred //
qed.

lemma tr_nap_pushs_lt (f) (n) (m):
      m < n → m = (⫯*[n]f)＠§❨m❩.
#f #n #m #Hmn
<tr_nap_unfold <tr_pap_pushs_le
/2 width=1 by nlt_npsucc_bi/
qed-.

theorem tr_nap_eq_repl (i):
        stream_eq_repl … (λf1,f2. f1＠§❨i❩ = f2＠§❨i❩).
#i #f1 #f2 #Hf
<tr_nap_unfold <tr_nap_unfold
/3 width=1 by tr_pap_eq_repl, eq_f/
qed.

lemma tr_eq_inv_nap_zero_tl_bi (f1) (f2):
      f1＠§❨𝟎❩ = f2＠§❨𝟎❩ → ⇂f1 ≗ ⇂f2 → f1 ≗ f2.
#f1 #f2
<tr_nap_unfold <tr_nap_unfold #H1 #H2
/3 width=1 by tr_eq_inv_pap_unit_tl_bi, eq_inv_pnpred_bi/
qed-.

lemma tr_nap_plus_sn (f) (m) (n:ℕ):
      (⫯⇂*[⁤↑n]f)＠§❨m❩+f＠§❨n❩ = f＠§❨m+n❩.
#f #m @(nat_ind_succ … m) -m [| #m #_ ] #n
[ <nplus_zero_sn <nplus_zero_sn //
| <tr_nap_push <nplus_comm in ⊢ (???%);
  <tr_nap_unfold <tr_nap_unfold <tr_nap_unfold
  <npsucc_pnpred <nplus_pos_sn <nrplus_pnpred_dx
  >nrplus_npsucc_sn <nrplus_pos_dx
  <pplus_comm in ⊢ (???%); <tr_pap_plus //
]
qed.

lemma tr_nap_plus_dx (f) (m) (n):
      (⇂*[n]f)＠§❨m❩+(⫯f)＠§❨n❩ = f＠§❨m+n❩.
#f #m #n @(nat_ind_succ … n) -n [| #n #_ ]
[ //
| <tr_nap_push
  <tr_nap_unfold <tr_nap_unfold <tr_nap_unfold
  <npsucc_pnpred <nplus_pnpred_sn
  >nrplus_npsucc_sn <nrplus_pos_dx
  <tr_pap_plus //
]
qed.

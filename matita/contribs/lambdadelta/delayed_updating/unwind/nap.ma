include "ground/relocation/tr_uni_pap.ma".
include "ground/relocation/tr_compose_pap.ma".
include "ground/notation/functions/applysucc_2.ma".
include "ground/arith/nat_lt.ma".
include "ground/arith/nat_plus_rplus.ma".
include "ground/arith/nat_pred_succ.ma".

lemma nlt_npsucc_bi (n1) (n2):
      n1 < n2 → npsucc n1 < npsucc n2.
#n1 #n2 #Hn elim Hn -n2 //
#n2 #_ #IH /2 width=1 by plt_succ_dx_trans/
qed.

definition tr_nap (f) (l:nat): nat ≝
           ↓(f＠⧣❨↑l❩).

interpretation
  "functional non-negative application (total relocation maps)"
  'ApplySucc f l = (tr_nap f l).

lemma tr_nap_unfold (f) (l):
      ↓(f＠⧣❨↑l❩) = f@↑❨l❩.
// qed.

lemma tr_compose_nap (f2) (f1) (l):
      f2@↑❨f1@↑❨l❩❩ = (f2∘f1)@↑❨l❩.
#f2 #f1 #l
<tr_nap_unfold <tr_nap_unfold <tr_nap_unfold
<tr_compose_pap <npsucc_pred //
qed.

lemma tr_uni_nap (n) (m):
      m + n = 𝐮❨n❩@↑❨m❩.
#n #m
<tr_nap_unfold
<tr_uni_pap <nrplus_npsucc_sn //
qed.

lemma tr_nap_push (f):
      ∀l. ↑(f@↑❨l❩) = (⫯f)@↑❨↑l❩.
#f #l
<tr_nap_unfold <tr_nap_unfold
<tr_pap_push <pnpred_psucc //
qed.

lemma tr_nap_pushs_lt (f) (n) (m):
      m < n → m = (⫯*[n]f)@↑❨m❩.
#f #n #m #Hmn
<tr_nap_unfold <tr_pap_pushs_le
/2 width=1 by nlt_npsucc_bi/
qed-.

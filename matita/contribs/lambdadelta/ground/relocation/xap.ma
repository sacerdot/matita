include "ground/arith/nat_rplus_pplus.ma".
include "ground/relocation/nap.ma".
include "ground/notation/functions/apply_2.ma".
include "ground/relocation/tr_compose_pn.ma".
include "ground/relocation/tr_pap_tls.ma".

definition tr_xap (f) (l:nat): nat ≝
           (⫯f)@↑❨l❩.

interpretation
  "functional extended application (total relocation maps)"
  'Apply f l = (tr_xap f l).

lemma tr_xap_unfold (f) (l):
      (⫯f)@↑❨l❩ = f＠❨l❩.
// qed.

lemma tr_xap_zero (f):
      (𝟎) = f＠❨𝟎❩.
// qed.

lemma tr_xap_ninj (f) (p):
      ninj (f＠⧣❨p❩) = f＠❨ninj p❩.
// qed.

lemma tr_xap_succ_nap (f) (n):
      ↑(f@↑❨n❩) = f＠❨↑n❩.
#f #n
<tr_xap_ninj //
qed.

lemma tr_compose_xap (f2) (f1) (l):
      f2＠❨f1＠❨l❩❩ = (f2∘f1)＠❨l❩.
#f2 #f1 #l
<tr_xap_unfold <tr_xap_unfold <tr_xap_unfold
>tr_compose_nap >tr_compose_push_bi //
qed.

lemma tr_uni_xap_succ (n) (m):
      ↑m + n = 𝐮❨n❩＠❨↑m❩.
#n #m
<tr_xap_unfold
<tr_nap_push <tr_uni_nap //
qed.

lemma tr_uni_xap (n) (m):
      𝐮❨n❩＠❨m❩ ≤ m+n.
#n #m @(nat_ind_succ … m) -m //
qed.

lemma tr_xap_push (f) (l):
      ↑(f＠❨l❩) = (⫯f)＠❨↑l❩.
#f #l
<tr_xap_unfold <tr_xap_unfold
<tr_nap_push //
qed.

lemma tr_xap_pushs_le (f) (n) (m):
      m ≤ n → m = (⫯*[n]f)＠❨m❩.
#f #n #m #Hmn
<tr_xap_unfold >tr_pushs_succ <tr_nap_pushs_lt //
/2 width=1 by nlt_succ_dx/
qed-.

lemma tr_xap_plus (n1) (n2) (f):
      (⇂*[n2]f)＠❨n1❩+f＠❨n2❩ = f＠❨n1+n2❩.
* [| #n1 ] // * [| #n2 ] // #f
<nrplus_inj_sn <nrplus_inj_dx
<nrplus_inj_sn <nrplus_inj_dx
>tr_pap_plus //
qed.

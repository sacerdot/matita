(**) (* reverse include *)
include "ground/relocation/t1/tr_pn_eq.ma".
include "ground/relocation/t1/tr_compose_pn.ma".
include "ground/relocation/t1/nap.ma".
include "ground/notation/functions/at_2.ma".

definition tr_xap (f) (l:ℕ): ℕ ≝
           (⫯f)＠§❨l❩.

interpretation
  "functional extended application (total relocation maps)"
  'At f l = (tr_xap f l).

lemma tr_xap_unfold (f) (l):
      (⫯f)＠§❨l❩ = f＠❨l❩.
// qed.

lemma tr_xap_zero (f):
      (𝟎) = f＠❨𝟎❩.
// qed.

lemma tr_xap_npos (f) (p):
      npos (f＠⧣❨p❩) = f＠❨npos p❩.
// qed.

lemma tr_xap_succ_nap (f) (n):
      (⁤↑(f＠§❨n❩)) = f＠❨⁤↑n❩.
#f #n
<tr_xap_npos //
qed.

lemma tr_compose_xap (f2) (f1) (l):
      f2＠❨f1＠❨l❩❩ = (f2•f1)＠❨l❩.
#f2 #f1 #l
<tr_xap_unfold <tr_xap_unfold <tr_xap_unfold
>tr_compose_nap >tr_compose_push_bi //
qed.

lemma tr_uni_xap_succ (n) (m:ℕ):
      (⁤↑m) + n = 𝐮❨n❩＠❨⁤↑m❩.
#n #m
<tr_xap_unfold
<tr_nap_push <tr_uni_nap //
qed.

lemma tr_uni_xap (n) (m):
      𝐮❨n❩＠❨m❩ ≤ m+n.
#n #m @(nat_ind_succ … m) -m //
qed.

lemma tr_xap_push (f) (l):
      (⁤↑(f＠❨l❩)) = (⫯f)＠❨⁤↑l❩.
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
<nplus_pos_sn <nrplus_pos_dx
<nplus_pos_sn <nrplus_pos_dx
>tr_pap_plus //
qed.

theorem tr_xap_eq_repl (i):
        stream_eq_repl … (λf1,f2. f1＠❨i❩ = f2＠❨i❩).
#i #f1 #f2 #Hf
<tr_xap_unfold <tr_xap_unfold
/3 width=1 by tr_push_eq_repl, tr_nap_eq_repl/
qed.

lemma tr_nap_plus_dx_xap (f) (m) (n:ℕ):
      (⇂*[⁤↑n]f)＠❨m❩+f＠§❨n❩ = f＠§❨m+n❩.
/2 width=1 by tr_nap_eq_repl/
qed.

lemma tr_nap_plus_sn_xap (f) (m) (n):
      (⇂*[n]f)＠§❨m❩+f＠❨n❩ = f＠§❨m+n❩.
// qed.

lemma tr_xap_pos (f) (n):
      n = (⁤↑⫰n) → f＠❨n❩ = (⁤↑⫰(f＠❨n❩)).
#f #n #H0 >H0 -H0
<tr_xap_npos <npsucc_pnpred //
qed.

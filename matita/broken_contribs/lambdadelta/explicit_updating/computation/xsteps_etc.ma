include "explicit_updating/reduction/xbeta1.ma".
include "explicit_updating/reduction/xbeta.ma".
include "explicit_updating/computation/xsteps_term.ma".

axiom tmp3 (t0):
      ∀t1. t0 ➡[𝛃′] t1 → ∀t2. t0 ➡*[𝛃ⓣ] t2 →
      ∃∃t. t1 ➡*[𝛃ⓣ] t & t2 ➡*[𝛃ⓕ] t.

include "explicit_updating/reduction/xbeta1_valid.ma".
include "explicit_updating/computation/xsteps_term_valid.ma".
include "explicit_updating/computation/xsteps_phi.ma".

lemma tmp2 (t0):
      ∀t1. t0 ➡[𝛃′] t1 → ∀t2. t0 ➡*𝛟 t2 →
      ∃∃t. t1 ➡*𝛟 t & t2 ➡*[𝛃ⓕ] t.
#t0 #t1 #Ht01 #t2 * #Ht02 #Ht2
elim (tmp3 … Ht01 … Ht02) -t0 #t0 #Ht10 #Ht20
lapply (term_valid_xsteps_trans … Ht2 … Ht20) -Ht2
[ /2 width=6 by term_valid_xbeta1_trans/
| /2 width=5 by xbeta1_inv_abst_sx/
| /3 width=3 by xsteps_phi_fold, ex2_intro/
]
qed-.

include "explicit_updating/computation/xsteps_phi_eq.ma".

lemma tmp1 (t0):
      ∀t1. t0 ➡*[𝛃′] t1 → ∀t2. t0 ➡*𝛟 t2 →
      ∃∃t. t1 ➡*𝛟 t & t2 ➡*[𝛃ⓕ] t. 
#t0 #t1 #Ht01 elim Ht01 -t1
[ #t1 #Ht01 #t2 #Ht02
  /4 width=3 by eq_xsteps_phi_trans, xsteps_term_refl, term_eq_sym, ex2_intro/
| #tx #t1 #_ #Htx1 #IH #t2 #Ht02
  elim (IH … Ht02) -t0 #t0 #Htx0 #Ht20
  elim (tmp2 … Htx1 … Htx0) -tx #tx #Ht1x #Ht0x
  /4 width=5 by xsteps_term_trans, xbeta1_eq_repl, ex2_intro/
]
qed-.  

(*  
include "explicit_updating/reduction/xbeta1.ma".
include "explicit_updating/computation/xsteps_term.ma".

lemma pippo (t:𝕋) (S) (f):
      ∃∃t0. (S•f)＠⧣❨t❩ ➡*[𝛃𝗻] t0 & S＠⧣❨𝐬❨f❩＠⧣❨t❩❩ ➡*[𝛃𝗻] t0.
#t elim t -t
[ #p #S #f
  <subst_tapp_lref <subst_tapp_lref <subst_after_dapp
  /3 width=3 by xsteps_term_refl, ex2_intro/
| #b #t #IH #S #f
  <subst_tapp_abst <subst_tapp_abst
  elim (IH (⫯S) (⫯f)) -IH #t0 #H1t #H2t
  @(ex2_intro … (𝛌b.t0))
  [
  | @xsteps_term_abst_bi
    @(xsteps_term_trans … H2t) -H2t [ @xbeta1_eq_repl ]
  
(*
include "explicit_updating/reduction/xbeta1.ma".
include "explicit_updating/computation/xsteps_term.ma".

lemma xsteps_subst_tapp_bi (S) (t1) (t2):
      (𝛃ⓣ) t1 t2 → 
      ∃∃t3. t2 ➡*[𝛃ⓣ] t3 & S＠⧣❨t1❩ ➡*[𝛃ⓣ] S＠⧣❨t3❩.
#S #t1 #t2 * -t1 -t2
[ #f #t #x #y #Hx #Hy
  @xsteps_term_eq_repl
  [ @xbeta1_eq_repl |||
  | @(subst_tapp_eq_repl S … Hx) //
  | @(subst_tapp_eq_repl S … Hy) //
  ] -x -y
  <subst_tapp_lift <unwind_unfold


include "explicit_updating/computation/xsteps_substitution_tapp.ma".

lemma xsteps_subst_tapp_bi (S1) (S2) (t1) (t2):
      S1 ➡*[𝛃ⓣ] S2 → (𝛃ⓣ) t1 t2 → S1＠⧣❨t1❩ ➡*[𝛃ⓣ] S2＠⧣❨t2❩.
#S1 #S2 #t1 #t2 #HS12 #Ht12
@xsteps_term_trans
[ @xbeta1_eq_repl |
| @(xsteps_subst_tapp_dx_bi … HS12)
| @xsteps_subst_tapp_bi //
]







include "ground/arith/nat_lt_pred.ma".
include "explicit_updating/syntax/beta_nexts.ma".
include "explicit_updating/reduction/xbeta1.ma".
include "explicit_updating/computation/xsteps.ma".

lemma pippo (v1) (v2): 
      v1 ➡*[𝛃ⓣ] v2 → ∀t,n. ⬕[n←v1]t ➡*[𝛃ⓣ] ⬕[n←v2]t.
#v1 #v2 #Hv12 #t elim t -t
[ #p #n >(npsucc_pnpred p)
  elim (nat_split_lt_eq_gt n (↓p)) #Hnp destruct
  [
  | <beta_lref_succ <beta_lref_succ
  | elim (nlt_inv_gen … Hnp) -Hnp #Hnp #H0 >H0 -H0
    <beta_lref_le // <beta_lref_le /2 width=1 by xsteps_refl/



lemma pippo (v1) (v2) (t1) (t2) (n):
      v1 ➡*[𝛃ⓣ] v2 → t1 ➡*[𝛃ⓣ] t2 → ⬕[n←v1]t1 ➡*[𝛃ⓣ] ⬕[n←v2]t2.
#v1 #v2 #t1 elim t1 -t1
*)
*)
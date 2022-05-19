(**************************************************************************)
(*       ___                                                              *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||         The HELM team.                                      *)
(*      ||A||         http://helm.cs.unibo.it                             *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU General Public License Version 2                  *)
(*                                                                        *)
(**************************************************************************)

include "ground/relocation/pr_eq.ma".
include "ground/relocation/pr_pat_lt.ma".
include "ground/relocation/pr_pat_pat.ma".
include "ground/relocation/pr_nat.ma".
include "ground/relocation/pr_ist.ma".

(* TOTALITY CONDITION FOR PARTIAL RELOCATION MAPS ***************************)

(* Advanced constructions with pr_pat ***************************************)

(*** at_dec *)
lemma pr_pat_dec (f) (i1) (i2): 𝐓❨f❩ → Decidable (＠⧣❨i1,f❩ ≘ i2).
#f #i1 #i2 #Hf lapply (Hf i1) -Hf *
#j2 #Hf elim (eq_pnat_dec i2 j2)
[ #H destruct /2 width=1 by or_introl/
| /4 width=6 by pr_pat_mono, or_intror/
]
qed-.

(*** is_at_dec *)
lemma is_pr_pat_dec (f) (i2): 𝐓❨f❩ → Decidable (∃i1. ＠⧣❨i1,f❩ ≘ i2).
#f #i2 #Hf
lapply (dec_plt (λi1.＠⧣❨i1,f❩ ≘ i2) … (↑i2)) [| * ]
[ /2 width=1 by pr_pat_dec/
| * /3 width=2 by ex_intro, or_introl/
| #H @or_intror * #i1 #Hi12
  /5 width=3 by pr_pat_increasing, plt_succ_dx, ex2_intro/
]
qed-.

(* Main destructions with pr_pat ********************************************)

(*** at_ext *)
corec theorem pr_eq_ext_pat (f1) (f2): 𝐓❨f1❩ → 𝐓❨f2❩ →
              (∀i,i1,i2. ＠⧣❨i,f1❩ ≘ i1 → ＠⧣❨i,f2❩ ≘ i2 → i1 = i2) →
              f1 ≐ f2.
cases (pr_map_split_tl f1) #H1
cases (pr_map_split_tl f2) #H2
#Hf1 #Hf2 #Hi
[ @(pr_eq_push … H1 H2) @pr_eq_ext_pat -pr_eq_ext_pat
  [3:|*: /2 width=3 by pr_ist_inv_push/ ] -Hf1 -Hf2 #i #i1 #i2 #Hg1 #Hg2
  lapply (Hi (↑i) (↑i1) (↑i2) ??) /2 width=7 by pr_pat_push/
| cases (Hf2 (𝟏)) -Hf1 -Hf2 -pr_eq_ext_pat
  #j2 #Hf2 cases (pr_pat_increasing_strict … Hf2 … H2) -H2
  lapply (Hi (𝟏) (𝟏) j2 … Hf2) /2 width=2 by pr_pat_refl/ -Hi -Hf2 -H1
  #H2 #H cases (plt_ge_false … H) -H //
| cases (Hf1 (𝟏)) -Hf1 -Hf2 -pr_eq_ext_pat
  #j1 #Hf1 cases (pr_pat_increasing_strict … Hf1 … H1) -H1
  lapply (Hi (𝟏) j1 (𝟏) Hf1 ?) /2 width=2 by pr_pat_refl/ -Hi -Hf1 -H2
  #H1 #H cases (plt_ge_false … H) -H //
| @(pr_eq_next … H1 H2) @pr_eq_ext_pat -pr_eq_ext_pat
  [3:|*: /2 width=3 by pr_ist_inv_next/ ] -Hf1 -Hf2 #i #i1 #i2 #Hg1 #Hg2
  lapply (Hi i (↑i1) (↑i2) ??) /2 width=5 by pr_pat_next/
]
qed-.

(* Advanced constructions with pr_nat ***************************************)

lemma is_pr_nat_dec (f) (l2): 𝐓❨f❩ → Decidable (∃l1. @↑❨l1,f❩ ≘ l2).
#f #l2 #Hf elim (is_pr_pat_dec … (↑l2) Hf)
[ * /3 width=2 by ex_intro, or_introl/
| #H @or_intror * /3 width=2 by ex_intro/
]
qed-.

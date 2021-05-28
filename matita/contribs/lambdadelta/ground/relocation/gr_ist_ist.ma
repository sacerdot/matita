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

include "ground/relocation/gr_eq.ma".
include "ground/relocation/gr_pat_lt.ma".
include "ground/relocation/gr_pat_pat.ma".
include "ground/relocation/gr_ist.ma".

(* TOTALITY CONDITION FOR GENERIC RELOCATION MAPS ***********************************************************)

(* Advanced properties on at ************************************************)

(*** at_dec *)
lemma gr_pat_dec (f) (i1) (i2): 𝐓❪f❫ → Decidable (@❪i1,f❫ ≘ i2).
#f #i1 #i2 #Hf lapply (Hf i1) -Hf *
#j2 #Hf elim (eq_pnat_dec i2 j2)
[ #H destruct /2 width=1 by or_introl/
| /4 width=6 by gr_pat_mono, or_intror/
]
qed-.

(*** is_at_dec *)
lemma is_gr_pat_dec (f) (i2): 𝐓❪f❫ → Decidable (∃i1. @❪i1,f❫ ≘ i2).
#f #i2 #Hf
lapply (dec_plt (λi1.@❪i1,f❫ ≘ i2) … (↑i2)) [| * ]
[ /2 width=1 by gr_pat_dec/
| * /3 width=2 by ex_intro, or_introl/
| #H @or_intror * #i1 #Hi12
  /5 width=3 by gr_pat_increasing, plt_succ_dx, ex2_intro/
]
qed-.

(* Main forward lemmas on at ************************************************)

(*** at_ext *)
corec theorem gr_eq_ext_pat (f1) (f2): 𝐓❪f1❫ → 𝐓❪f2❫ →
              (∀i,i1,i2. @❪i,f1❫ ≘ i1 → @❪i,f2❫ ≘ i2 → i1 = i2) →
              f1 ≡ f2.
cases (gr_map_split_tl f1) #H1
cases (gr_map_split_tl f2) #H2
#Hf1 #Hf2 #Hi
[ @(gr_eq_push … H1 H2) @gr_eq_ext_pat -gr_eq_ext_pat
  [3:|*: /2 width=3 by gr_ist_inv_push/ ] -Hf1 -Hf2 #i #i1 #i2 #Hg1 #Hg2
  lapply (Hi (↑i) (↑i1) (↑i2) ??) /2 width=7 by gr_pat_push/
| cases (Hf2 (𝟏)) -Hf1 -Hf2 -gr_eq_ext_pat
  #j2 #Hf2 cases (gr_pat_increasing_strict … Hf2 … H2) -H2
  lapply (Hi (𝟏) (𝟏) j2 … Hf2) /2 width=2 by gr_pat_refl/ -Hi -Hf2 -H1
  #H2 #H cases (plt_ge_false … H) -H //
| cases (Hf1 (𝟏)) -Hf1 -Hf2 -gr_eq_ext_pat
  #j1 #Hf1 cases (gr_pat_increasing_strict … Hf1 … H1) -H1
  lapply (Hi (𝟏) j1 (𝟏) Hf1 ?) /2 width=2 by gr_pat_refl/ -Hi -Hf1 -H2
  #H1 #H cases (plt_ge_false … H) -H //
| @(gr_eq_next … H1 H2) @gr_eq_ext_pat -gr_eq_ext_pat
  [3:|*: /2 width=3 by gr_ist_inv_next/ ] -Hf1 -Hf2 #i #i1 #i2 #Hg1 #Hg2
  lapply (Hi i (↑i1) (↑i2) ??) /2 width=5 by gr_pat_next/
]
qed-.

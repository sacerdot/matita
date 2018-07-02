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

include "static_2/relocation/seq_seq.ma".
include "static_2/static/rex_drops.ma".
include "static_2/i_static/rexs.ma".

(* ITERATED EXTENSION ON REFERRED ENTRIES OF A CONTEXT-SENSITIVE REALTION ***)

definition tc_f_dedropable_sn: predicate (relation3 lenv term term) ≝
                               λR. ∀b,f,L1,K1. ⬇*[b, f] L1 ≘ K1 →
                               ∀K2,T. K1 ⪤*[R, T] K2 → ∀U. ⬆*[f] T ≘ U →
                               ∃∃L2. L1 ⪤*[R, U] L2 & ⬇*[b, f] L2 ≘ K2 & L1 ≡[f] L2.

definition tc_f_dropable_sn: predicate (relation3 lenv term term) ≝
                             λR. ∀b,f,L1,K1. ⬇*[b, f] L1 ≘ K1 → 𝐔⦃f⦄ →
                             ∀L2,U. L1 ⪤*[R, U] L2 → ∀T. ⬆*[f] T ≘ U →
                             ∃∃K2. K1 ⪤*[R, T] K2 & ⬇*[b, f] L2 ≘ K2.

definition tc_f_dropable_dx: predicate (relation3 lenv term term) ≝
                             λR. ∀L1,L2,U. L1 ⪤*[R, U] L2 →
                             ∀b,f,K2. ⬇*[b, f] L2 ≘ K2 → 𝐔⦃f⦄ → ∀T. ⬆*[f] T ≘ U →
                             ∃∃K1. ⬇*[b, f] L1 ≘ K1 & K1 ⪤*[R, T] K2.

(* Properties with generic slicing for local environments *******************)

lemma dedropable_sn_CTC: ∀R. f_dedropable_sn R → tc_f_dedropable_sn R.
#R #HR #b #f #L1 #K1 #HLK1 #K2 #T #H elim H -K2
[ #K2 #HK12 #U #HTU elim (HR … HLK1 … HK12 … HTU) -K1 -T -HR
  /3 width=4 by ex3_intro, inj/
| #K #K2 #_ #HK2 #IH #U #HTU -HLK1
  elim (IH … HTU) -IH #L #HL1 #HLK
  elim (HR … HLK … HK2 … HTU) -K -T -HR
  /3 width=6 by seq_trans, rexs_step_dx, ex3_intro/
]
qed-.

(* Inversion lemmas with generic slicing for local environments *************)

lemma dropable_sn_CTC: ∀R. f_dropable_sn R → tc_f_dropable_sn R.
#R #HR #b #f #L1 #K1 #HLK1 #Hf #L2 #U #H elim H -L2
[ #L2 #HL12 #T #HTU elim (HR … HLK1 … HL12 … HTU) -L1 -U -HR
  /3 width=3 by inj, ex2_intro/
| #L #L2 #_ #HL2 #IH #T #HTU -HLK1
  elim (IH … HTU) -IH #K #HK1 #HLK
  elim (HR … HLK … HL2 … HTU) -L -U -HR
  /3 width=3 by rexs_step_dx, ex2_intro/
]
qed-.

lemma dropable_dx_CTC: ∀R. f_dropable_dx R → tc_f_dropable_dx R.
#R #HR #L1 #L2 #U #H elim H -L2
[ #L2 #HL12 #b #f #K2 #HLK2 #Hf #T #HTU
  elim (HR … HL12 … HLK2 … HTU) -L2 -U -HR
  /3 width=3 by inj, ex2_intro/
| #L #L2 #_ #HL2 #IH #b #f #K2 #HLK2 #Hf #T #HTU
  elim (HR … HL2 … HLK2 … HTU) -L2 -HR // #K #HLK #HK2
  elim (IH … HLK … HTU) -IH -L -U
  /3 width=5 by rexs_step_dx, ex2_intro/
]
qed-.

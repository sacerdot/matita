(* Questo documento fa parte della libreria digitale HELM (http://helm.cs.unibo.it)
   ed è distribuito ai sensi della licenza GNU GPL versione 2
*)

include "ground/arith/wf1_ind_plt.ma".
include "canale/albero/peso.ma".
include "canale/notazione/sottotermine.ma".

(* Sottotermine *************************************************************)

inductive sub (X): predicate (𝕋) ≝
| sub_refl    : sub X X
| sub_step (T): psub X T → sub X T

with psub: predicate (𝕋) ≝
| psub_nabs (x) (T): sub X T → psub X (𝛌x.T)
| psub_appl (T) (V): sub X T → psub X (T❨V❩)
| psub_side (T) (V): sub X V → psub X (T❨V❩)
| psub_aabs (T): sub X T → psub X (𝛌.T)
.

interpretation
  "sottotermine (termine)"
  'subseteq U T = (sub U T).

interpretation
  "sottotermine prorio (termine)"
  'PSub U T = (psub U T).

interpretation
  "non sottotermine (termine)"
  'NoSub U T = (negation (sub U T)).

interpretation
  "non sottotermine prorio (termine)"
  'NoPSub U T = (negation (psub U T)).

(* Eliminazioni di base *****************************************************)

lemma sub_inv_gen (U) (T): U ⊆ T → ∨∨ U = T | U ⊂ T. 
#U #T * -T
[ /2 width=1 by or_introl/
| #T #H0 /2 width=1 by or_intror/
]
qed-.

lemma psub_inv_refs_dx (U) (r:ℝ): U ⧸⊂ r.
#U #s @(insert_eq_1 … (Refs s)) #Z * -Z
[ #x #T #_ #H0 -U destruct
| #T #V #_ #H0 -U destruct
| #T #V #_ #H0 -U destruct
| #T #_ #H0 -U destruct
]
qed-.

lemma psub_inv_nabs_dx (U) (x) (T): U ⊂ 𝛌x.T → U ⊆ T.
#U #y #Y @(insert_eq_1 … (𝛌y.Y)) #Z * -Z
[ #x #T #HUT #H0 destruct -x //
| #T #V #_ #H0 destruct
| #T #V #_ #H0 destruct
| #T #_ #H0 destruct
]
qed-.

lemma psub_inv_appl_dx (U) (T) (V): U ⊂ T❨V❩ → ∨∨ U ⊆ T | U ⊆ V.
#U #X #Y @(insert_eq_1 … (X❨Y❩)) #Z * -Z
[ #x #T #_ #H0 destruct
| #T #V #HUT #H0 destruct /2 width=1 by or_introl/
| #T #V #HWV #H0 destruct /2 width=1 by or_intror/
| #T #_ #H0 destruct
]
qed-.

lemma psub_inv_aabs_dx (U) (T): U ⊂ 𝛌.T → U ⊆ T.
#U #Y @(insert_eq_1 … (𝛌.Y)) #Z * -Z
[ #x #T #_ #H0 destruct
| #T #V #_ #H0 destruct
| #T #V #_ #H0 destruct
| #T #HUT #H0 destruct //
]
qed-.

(* Eliminazioni col peso ****************************************************)

lemma sub_peso (U) (T): U ⊆ T → ♯U ≤ ♯T.
#U @(wf1_ind_plt … peso) #p #IH *
[ #r #Hp #H0
  elim (sub_inv_gen … H0) -H0 #H0 destruct //
  elim (psub_inv_refs_dx … H0)
| #x #T #Hp #H0
  elim (sub_inv_gen … H0) -H0 #H0 destruct //
  lapply (psub_inv_nabs_dx … H0) -H0 #H0
  /3 width=1 by ple_succ_dx/
| #T #V #Hp #H0
  elim (sub_inv_gen … H0) -H0 #H0 destruct //
  elim (psub_inv_appl_dx … H0) -H0 #H0
  lapply (IH … H0) -H0 // -IH #IH
  /3 width=3 by ple_plt_trans, plt_des_le/
| #T #Hp #H0
  elim (sub_inv_gen … H0) -H0 #H0 destruct //
  lapply (psub_inv_aabs_dx … H0) -H0 #H0
  /3 width=1 by ple_succ_dx/
]
qed-.

lemma psub_peso (U) (T): U ⊂ T → ♯U < ♯T.
#U #T * -T
/3 width=3 by sub_peso, ple_plt_trans/
qed-.

(* Costruzioni di base ******************************************************)

lemma psub_nabs_refl (x) (T): T ⊂ 𝛌x.T.
/2 width=1 by sub_refl, psub_nabs/
qed.

lemma psub_appl_refl (T) (V): T ⊂ T❨V❩.
/2 width=1 by sub_refl, psub_appl/
qed.

lemma psub_side_refl (T) (V): V ⊂ T❨V❩.
/2 width=1 by sub_refl, psub_side/
qed.

(* Costruzioni principali ***************************************************)

theorem sub_trans: Transitive … sub.
#U #X #HX @(wf1_ind_plt … peso) #p #IH *
[ #r #_ #H0 -p
  elim (sub_inv_gen … H0) -H0 #H0 destruct // -HX
  elim (psub_inv_refs_dx … H0)
| #x #T #Hp #H0
  elim (sub_inv_gen … H0) -H0 #H0 destruct //
  lapply (psub_inv_nabs_dx … H0) -H0 #H0
  /4 width=3 by psub_nabs, sub_step/
| #T #V #Hp #H0
  elim (sub_inv_gen … H0) -H0 #H0 destruct //
  elim (psub_inv_appl_dx … H0) -H0 #H0
  /4 width=3 by sub_step, psub_appl, psub_side/
| #T #Hp #H0
  elim (sub_inv_gen … H0) -H0 #H0 destruct //
  lapply (psub_inv_aabs_dx … H0) -H0 #H0
  /4 width=3 by psub_aabs, sub_step/
]
qed-.

theorem sub_psub_trans (U) (X) (T): U ⊆ X → X ⊂ T → U ⊂ T.
#U #X #T #UX * -T
/3 width=3 by psub_nabs, psub_appl, psub_side, psub_aabs, sub_trans/
qed-.

theorem psub_trans: Transitive … psub.
/3 width=3 by sub_step, sub_psub_trans/
qed-.

theorem psub_sub_trans (U) (X) (T): U ⊂ X → X ⊆ T → U ⊂ T.
#U #X #T #UX * -T
/2 width=3 by psub_trans/
qed-.

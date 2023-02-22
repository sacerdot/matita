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

include "ground_2/relocation/trace_at.ma".

(* RELOCATION TRACE *********************************************************)

inductive sle: relation trace ≝
| sle_empty: sle (◊) (◊)
| sle_true : ∀t1,t2. sle t1 t2 → sle (Ⓣ @ t1) (Ⓣ @ t2)
| sle_false: ∀t1,t2,b. sle t1 t2 → sle (Ⓕ @ t1) (b @ t2)
.

interpretation
   "inclusion (trace)"
   'subseteq t1 t2 = (sle t1 t2).

(* Basic properties *********************************************************)

(* Basic forward lemmas *****************************************************)

lemma sle_fwd_length: ∀t1,t2. t1 ⊆ t2 → |t1| = |t2|.
#t1 #t2 #H elim H -t1 -t2 //
qed-.

lemma sle_fwd_colength: ∀t1,t2. t1 ⊆ t2 → ∥t1∥ ≤ ∥t2∥.
#t1 #t2 #H elim H -t1 -t2 /2 width=1 by le_S_S/
#t1 #t2 * /2 width=1 by le_S/
qed-.

(* Inversion lemmas on application ******************************************)

lemma sle_inv_at: ∀t1,t2. t1 ⊆ t2 →
                  ∀i,i1,i2. @⦃i, t1⦄ ≡ i1 → @⦃i, t2⦄  ≡ i2 → i2 ≤ i1.
#t1 #t2 #H elim H -t1 -t2
[ #i #i1 #i2 #_ #H2 elim (at_inv_empty … H2) -H2 //
| #t1 #t2 #_ #IH #i #i1 #i2 #H0 #H2 elim (at_inv_true … H2) -H2 * //
  #j1 #j2 #H1 #H2 #Hj destruct elim (at_inv_true_succ_sn … H0) -H0
  /3 width=3 by le_S_S/
| #t1 #t2 * #_ #IH #i #i1 #i2 #H0 #H2
  [ elim (at_inv_true … H2) -H2 * //
    #j #j2 #H1 #H2 #Hj2 destruct elim (at_inv_false … H0) -H0
    #j1 #H #Hj1 destruct elim (at_monotonic … Hj1 j) -Hj1 //
    #x #H1x #H2x @le_S_S /4 width=3 by lt_to_le, le_to_lt_to_lt/ (**) (* full auto too slow *)
  | elim (at_inv_false … H2) elim (at_inv_false … H0) -H0 -H2
    /3 width=3 by le_S_S/
  ]
]  
qed-.

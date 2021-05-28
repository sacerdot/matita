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

include "ground/relocation/gr_coafter_eq.ma".

(* RELATIONAL CO-COMPOSITION FOR GENERIC RELOCATION MAPS ***********************************************************)

(* Main inversion lemmas ****************************************************)

(*** coafter_mono *)
corec theorem gr_coafter_mono:
              ∀f1,f2,x,y. f1 ~⊚ f2 ≘ x → f1 ~⊚ f2 ≘ y → x ≡ y.
#f1 #f2 #x #y * -f1 -f2 -x
#f1 #f2 #x #g1 [1,2: #g2 ] #g #Hx #H1 [1,2: #H2 ] #H0x #Hy
[ cases (gr_coafter_inv_push_bi … Hy … H1 H2) -g1 -g2 /3 width=8 by gr_eq_push/
| cases (gr_coafter_inv_push_next … Hy … H1 H2) -g1 -g2 /3 width=8 by gr_eq_next/
| cases (gr_coafter_inv_next_sn … Hy … H1) -g1 /3 width=8 by gr_eq_push/
]
qed-.

(*** coafter_mono_eq *)
lemma gr_coafter_mono_eq:
      ∀f1,f2,f. f1 ~⊚ f2 ≘ f → ∀g1,g2,g. g1 ~⊚ g2 ≘ g →
      f1 ≡ g1 → f2 ≡ g2 → f ≡ g.
/4 width=4 by gr_coafter_mono, gr_coafter_eq_repl_back_dx, gr_coafter_eq_repl_back_sn/ qed-.

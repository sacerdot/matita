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

include "basic_2/relocation/lifts_lifts.ma".
include "basic_2/relocation/lifts_vector.ma".

(* GENERIC RELOCATION FOR TERM VECTORS *************************************)

(* Main properties **********************************************************)

(* Basic_1: includes: lifts_inj *)
theorem liftsv_inj: ∀T1c,Us,f. ⬆*[f] T1c ≡ Us →
                    ∀T2c. ⬆*[f] T2c ≡ Us → T1c = T2c.
#T1c #Us #f #H elim H -T1c -Us
[ #T2c #H >(liftsv_inv_nil2 … H) -H //
| #T1c #Us #T1 #U #HT1U #_ #IHT1Us #X #H destruct
  elim (liftsv_inv_cons2 … H) -H #T2 #T2c #HT2U #HT2Us #H destruct
  >(lifts_inj … HT1U … HT2U) -U /3 width=1 by eq_f/
]
qed-.

(* Basic_2A1: includes: liftv_mono *)
theorem liftsv_mono: ∀Ts,U1c,f. ⬆*[f] Ts ≡ U1c →
                     ∀U2c. ⬆*[f] Ts ≡ U2c → U1c = U2c.
#Ts #U1c #f #H elim H -Ts -U1c
[ #U2c #H >(liftsv_inv_nil1 … H) -H //
| #Ts #U1c #T #U1 #HTU1 #_ #IHTU1c #X #H destruct
  elim (liftsv_inv_cons1 … H) -H #U2 #U2c #HTU2 #HTU2c #H destruct
  >(lifts_mono … HTU1 … HTU2) -T /3 width=1 by eq_f/
]
qed-.

(* Basic_1: includes: lifts1_xhg (right to left) *)
(* Basic_2A1: includes: liftsv_liftv_trans_le *)
theorem liftsv_trans: ∀T1c,Ts,f1. ⬆*[f1] T1c ≡ Ts → ∀T2c,f2. ⬆*[f2] Ts ≡ T2c →
                      ∀f. f2 ⊚ f1 ≡ f → ⬆*[f] T1c ≡ T2c.
#T1c #Ts #f1 #H elim H -T1c -Ts
[ #T2c #f2 #H >(liftsv_inv_nil1 … H) -T2c /2 width=3 by liftsv_nil/
| #T1c #Ts #T1 #T #HT1 #_ #IHT1c #X #f2 #H elim (liftsv_inv_cons1 … H) -H
  #T2 #T2c #HT2 #HT2c #H destruct /3 width=6 by lifts_trans, liftsv_cons/
]
qed-.

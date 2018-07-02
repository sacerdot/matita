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

include "static_2/relocation/lifts_lifts.ma".
include "static_2/relocation/lifts_vector.ma".

(* GENERIC RELOCATION FOR TERM VECTORS *************************************)

(* Main properties **********************************************************)

(* Basic_1: includes: lifts_inj *)
theorem liftsv_inj: ∀f,T1s,Us. ⬆*[f] T1s ≘ Us →
                    ∀T2s. ⬆*[f] T2s ≘ Us → T1s = T2s.
#f #T1s #Us #H elim H -T1s -Us
[ #T2s #H >(liftsv_inv_nil2 … H) -H //
| #T1s #Us #T1 #U #HT1U #_ #IHT1Us #X #H destruct
  elim (liftsv_inv_cons2 … H) -H #T2 #T2s #HT2U #HT2Us #H destruct
  >(lifts_inj … HT1U … HT2U) -U /3 width=1 by eq_f/
]
qed-.

(* Basic_2A1: includes: liftv_mono *)
theorem liftsv_mono: ∀f,Ts,U1s. ⬆*[f] Ts ≘ U1s →
                     ∀U2s. ⬆*[f] Ts ≘ U2s → U1s = U2s.
#f #Ts #U1s #H elim H -Ts -U1s
[ #U2s #H >(liftsv_inv_nil1 … H) -H //
| #Ts #U1s #T #U1 #HTU1 #_ #IHTU1s #X #H destruct
  elim (liftsv_inv_cons1 … H) -H #U2 #U2s #HTU2 #HTU2s #H destruct
  >(lifts_mono … HTU1 … HTU2) -T /3 width=1 by eq_f/
]
qed-.

(* Basic_1: includes: lifts1_xhg (right to left) *)
(* Basic_2A1: includes: liftsv_liftv_trans_le *)
theorem liftsv_trans: ∀f1,T1s,Ts. ⬆*[f1] T1s ≘ Ts → ∀T2s,f2. ⬆*[f2] Ts ≘ T2s →
                      ∀f. f2 ⊚ f1 ≘ f → ⬆*[f] T1s ≘ T2s.
#f1 #T1s #Ts #H elim H -T1s -Ts
[ #T2s #f2 #H >(liftsv_inv_nil1 … H) -T2s /2 width=3 by liftsv_nil/
| #T1s #Ts #T1 #T #HT1 #_ #IHT1s #X #f2 #H elim (liftsv_inv_cons1 … H) -H
  #T2 #T2s #HT2 #HT2s #H destruct /3 width=6 by lifts_trans, liftsv_cons/
]
qed-.

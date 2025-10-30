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

include "ground/lib/stream_eq.ma".

(* EXTENSIONAL EQUIVALENCE FOR STREAMS **************************************)

(* Main constructions *******************************************************)

corec theorem stream_eq_trans (A):
              Transitive … (stream_eq A).
#t1 #t * -t1 -t
#a1 #a #t1 #t * #Ht1 * #a2 #t2 #H
cases (stream_eq_inv_cons_bi A … H) -H -a
/3 width=7 by stream_eq_cons/
qed-.

theorem stream_eq_canc_sx (A):
        ∀t,t1,t2. t ≗ t1 → t ≗ t2 → t1 ≗{A} t2.
/3 width=3 by stream_eq_trans, stream_eq_sym/ qed-.

theorem stream_eq_canc_dx (A):
        ∀t,t1,t2. t1 ≗ t → t2 ≗ t → t1 ≗{A} t2.
/3 width=3 by stream_eq_trans, stream_eq_sym/ qed-.

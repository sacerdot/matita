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

include "basic_2/notation/relations/predtysnstar_4.ma".
include "basic_2/relocation/lex.ma".
include "basic_2/rt_computation/cpxs_ext.ma".

(* UNBOUND PARALLEL RT-COMPUTATION FOR LOCAL ENVIRONMENTS *******************)

definition lpxs: ∀h. relation3 genv lenv lenv ≝
                 λh,G. lex (cpxs h G).

interpretation
   "unbound parallel rt-computation (local environment)"
   'PRedTySnStar h G L1 L2 = (lpxs h G L1 L2).

(* Basic properties *********************************************************)

lemma lpxs_refl: ∀h,G. reflexive … (lpxs h G).
/2 width=1 by lex_refl/ qed.

(* Basic inversion lemmas ***************************************************)

lemma lpxs_inv_bind_sn: ∀h,G,I1,L2,K1. ⦃G, K1.ⓘ{I1}⦄ ⊢⬈*[h] L2 →
                        ∃∃I2,K2. ⦃G, K1⦄ ⊢⬈*[h] K2 & ⦃G, K1⦄ ⊢ I1 ⬈*[h] I2 & L2 = K2.ⓘ{I2}.
/2 width=1 by lex_inv_bind_sn/ qed-.

lemma lpxs_inv_pair_sn: ∀h,G,I,L2,K1,V1. ⦃G, K1.ⓑ{I}V1⦄ ⊢⬈*[h] L2 →
                        ∃∃K2,V2. ⦃G, K1⦄ ⊢⬈*[h] K2 & ⦃G, K1⦄ ⊢ V1 ⬈*[h] V2 & L2 = K2.ⓑ{I}V2.
#h #G #I #L2 #K1 #V1 #H
elim (lpxs_inv_bind_sn … H) -H #Y #K2 #HK12 #H0 #H destruct
elim (ext2_inv_pair_sn … H0) -H0 #V2 #HV12 #H destruct
/2 width=5 by ex3_2_intro/
qed-.

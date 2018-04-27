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

include "basic_2/s_computation/fqus.ma".
include "basic_2/rt_computation/csx_lsubr.ma".

(* STRONGLY NORMALIZING TERMS FOR UNBOUND PARALLEL RT-TRANSITION ************)

(* Properties with extended supclosure **************************************)

lemma csx_fqu_conf: ∀h,o,b,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐[b] ⦃G2, L2, T2⦄ →
                    ⦃G1, L1⦄ ⊢ ⬈*[h, o] 𝐒⦃T1⦄ → ⦃G2, L2⦄ ⊢ ⬈*[h, o] 𝐒⦃T2⦄.
#h #o #b #G1 #G2 #L1 #L2 #T1 #T2 #H elim H -G1 -G2 -L1 -L2 -T1 -T2
[ /3 width=5 by csx_inv_lref_pair, drops_refl/
| /2 width=3 by csx_fwd_pair_sn/
| /2 width=2 by csx_fwd_bind_dx/
| /2 width=4 by csx_fwd_bind_dx_unit/
| /2 width=3 by csx_fwd_flat_dx/
| /4 width=7 by csx_inv_lifts, drops_refl, drops_drop/
]
qed-.

lemma csx_fquq_conf: ∀h,o,b,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐⸮[b] ⦃G2, L2, T2⦄ →
                     ⦃G1, L1⦄ ⊢ ⬈*[h, o] 𝐒⦃T1⦄ → ⦃G2, L2⦄ ⊢ ⬈*[h, o] 𝐒⦃T2⦄.
#h #o #b #G1 #G2 #L1 #L2 #T1 #T2 * /2 width=6 by csx_fqu_conf/
* #HG #HL #HT destruct //
qed-.

lemma csx_fqup_conf: ∀h,o,b,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐+[b] ⦃G2, L2, T2⦄ →
                     ⦃G1, L1⦄ ⊢ ⬈*[h, o] 𝐒⦃T1⦄ → ⦃G2, L2⦄ ⊢ ⬈*[h, o] 𝐒⦃T2⦄.
#h #o #b #G1 #G2 #L1 #L2 #T1 #T2 #H @(fqup_ind … H) -G2 -L2 -T2
/3 width=6 by csx_fqu_conf/
qed-.

lemma csx_fqus_conf: ∀h,o,b,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐*[b] ⦃G2, L2, T2⦄ →
                     ⦃G1, L1⦄ ⊢ ⬈*[h, o] 𝐒⦃T1⦄ → ⦃G2, L2⦄ ⊢ ⬈*[h, o] 𝐒⦃T2⦄.
#h #o #b #G1 #G2 #L1 #L2 #T1 #T2 #H @(fqus_ind … H) -H
/3 width=6 by csx_fquq_conf/
qed-.

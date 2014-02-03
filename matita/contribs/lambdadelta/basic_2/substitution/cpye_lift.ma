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

include "basic_2/relocation/cny_lift.ma".
include "basic_2/substitution/fqup.ma".
include "basic_2/substitution/cpys_lift.ma".
include "basic_2/substitution/cpye.ma".

(* EVALUATION FOR CONTEXT-SENSITIVE EXTENDED SUBSTITUTION ON TERMS **********)

lemma cpye_subst: ∀I,G,L,K,V1,V2,W2,i,d,e. d ≤ yinj i → i < d + e →
                  ⇩[i] L ≡ K.ⓑ{I}V1 → ⦃G, K⦄ ⊢ V1 ▶*[O, ⫰(d+e-i)] 𝐍⦃V2⦄ →
                  ⇧[O, i+1] V2 ≡ W2 → ⦃G, L⦄ ⊢ #i ▶*[d, e] 𝐍⦃W2⦄.
#I #G #L #K #V1 #V2 #W2 #i #d #e #Hdi #Hide #HLK *
/4 width=13 by cpys_subst, cny_subst_aux, ldrop_fwd_drop2, conj/
qed.

lemma cpys_total: ∀G,L,T1,d,e. ∃T2. ⦃G, L⦄ ⊢ T1 ▶*[d, e] 𝐍⦃T2⦄.
#G #L #T1 @(fqup_wf_ind_eq … G L T1) -G -L -T1
#Z #Y #X #IH #G #L * *
[ #k #HG #HL #HT #d #e destruct -IH /2 width=2 by ex_intro/
| #i #HG #HL #HT #d #e destruct
  elim (ylt_split i d) /3 width=2 by cpye_skip, ex_intro/
  elim (ylt_split i (d+e)) /3 width=2 by cpye_top, ex_intro/
  elim (lt_or_ge i (|L|)) /3 width=2 by cpye_free, ex_intro/
  #Hi #Hide #Hdi elim (ldrop_O1_lt L i) // -Hi
  #I #K #V1 #HLK elim (IH G K V1 … 0 (⫰(d+e-i))) -IH /2 width=2 by fqup_lref/
  #V2 elim (lift_total V2 0 (i+1)) /3 width=8 by ex_intro, cpye_subst/
| #p #HG #HL #HT #d #e destruct -IH /2 width=2 by ex_intro/
| #a #I #V1 #T1 #HG #HL #HT #d #e destruct
  elim (IH G L V1 … d e) // elim (IH G (L.ⓑ{I}V1) T1 … (⫯d) e) //
  /3 width=2 by cpye_bind, ex_intro/
| #I #V1 #T1 #HG #HL #HT #d #e destruct
  elim (IH G L V1 … d e) // elim (IH G L T1 … d e) //
  /3 width=2 by cpye_flat, ex_intro/
]
qed-.

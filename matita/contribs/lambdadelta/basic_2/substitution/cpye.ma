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

include "basic_2/notation/relations/psubsteval_6.ma".
include "basic_2/relocation/cny.ma".
include "basic_2/substitution/cpys.ma".

(* EVALUATION FOR CONTEXT-SENSITIVE EXTENDED SUBSTITUTION ON TERMS **********)

definition cpye: ynat → ynat → relation4 genv lenv term term ≝
                 λd,e,G,L,T1,T2. ⦃G, L⦄ ⊢ T1 ▶*[d, e] T2 ∧ ⦃G, L⦄ ⊢ ▶[d, e] 𝐍⦃T2⦄.

interpretation "evaluation for context-sensitive extended substitution (term)"
   'PSubstEval G L T1 T2 d e = (cpye d e G L T1 T2).

(* Basic_properties *********************************************************)

lemma cpye_sort: ∀G,L,d,e,k. ⦃G, L⦄ ⊢ ⋆k ▶*[d, e] 𝐍⦃⋆k⦄.
/3 width=5 by cny_sort, conj/ qed.

lemma cpye_free: ∀G,L,d,e,i. |L| ≤ i → ⦃G, L⦄ ⊢ #i ▶*[d, e] 𝐍⦃#i⦄.
/3 width=6 by cny_lref_free, conj/ qed.

lemma cpye_top: ∀G,L,d,e,i. d + e ≤ yinj i → ⦃G, L⦄ ⊢ #i ▶*[d, e] 𝐍⦃#i⦄.
/3 width=6 by cny_lref_top, conj/ qed.

lemma cpye_skip: ∀G,L,d,e,i. yinj i < d → ⦃G, L⦄ ⊢ #i ▶*[d, e] 𝐍⦃#i⦄.
/3 width=6 by cny_lref_skip, conj/ qed.

lemma cpye_gref: ∀G,L,d,e,p. ⦃G, L⦄ ⊢ §p ▶*[d, e] 𝐍⦃§p⦄.
/3 width=5 by cny_gref, conj/ qed.

lemma cpye_bind: ∀G,L,V1,V2,d,e. ⦃G, L⦄ ⊢ V1 ▶*[d, e] 𝐍⦃V2⦄ →
                 ∀I,T1,T2. ⦃G, L.ⓑ{I}V1⦄ ⊢ T1 ▶*[⫯d, e] 𝐍⦃T2⦄ →
                 ∀a. ⦃G, L⦄ ⊢ ⓑ{a,I}V1.T1 ▶*[d, e] 𝐍⦃ⓑ{a,I}V2.T2⦄.
#G #L #V1 #V2 #d #e * #HV12 #HV2 #I #T1 #T2 *
/5 width=8 by cpys_bind, cny_bind, lsuby_cny_conf, lsuby_succ, conj/
qed.

lemma cpye_flat: ∀G,L,V1,V2,d,e. ⦃G, L⦄ ⊢ V1 ▶*[d, e] 𝐍⦃V2⦄ →
                 ∀T1,T2. ⦃G, L⦄ ⊢ T1 ▶*[d, e] 𝐍⦃T2⦄ →
                 ∀I. ⦃G, L⦄ ⊢ ⓕ{I}V1.T1 ▶*[d, e] 𝐍⦃ⓕ{I}V2.T2⦄.
#G #L #V1 #V2 #d #e * #HV12 #HV2 #T1 #T2 *
/3 width=7 by cpys_flat, cny_flat, conj/
qed.

(* Basic inversion lemmas ***************************************************)

lemma 
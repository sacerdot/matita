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

include "Basic_2/grammar/lenv_length.ma".

(* LOCAL ENVIRONMENT REFINEMENT FOR SUBSTITUTION ****************************)

inductive lsubs: nat → nat → relation lenv ≝
| lsubs_sort: ∀d,e. lsubs d e (⋆) (⋆)
| lsubs_OO:   ∀L1,L2. lsubs 0 0 L1 L2
| lsubs_abbr: ∀L1,L2,V,e. lsubs 0 e L1 L2 →
              lsubs 0 (e + 1) (L1. 𝕓{Abbr} V) (L2.𝕓{Abbr} V)
| lsubs_abst: ∀L1,L2,I,V1,V2,e. lsubs 0 e L1 L2 →
              lsubs 0 (e + 1) (L1. 𝕓{Abst} V1) (L2.𝕓{I} V2)
| lsubs_skip: ∀L1,L2,I1,I2,V1,V2,d,e.
              lsubs d e L1 L2 → lsubs (d + 1) e (L1. 𝕓{I1} V1) (L2. 𝕓{I2} V2)
.

interpretation "local environment refinement (substitution)" 'SubEq L1 d e L2 = (lsubs d e L1 L2).

definition lsubs_conf: ∀S. (lenv → relation S) → Prop ≝ λS,R.
                       ∀L1,s1,s2. R L1 s1 s2 →
                       ∀L2,d,e. L1 [d, e] ≼ L2 → R L2 s1 s2.

(* Basic properties *********************************************************)

lemma TC_lsubs_conf: ∀S,R. lsubs_conf S R → lsubs_conf S (λL. (TC … (R L))).
#S #R #HR #L1 #s1 #s2 #H elim H -H s2
[ /3 width=5/
| #s #s2 #_ #Hs2 #IHs1 #L2 #d #e #HL12
  lapply (HR … Hs2 … HL12) -HR Hs2 HL12 /3/
]
qed.

lemma lsubs_bind_eq: ∀L1,L2,e. L1 [0, e] ≼ L2 → ∀I,V.
                     L1. 𝕓{I} V [0, e + 1] ≼ L2.𝕓{I} V.
#L1 #L2 #e #HL12 #I #V elim I -I /2/
qed.

lemma lsubs_refl: ∀d,e,L. L [d, e] ≼ L.
#d elim d -d
[ #e elim e -e // #e #IHe #L elim L -L /2/
| #d #IHd #e #L elim L -L /2/
]
qed.

lemma lsubs_skip_lt: ∀L1,L2,d,e. L1 [d - 1, e] ≼ L2 → 0 < d →
                     ∀I1,I2,V1,V2. L1. 𝕓{I1} V1 [d, e] ≼ L2. 𝕓{I2} V2.

#L1 #L2 #d #e #HL12 #Hd >(plus_minus_m_m d 1) /2/
qed.

(* Basic inversion lemmas ***************************************************)

(* Basic forward lemmas ***************************************************)

fact lsubs_fwd_length_full1_aux: ∀L1,L2,d,e. L1 [d, e] ≼ L2 →
                                 d = 0 → e = |L1| → |L1| ≤ |L2|.
#L1 #L2 #d #e #H elim H -H L1 L2 d e; normalize
[ //
| /2/
| /3/
| /3/
| #L1 #L2 #_ #_ #_ #_ #d #e #_ #_ #H
  elim (plus_S_eq_O_false … H)
]   
qed.

lemma lsubs_fwd_length_full1: ∀L1,L2. L1 [0, |L1|] ≼ L2 → |L1| ≤ |L2|.
/2 width=5/ qed-.

fact lsubs_fwd_length_full2_aux: ∀L1,L2,d,e. L1 [d, e] ≼ L2 →
                                 d = 0 → e = |L2| → |L2| ≤ |L1|.
#L1 #L2 #d #e #H elim H -H L1 L2 d e; normalize
[ //
| /2/
| /3/
| /3/
| #L1 #L2 #_ #_ #_ #_ #d #e #_ #_ #H
  elim (plus_S_eq_O_false … H)
]   
qed.

lemma lsubs_fwd_length_full2: ∀L1,L2. L1 [0, |L2|] ≼ L2 → |L2| ≤ |L1|.
/2 width=5/ qed-.

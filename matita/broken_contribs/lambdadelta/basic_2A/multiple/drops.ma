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

include "ground/xoa/ex_4_3.ma".
include "ground/relocation/mr2_minus.ma".
include "basic_2A/notation/relations/rdropstar_3.ma".
include "basic_2A/notation/relations/rdropstar_4.ma".
include "basic_2A/substitution/drop.ma".
include "basic_2A/multiple/lifts_vector.ma".

(* ITERATED LOCAL ENVIRONMENT SLICING ***************************************)

inductive drops (s:bool): mr2 → relation lenv ≝
| drops_nil : ∀L. drops s (𝐞) L L
| drops_cons: ∀L1,L,L2,cs,l,m.
              drops s cs L1 L → ⬇[s, l, m] L ≡ L2 → drops s (❨l, m❩◗ cs) L1 L2
.

interpretation "iterated slicing (local environment) abstract"
   'RDropStar s cs T1 T2 = (drops s cs T1 T2).
(*
interpretation "iterated slicing (local environment) general"
   'RDropStar des T1 T2 = (drops true des T1 T2).
*)

definition d_liftable1: relation2 lenv term → predicate bool ≝
                        λR,s. ∀K,T. R K T → ∀L,l,m. ⬇[s, l, m] L ≡ K →
                        ∀U. ⬆[l, m] T ≡ U → R L U.

definition d_liftables1: relation2 lenv term → predicate bool ≝
                         λR,s. ∀L,K,cs. ⬇*[s, cs] L ≡ K →
                         ∀T,U. ⬆*[cs] T ≡ U → R K T → R L U.

definition d_liftables1_all: relation2 lenv term → predicate bool ≝
                             λR,s. ∀L,K,cs. ⬇*[s, cs] L ≡ K →
                             ∀Ts,Us. ⬆*[cs] Ts ≡ Us → 
                             all … (R K) Ts → all … (R L) Us.

(* Basic inversion lemmas ***************************************************)

fact drops_inv_nil_aux: ∀L1,L2,s,cs. ⬇*[s, cs] L1 ≡ L2 → cs = 𝐞 → L1 = L2.
#L1 #L2 #s #cs * -L1 -L2 -cs //
#L1 #L #L2 #l #m #cs #_ #_ #H destruct
qed-.

lemma drops_inv_nil: ∀L1,L2,s. ⬇*[s, 𝐞] L1 ≡ L2 → L1 = L2.
/2 width=4 by drops_inv_nil_aux/ qed-.

fact drops_inv_cons_aux: ∀L1,L2,s,cs. ⬇*[s, cs] L1 ≡ L2 →
                         ∀l,m,tl. cs = ❨l, m❩◗ tl →
                         ∃∃L. ⬇*[s, tl] L1 ≡ L & ⬇[s, l, m] L ≡ L2.
#L1 #L2 #s #cs * -L1 -L2 -cs
[ #L #l #m #tl #H destruct
| #L1 #L #L2 #cs #l #m #HT1 #HT2 #l0 #m0 #tl #H destruct
  /2 width=3 by ex2_intro/
]
qed-.

lemma drops_inv_cons: ∀L1,L2,s,l,m,cs. ⬇*[s, ❨l, m❩◗ cs] L1 ≡ L2 →
                      ∃∃L. ⬇*[s, cs] L1 ≡ L & ⬇[s, l, m] L ≡ L2.
/2 width=3 by drops_inv_cons_aux/ qed-.

lemma drops_inv_skip2: ∀I,s,cs,cs2,i. cs ▭ i ≘ cs2 →
                       ∀L1,K2,V2. ⬇*[s, cs2] L1 ≡ K2. ⓑ{I} V2 →
                       ∃∃K1,V1,cs1. cs + 1 ▭ i + 1 ≘ cs1 + 1 &
                                     ⬇*[s, cs1] K1 ≡ K2 &
                                     ⬆*[cs1] V2 ≡ V1 &
                                     L1 = K1. ⓑ{I} V1.
#I #s #cs #cs2 #i #H elim H -cs -cs2 -i
[ #i #L1 #K2 #V2 #H
  >(drops_inv_nil … H) -L1 /2 width=7 by lifts_nil, minuss_nil, ex4_3_intro, drops_nil/
| #cs #cs2 #l #m #i #Hil #_ #IHcs2 #L1 #K2 #V2 #H
  elim (drops_inv_cons … H) -H #L #HL1 #H
  elim (drop_inv_skip2 … H) -H /2 width=1 by lt_plus_to_minus_r/ #K #V >minus_plus #HK2 #HV2 #H destruct
  elim (IHcs2 … HL1) -IHcs2 -HL1 #K1 #V1 #cs1 #Hcs1 #HK1 #HV1 #X destruct
  @(ex4_3_intro … K1 V1 … ) // [3,4: /2 width=7 by lifts_cons, drops_cons/ | skip ]
  normalize >plus_minus /3 width=1 by minuss_lt, lt_minus_to_plus/ (**) (* explicit constructors *)
| #cs #cs2 #l #m #i #Hil #_ #IHcs2 #L1 #K2 #V2 #H
  elim (IHcs2 … H) -IHcs2 -H #K1 #V1 #cs1 #Hcs1 #HK1 #HV1 #X destruct
  /4 width=7 by minuss_ge, ex4_3_intro, le_S_S/
]
qed-.

(* Basic properties *********************************************************)

lemma drops_skip: ∀L1,L2,s,cs. ⬇*[s, cs] L1 ≡ L2 → ∀V1,V2. ⬆*[cs] V2 ≡ V1 →
                  ∀I. ⬇*[s, cs + 1] L1.ⓑ{I}V1 ≡ L2.ⓑ{I}V2.
#L1 #L2 #s #cs #H elim H -L1 -L2 -cs
[ #L #V1 #V2 #HV12 #I
  >(lifts_inv_nil … HV12) -HV12 //
| #L1 #L #L2 #cs #l #m #_ #HL2 #IHL #V1 #V2 #H #I
  elim (lifts_inv_cons … H) -H /3 width=5 by drop_skip, drops_cons/
].
qed.

lemma d1_liftable_liftables: ∀R,s. d_liftable1 R s → d_liftables1 R s.
#R #s #HR #L #K #cs #H elim H -L -K -cs
[ #L #T #U #H #HT <(lifts_inv_nil … H) -H //
| #L1 #L #L2 #cs #l #m #_ #HL2 #IHL #T2 #T1 #H #HLT2
  elim (lifts_inv_cons … H) -H /3 width=10 by/
]
qed.

lemma d1_liftables_liftables_all: ∀R,s. d_liftables1 R s → d_liftables1_all R s.
#R #s #HR #L #K #cs #HLK #Ts #Us #H elim H -Ts -Us normalize //
#Ts #Us #T #U #HTU #_ #IHTUs * /3 width=7 by conj/
qed.

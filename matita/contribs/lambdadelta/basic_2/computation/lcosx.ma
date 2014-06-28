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

include "basic_2/notation/relations/cosn_5.ma".
include "basic_2/computation/lsx.ma".

(* SN EXTENDED STRONGLY CONORMALIZING LOCAL ENVIRONMENTS ********************)

inductive lcosx (h) (g) (G): relation2 ynat lenv ≝
| lcosx_sort: ∀d. lcosx h g G d (⋆)
| lcosx_skip: ∀I,L,T. lcosx h g G 0 L → lcosx h g G 0 (L.ⓑ{I}T)
| lcosx_pair: ∀I,L,T,d. G ⊢ ⬊*[h, g, T, d] L →
              lcosx h g G d L → lcosx h g G (⫯d) (L.ⓑ{I}T)
.

interpretation
   "sn extended strong conormalization (local environment)"
   'CoSN h g d G L = (lcosx h g G d L).

(* Basic properties *********************************************************)

lemma lcosx_O: ∀h,g,G,L. G ⊢ ~⬊*[h, g, 0] L.
#h #g #G #L elim L /2 width=1 by lcosx_skip/
qed.

lemma lcosx_drop_trans_lt: ∀h,g,G,L,d. G ⊢ ~⬊*[h, g, d] L →
                            ∀I,K,V,i. ⇩[i] L ≡ K.ⓑ{I}V → i < d →
                            G ⊢ ~⬊*[h, g, ⫰(d-i)] K ∧ G ⊢ ⬊*[h, g, V, ⫰(d-i)] K.
#h #g #G #L #d #H elim H -L -d
[ #d #J #K #V #i #H elim (drop_inv_atom1 … H) -H #H destruct
| #I #L #T #_ #_ #J #K #V #i #_ #H elim (ylt_yle_false … H) -H //
| #I #L #T #d #HT #HL #IHL #J #K #V #i #H #Hid
  elim (drop_inv_O1_pair1 … H) -H * #Hi #HLK destruct
  [ >ypred_succ /2 width=1 by conj/
  | lapply (ylt_pred … Hid ?) -Hid /2 width=1 by ylt_inj/ >ypred_succ #Hid
    elim (IHL … HLK ?) -IHL -HLK <yminus_inj >yminus_SO2 //
    <(ypred_succ d) in ⊢ (%→%→?); >yminus_pred /2 width=1 by ylt_inj, conj/
  ]
]
qed-.

(* Basic inversion lemmas ***************************************************)

fact lcosx_inv_succ_aux: ∀h,g,G,L,x. G ⊢ ~⬊*[h, g, x] L → ∀d. x = ⫯d →
                         L = ⋆ ∨
                         ∃∃I,K,V. L = K.ⓑ{I}V & G ⊢ ~⬊*[h, g, d] K &
                                  G ⊢ ⬊*[h, g, V, d] K.
#h #g #G #L #d * -L -d /2 width=1 by or_introl/
[ #I #L #T #_ #x #H elim (ysucc_inv_O_sn … H)
| #I #L #T #d #HT #HL #x #H <(ysucc_inj … H) -x
  /3 width=6 by ex3_3_intro, or_intror/
]
qed-.

lemma lcosx_inv_succ: ∀h,g,G,L,d. G ⊢ ~⬊*[h, g, ⫯d] L → L = ⋆ ∨
                      ∃∃I,K,V. L = K.ⓑ{I}V & G ⊢ ~⬊*[h, g, d] K &
                               G ⊢ ⬊*[h, g, V, d] K.
/2 width=3 by lcosx_inv_succ_aux/ qed-.

lemma lcosx_inv_pair: ∀h,g,I,G,L,T,d. G ⊢ ~⬊*[h, g, ⫯d] L.ⓑ{I}T →
                      G ⊢ ~⬊*[h, g, d] L ∧ G ⊢ ⬊*[h, g, T, d] L.
#h #g #I #G #L #T #d #H elim (lcosx_inv_succ … H) -H
[ #H destruct
| * #Z #Y #X #H destruct /2 width=1 by conj/
]
qed-.

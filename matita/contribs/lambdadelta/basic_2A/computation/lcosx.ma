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

include "basic_2A/notation/relations/cosn_5.ma".
include "basic_2A/computation/lsx.ma".

(* SN EXTENDED STRONGLY CONORMALIZING LOCAL ENVIRONMENTS ********************)

inductive lcosx (h) (g) (G): relation2 ynat lenv ≝
| lcosx_sort: ∀l. lcosx h g G l (⋆)
| lcosx_skip: ∀I,L,T. lcosx h g G 0 L → lcosx h g G 0 (L.ⓑ{I}T)
| lcosx_pair: ∀I,L,T,l. G ⊢ ⬊*[h, g, T, l] L →
              lcosx h g G l L → lcosx h g G (⫯l) (L.ⓑ{I}T)
.

interpretation
   "sn extended strong conormalization (local environment)"
   'CoSN h g l G L = (lcosx h g G l L).

(* Basic properties *********************************************************)

lemma lcosx_O: ∀h,g,G,L. G ⊢ ~⬊*[h, g, 0] L.
#h #g #G #L elim L /2 width=1 by lcosx_skip/
qed.

lemma lcosx_drop_trans_lt: ∀h,g,G,L,l. G ⊢ ~⬊*[h, g, l] L →
                            ∀I,K,V,i. ⬇[i] L ≡ K.ⓑ{I}V → i < l →
                            G ⊢ ~⬊*[h, g, ⫰(l-i)] K ∧ G ⊢ ⬊*[h, g, V, ⫰(l-i)] K.
#h #g #G #L #l #H elim H -L -l
[ #l #J #K #V #i #H elim (drop_inv_atom1 … H) -H #H destruct
| #I #L #T #_ #_ #J #K #V #i #_ #H elim (ylt_yle_false … H) -H //
| #I #L #T #l #HT #HL #IHL #J #K #V #i #H #Hil
  elim (drop_inv_O1_pair1 … H) -H * #Hi #HLK destruct
  [ >ypred_succ /2 width=1 by conj/
  | lapply (ylt_pred … Hil ?) -Hil /2 width=1 by ylt_inj/ >ypred_succ #Hil
    elim (IHL … HLK ?) -IHL -HLK <yminus_inj >yminus_SO2 //
    <(ypred_succ l) in ⊢ (%→%→?); >yminus_pred /2 width=1 by ylt_inj, conj/
  ]
]
qed-.

(* Basic inversion lemmas ***************************************************)

fact lcosx_inv_succ_aux: ∀h,g,G,L,x. G ⊢ ~⬊*[h, g, x] L → ∀l. x = ⫯l →
                         L = ⋆ ∨
                         ∃∃I,K,V. L = K.ⓑ{I}V & G ⊢ ~⬊*[h, g, l] K &
                                  G ⊢ ⬊*[h, g, V, l] K.
#h #g #G #L #l * -L -l /2 width=1 by or_introl/
[ #I #L #T #_ #x #H elim (ysucc_inv_O_sn … H)
| #I #L #T #l #HT #HL #x #H <(ysucc_inj … H) -x
  /3 width=6 by ex3_3_intro, or_intror/
]
qed-.

lemma lcosx_inv_succ: ∀h,g,G,L,l. G ⊢ ~⬊*[h, g, ⫯l] L → L = ⋆ ∨
                      ∃∃I,K,V. L = K.ⓑ{I}V & G ⊢ ~⬊*[h, g, l] K &
                               G ⊢ ⬊*[h, g, V, l] K.
/2 width=3 by lcosx_inv_succ_aux/ qed-.

lemma lcosx_inv_pair: ∀h,g,I,G,L,T,l. G ⊢ ~⬊*[h, g, ⫯l] L.ⓑ{I}T →
                      G ⊢ ~⬊*[h, g, l] L ∧ G ⊢ ⬊*[h, g, T, l] L.
#h #g #I #G #L #T #l #H elim (lcosx_inv_succ … H) -H
[ #H destruct
| * #Z #Y #X #H destruct /2 width=1 by conj/
]
qed-.

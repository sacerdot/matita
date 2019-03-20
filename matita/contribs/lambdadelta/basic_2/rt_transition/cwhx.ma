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

include "basic_2/notation/relations/predtywhead_4.ma".
include "static_2/syntax/item_sh.ma".
include "static_2/syntax/lenv.ma".
include "static_2/syntax/genv.ma".

(* WHD NORMAL TERMS FOR UNBOUND CONTEXT-SENSITIVE PARALLEL RT-TRANSITION ****)

inductive cwhx (h:sh) (G:genv): relation2 lenv term ≝
| cwhx_sort: ∀L,s. cwhx h G L (⋆s)
| cwhx_abst: ∀p,L,W,T. cwhx h G L (ⓛ{p}W.T)
| cwhx_ldef: ∀L,V,T. cwhx h G (L.ⓓV) T → cwhx h G L (-ⓓV.T)
.

interpretation
   "whd normality for unbound context-sensitive parallel rt-transition (term)"
   'PRedTyWHead h G L T = (cwhx h G L T).

(* Basic inversion lemmas ***************************************************)

fact cwhx_inv_lref_aux (h) (G):
                       ∀Y,X. ⦃G,Y⦄ ⊢ ⬈[h] 𝐖𝐇⦃X⦄ →
                       ∀i. X = #i → ⊥.
#h #G #Y #X * - X -Y
[ #L #s #i #H destruct
| #p #L #W #T #i #H destruct
| #L #V #T #_ #i #H destruct
]
qed-.

lemma cwhx_inv_lref (h) (G):
                    ∀L,i. ⦃G,L⦄ ⊢ ⬈[h] 𝐖𝐇⦃#i⦄ → ⊥.
/2 width=7 by cwhx_inv_lref_aux/ qed-.

fact cwhx_inv_gref_aux (h) (G):
                       ∀Y,X. ⦃G,Y⦄ ⊢ ⬈[h] 𝐖𝐇⦃X⦄ →
                       ∀l. X = §l → ⊥.
#h #G #Y #X * - X -Y
[ #L #s #l #H destruct
| #p #L #W #T #l #H destruct
| #L #V #T #_ #l #H destruct
]
qed-.

lemma cwhx_inv_gref (h) (G):
                    ∀L,l. ⦃G,L⦄ ⊢ ⬈[h] 𝐖𝐇⦃§l⦄ → ⊥.
/2 width=7 by cwhx_inv_gref_aux/ qed-.

fact cwhx_inv_abbr_aux (h) (G):
                       ∀Y,X. ⦃G,Y⦄ ⊢ ⬈[h] 𝐖𝐇⦃X⦄ →
                       ∀V,T. X = +ⓓV.T → ⊥.
#h #G #Y #X * - X -Y
[ #L #s #X1 #X2 #H destruct
| #p #L #W #T #X1 #X2 #H destruct
| #L #V #T #_ #X1 #X2 #H destruct
]
qed-.

lemma cwhx_inv_abbr (h) (G):
                    ∀Y,V,T. ⦃G,Y⦄ ⊢ ⬈[h] 𝐖𝐇⦃+ⓓV.T⦄ → ⊥.
/2 width=8 by cwhx_inv_abbr_aux/ qed-.

fact cwhx_inv_ldef_aux (h) (G):
                       ∀Y,X. ⦃G,Y⦄ ⊢ ⬈[h] 𝐖𝐇⦃X⦄ →
                       ∀V,T. X = -ⓓV.T → ⦃G,Y.ⓓV⦄ ⊢ ⬈[h] 𝐖𝐇⦃T⦄.
#h #G #Y #X * - X -Y
[ #L #s #X1 #X2 #H destruct
| #p #L #W #T #X1 #X2 #H destruct
| #L #V #T #HT #X1 #X2 #H destruct //
]
qed-.

lemma cwhx_inv_ldef (h) (G):
                    ∀Y,V,T. ⦃G,Y⦄ ⊢ ⬈[h] 𝐖𝐇⦃-ⓓV.T⦄ → ⦃G,Y.ⓓV⦄ ⊢ ⬈[h] 𝐖𝐇⦃T⦄.
/2 width=3 by cwhx_inv_ldef_aux/ qed-.

fact cwhx_inv_appl_aux (h) (G):
                       ∀Y,X. ⦃G,Y⦄ ⊢ ⬈[h] 𝐖𝐇⦃X⦄ →
                       ∀V,T. X = ⓐV.T → ⊥.
#h #G #Y #X * - X -Y
[ #L #s #X1 #X2 #H destruct
| #p #L #W #T #X1 #X2 #H destruct
| #L #V #T #_ #X1 #X2 #H destruct
]
qed-.

lemma cwhx_inv_appl (h) (G):
                    ∀Y,V,T. ⦃G,Y⦄ ⊢ ⬈[h] 𝐖𝐇⦃ⓐV.T⦄ → ⊥.
/2 width=8 by cwhx_inv_appl_aux/ qed-.

fact cwhx_inv_cast_aux (h) (G):
                       ∀Y,X. ⦃G,Y⦄ ⊢ ⬈[h] 𝐖𝐇⦃X⦄ →
                       ∀U,T. X = ⓝU.T → ⊥.
#h #G #Y #X * - X -Y
[ #L #s #X1 #X2 #H destruct
| #p #L #W #T #X1 #X2 #H destruct
| #L #V #T #_ #X1 #X2 #H destruct
]
qed-.

lemma cwhx_inv_cast (h) (G):
                    ∀Y,U,T. ⦃G,Y⦄ ⊢ ⬈[h] 𝐖𝐇⦃ⓝU.T⦄ → ⊥.
/2 width=8 by cwhx_inv_cast_aux/ qed-.

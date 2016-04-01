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

include "basic_2/notation/relations/supterm_6.ma".
include "basic_2/grammar/lenv.ma".
include "basic_2/grammar/genv.ma".
include "basic_2/relocation/lifts.ma".

(* SUPCLOSURE ***************************************************************)

(* activate genv *)
inductive fqu: tri_relation genv lenv term ≝
| fqu_lref_O : ∀I,G,L,V. fqu G (L.ⓑ{I}V) (#0) G L V
| fqu_pair_sn: ∀I,G,L,V,T. fqu G L (②{I}V.T) G L V
| fqu_bind_dx: ∀p,I,G,L,V,T. fqu G L (ⓑ{p,I}V.T) G (L.ⓑ{I}V) T
| fqu_flat_dx: ∀I,G,L,V,T. fqu G L (ⓕ{I}V.T) G L T
| fqu_drop   : ∀I,G,L,V,T,U. ⬆*[1] T ≡ U → fqu G (L.ⓑ{I}V) U G L T
.

interpretation
   "structural successor (closure)"
   'SupTerm G1 L1 T1 G2 L2 T2 = (fqu G1 L1 T1 G2 L2 T2).

(* Basic properties *********************************************************)

lemma fqu_lref_S: ∀I,G,L,V,i. ⦃G, L.ⓑ{I}V, #(⫯i)⦄ ⊐ ⦃G, L, #(i)⦄.
/2 width=1 by fqu_drop/ qed.

(* Basic_2A1: removed theorems 3:
              fqu_drop fqu_drop_lt fqu_lref_S_lt
*)

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

include "ground/lib/star.ma".
include "ground/lib/ltc.ma".

(* LABELLED TRANSITIVE CLOSURE **********************************************)

alias symbol "subseteq" = "relation inclusion". (**)

(* Constructions with contextual transitive closure *************************)

lemma ltc_CTC (C) (A) (i) (f) (B) (R:relation4 C A B B):
              left_identity … f i →
              ∀c. CTC … (λc. R c i) c ⊆ ltc … f … (R c) i.
#C #A #i #f #B #R #Hf #c #b1 #b2 #H elim H -b2 /2 width=1 by ltc_rc/
#b #b2 #_ #Hb2 #IH >(Hf i) -Hf /2 width=3 by ltc_dx/
qed.

(* Inversions with contextual transitive closure ****************************)

lemma ltc_inv_CTC (C) (A) (i) (f) (B) (R:relation4 C A B B):
                  associative … f → annulment_2 … f i →
                  ∀c. ltc … f … (R c) i ⊆ CTC … (λc. R c i) c.
#C #A #i #f #B #R #H1f #H2f #c #b1 #b2
@(insert_eq_1 … i) #a #H
@(ltc_ind_dx A f B … H) -a -b2 /2 width=1 by inj/ -H1f
#a1 #a2 #b #b2 #_ #IH #Hb2 #H <H
elim (H2f … H) -H2f -H #H1 #H2 destruct
/3 width=3 by step/
qed-.

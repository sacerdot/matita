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

include "ground/notation/relations/rcolength_2.ma".
include "ground/relocation/rtmap_isid.ma".

(* RELOCATION MAP ***********************************************************)

inductive fcla: relation2 rtmap nat ≝
| fcla_isid: ∀f. 𝐈❪f❫ → fcla f (𝟎)
| fcla_push: ∀f,n. fcla f n → fcla (⫯f) n
| fcla_next: ∀f,n. fcla f n → fcla (↑f) (↑n)
.

interpretation "finite colength assignment (rtmap)"
   'RCoLength f n = (fcla f n).

(* Basic inversion lemmas ***************************************************)

lemma fcla_inv_px: ∀g,m. 𝐂❪g❫ ≘ m → ∀f. ⫯f = g → 𝐂❪f❫ ≘ m.
#g #m * -g -m /3 width=3 by fcla_isid, isid_inv_push/
#g #m #_ #f #H elim (discr_push_next … H)
qed-.

lemma fcla_inv_nx: ∀g,m. 𝐂❪g❫ ≘ m → ∀f. ↑f = g →
                   ∃∃n. 𝐂❪f❫ ≘ n & ↑n = m.
#g #m * -g -m /2 width=3 by ex2_intro/
[ #g #Hg #f #H elim (isid_inv_next …  H) -H //
| #g #m #_ #f #H elim (discr_next_push … H)
]
qed-.

(* Advanced inversion lemmas ************************************************)

lemma cla_inv_nn: ∀g,m. 𝐂❪g❫ ≘ m → ∀f,n. ↑f = g → ↑n = m → 𝐂❪f❫ ≘ n.
#g #m #H #f #n #H1 #H2 elim (fcla_inv_nx … H … H1) -g
#x #Hf #H destruct <(eq_inv_nsucc_bi … H) -n //
qed-.

lemma cla_inv_np: ∀g,m. 𝐂❪g❫ ≘ m → ∀f. ↑f = g → 𝟎 = m → ⊥.
#g #m #H #f #H1 elim (fcla_inv_nx … H … H1) -g
#x #_ #H1 #H2 destruct /2 width=2 by eq_inv_zero_nsucc/
qed-.

lemma fcla_inv_xp: ∀g,m. 𝐂❪g❫ ≘ m → 𝟎 = m → 𝐈❪g❫.
#g #m #H elim H -g -m /3 width=3 by isid_push/
#g #m #_ #_ #H destruct elim (eq_inv_zero_nsucc … H)
qed-.

lemma fcla_inv_isid: ∀f,n. 𝐂❪f❫ ≘ n → 𝐈❪f❫ → 𝟎 = n.
#f #n #H elim H -f -n /3 width=3 by isid_inv_push/
#f #n #_ #_ #H elim (isid_inv_next … H) -H //
qed-.

(* Main forward lemmas ******************************************************)

theorem fcla_mono: ∀f,n1. 𝐂❪f❫ ≘ n1 → ∀n2. 𝐂❪f❫ ≘ n2 → n1 = n2.
#f #n #H elim H -f -n
[ /2 width=3 by fcla_inv_isid/
| /3 width=3 by fcla_inv_px/
| #f #n1 #_ #IH #n2 #H elim (fcla_inv_nx … H) -H [2,3 : // ]
  #g #Hf #H destruct >IH //
]
qed-.

(* Basic properties *********************************************************)

lemma fcla_eq_repl_back: ∀n. eq_repl_back … (λf. 𝐂❪f❫ ≘ n).
#n #f1 #H elim H -f1 -n /3 width=3 by fcla_isid, isid_eq_repl_back/
#f1 #n #_ #IH #g2 #H [ elim (eq_inv_px … H) | elim (eq_inv_nx … H) ] -H
/3 width=3 by fcla_push, fcla_next/
qed-.

lemma fcla_eq_repl_fwd: ∀n. eq_repl_fwd … (λf. 𝐂❪f❫ ≘ n).
#n @eq_repl_sym /2 width=3 by fcla_eq_repl_back/
qed-.

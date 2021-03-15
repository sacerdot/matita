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

include "ground/notation/functions/upspoonstar_2.ma".
include "ground/arith/nat_succ_iter.ma".
include "ground/relocation/rtmap_eq.ma".

(* RELOCATION MAP ***********************************************************)

definition pushs (f:rtmap) (n:nat) ≝ push^n f.

interpretation "pushs (rtmap)" 'UpSpoonStar n f = (pushs f n).

(* Basic properties *********************************************************)

lemma pushs_O: ∀f. f = ⫯*[𝟎] f.
// qed.

lemma pushs_S: ∀f,n. ⫯⫯*[n] f = ⫯*[↑n] f.
#f #n @(niter_succ … push)
qed.

lemma pushs_eq_repl: ∀n. eq_repl (λf1,f2. ⫯*[n] f1 ≡ ⫯*[n] f2).
#n @(nat_ind_succ … n) -n /3 width=5 by eq_push/
qed.

(* Advanced properties ******************************************************)

lemma push_swap (n) (f):  ⫯⫯*[n] f = ⫯*[n] ⫯f.
#n #f @(niter_appl … push)
qed.

lemma pushs_xn: ∀n,f. ⫯*[n] ⫯f = ⫯*[↑n] f.
// qed.

(* Basic_inversion lemmas *****************************************************)

lemma eq_inv_pushs_sn: ∀n,f1,g2. ⫯*[n] f1 ≡ g2 →
                       ∃∃f2. f1 ≡ f2 & ⫯*[n] f2 = g2.
#n @(nat_ind_succ … n) -n /2 width=3 by ex2_intro/
#n #IH #f1 #g2 #H elim (eq_inv_px … H) -H [|*: // ]
#f0 #Hf10 #H1 elim (IH … Hf10) -IH -Hf10 #f2 #Hf12 #H2 destruct
/2 width=3 by ex2_intro/
qed-.

lemma eq_inv_pushs_dx: ∀n,f2,g1. g1 ≡ ⫯*[n] f2 →
                       ∃∃f1. f1 ≡ f2 & ⫯*[n] f1 = g1.
#n @(nat_ind_succ … n) -n /2 width=3 by ex2_intro/
#n #IH #f2 #g1 #H elim (eq_inv_xp … H) -H [|*: // ]
#f0 #Hf02 #H1 elim (IH … Hf02) -IH -Hf02 #f1 #Hf12 #H2 destruct
/2 width=3 by ex2_intro/
qed-.

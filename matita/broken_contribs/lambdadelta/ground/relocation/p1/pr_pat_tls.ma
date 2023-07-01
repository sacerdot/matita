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

include "ground/arith/pnat_plus.ma".
include "ground/relocation/p1/pr_tls.ma".
include "ground/relocation/p1/pr_pat_eq.ma".

(* POSITIVE APPLICATION FOR PARTIAL RELOCATION MAPS *************************)

(* Constructions with pr_tls ************************************************)

(* Note: this requires ↑ on first n *)
(*** at_pxx_tls *)
lemma pr_pat_unit_succ_tls (n) (f):
      ＠⧣❨𝟏,f❩ ≘ ↑n → ＠⧣❨𝟏,⫰*[n]f❩ ≘ 𝟏.
#n @(nat_ind_succ … n) -n //
#n #IH #f #Hf
elim (pr_pat_inv_unit_succ … Hf) -Hf [|*: // ] #g #Hg #H0 destruct
<pr_tls_swap /2 width=1 by/
qed.

(* Note: this requires ↑ on third n2 *)
(*** at_tls *)
lemma pr_pat_tls (n2) (f): ⫯⫰*[⁤↑n2]f ≐ ⫰*[n2]f → ∃i1. ＠⧣❨i1,f❩ ≘ ↑n2.
#n2 @(nat_ind_succ … n2) -n2
[ /4 width=4 by pr_pat_eq_repl_back, pr_pat_refl, ex_intro/
| #n2 #IH #f <pr_tls_swap <pr_tls_swap in ⊢ (??%→?); #H
  elim (IH … H) -IH -H #i1 #Hf
  elim (pr_map_split_tl f) #Hg destruct
  /3 width=8 by pr_pat_push, pr_pat_next, ex_intro/
]
qed-.

(* Inversions with pr_tls ***************************************************)

(* Note: this does not require ↑ on second and third p *)
(*** at_inv_nxx *)
lemma pr_pat_inv_succ_sn (p) (g) (i1) (j2):
      ＠⧣❨↑i1,g❩ ≘ j2 → ＠⧣❨𝟏,g❩ ≘ p →
      ∃∃i2. ＠⧣❨i1,⫰*[⁤p]g❩ ≘ i2 & p+i2 = j2.
#p elim p -p
[ #g #i1 #j2 #Hg #H
  elim (pr_pat_inv_unit_bi … H) -H [|*: // ] #f #H0
  elim (pr_pat_inv_succ_push … Hg … H0) -Hg [|*: // ] #x2 #Hf #H2 destruct
  /2 width=3 by ex2_intro/
| #p #IH #g #i1 #j2 #Hg #H
  elim (pr_pat_inv_unit_succ … H) -H [|*: // ] #f #Hf2 #H0
  elim (pr_pat_inv_next … Hg … H0) -Hg #x2 #Hf1 #H2 destruct
  elim (IH … Hf1 Hf2) -IH -Hf1 -Hf2 #i2 #Hf #H2 destruct
  >npsucc_pos /2 width=3 by ex2_intro/
]
qed-.

(* Note: this requires ↑ on first n2 *)
(*** at_inv_tls *)
lemma pr_pat_inv_succ_dx_tls (n2:ℕ) (i1) (f):
      ＠⧣❨i1,f❩ ≘ ↑n2 → ⫯⫰*[⁤↑n2]f ≐ ⫰*[n2]f.
#n2 @(nat_ind_succ … n2) -n2
[ #i1 #f #Hf elim (pr_pat_inv_unit_dx … Hf) -Hf // #g #H1 #H destruct
  /2 width=1 by pr_eq_refl/
| #n2 #IH #i1 #f #Hf
  elim (pr_pat_inv_succ_dx … Hf) -Hf [1,3: * |*: // ]
  [ #g #j1 #Hg #H1 #H2 | #g #Hg #Ho ] destruct
  <pr_tls_swap /2 width=2 by/
]
qed-.

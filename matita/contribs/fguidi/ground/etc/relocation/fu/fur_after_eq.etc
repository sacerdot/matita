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

include "ground/relocation/fu/fur_after_dapp.ma".
include "ground/relocation/fu/fur_eq.ma".

(* COMPOSITION FOR FINITE RELOCATION MAPS FOR UNWIND ************************)

(* Constructions with fur_eq ************************************************)

lemma fur_after_aux_eq_repl (h):
      (∀g,f,p. g＠⧣❨f＠⧣❨p❩❩ = (h g f)＠⧣❨p❩) →
      compatible_3 … fur_eq fur_eq fur_eq (λg,f.g•[h]f).
#h #Hh #g1 #g2 #Hg #f1 #f2 #Hf #p
<fur_dapp_after_aux // <fur_dapp_after_aux // -Hh
<(fur_dapp_eq_repl … Hf) -f2 <(fur_push_eq_repl … Hg) -g2 //
qed.

lemma fur_after_eq_repl:
      compatible_3 … fur_eq fur_eq fur_eq (λg,f.g•f).
#g1 #g2 #Hg #f1 #f2 #Hf #p
//
qed.



(*

include "ground/relocation/fu/fur_nexts_eq.ma".
include "ground/relocation/fu/fur_dapp_joins.ma".

axiom fur_dapp_j_sn (h) (f):
      ∃∃q. ∀p. p < q → f＠⧣❨p❩ = (𝗷h◗f)＠⧣❨p❩
        &  ∀p. q ≤ p → f＠⧣❨p❩+h = (𝗷h◗f)＠⧣❨p❩.
(*
#h #f elim f -f
[| * [| #k ] #f * #q #Hlt #Hge ]
[ //
| cases p -p
  [ /2 width=1 by or_introl/
  | #p <fur_dapp_p_dx_succ <fur_dapp_p_dx_succ
    elim (IH p) -IH #Hf
    /2 width=1 by or_introl, or_intror/
  ]
| <fur_dapp_j_dx <fur_dapp_j_dx
  elim (IH (p+k)) -IH #Hf
  /2 width=1 by or_introl, or_intror/
]
qed-.
*)
lemma fur_j_sn_eq_repl (k):
      compatible_2_fwd … fur_eq fur_eq (λf.𝗷k◗f).
#k #f1 #f2 #Hf #p
elim (fur_dapp_j_sn k f1) #q1 #Hlt1 #Hge1
elim (fur_dapp_j_sn k f2) #q2 #Hlt2 #Hge2
elim (pnat_split_lt_ge q2 q1) #Hq
[ 
| elim (pnat_split_lt_ge p q1) #H1p
  [ lapply (plt_ple_trans … H1p Hq) -Hq #H2p
    <Hlt1 // <Hlt2 //
  | elim (pnat_split_lt_ge p q2) #H2p
    [ -Hlt1 -Hge2 -Hq
      lapply (Hge1 … H1p) -Hge1 -H1p #H1
      lapply (Hlt2 … H2p) -Hlt2 -H2p #H2
    | <Hge1 // <Hge2 //
    ]
  ]
]

lemma fur_append_eq_repl_dx (f) (g1) (g2):
      g1 ≐ g2 → f●g1 ≐ f●g2.
#f @(list_ind_rcons … f) -f //
#f * [| #k ] #IH #g1 #g2 #Hg
<list_append_rcons_dx <list_append_rcons_dx
[ /3 width=1 by _/

lemma fur_after_aux_joins_dx (h) (g) (f2) (f1):
      (𝟎) = ♭f1 →
      (g•[h]f2)●f1 = g•[h](f2●f1).
#h #g #f2 #f1 elim f1 -f1 //
* [| #k ] #f1 #IH
[ <fur_depth_p_dx #Hf1 destruct
| <fur_depth_j_dx #Hf1
  <fur_after_aux_j_dx <IH -IH //
]
qed.

*)

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

include "ground/relocation/fu/fur_dapp.ma".
include "ground/relocation/fu/fur_depth.ma".
include "ground/relocation/fu/fur_height.ma".
include "ground/lib/list_length_append.ma".
include "ground/arith/wf1_ind_nlt.ma".
include "ground/arith/nat_lt_plus.ma".
include "ground/arith/nat_plus_rplus.ma".
include "ground/xoa/ex_3_2.ma".

(* DEPTH APPLICATION FOR FINITE RELOCATION MAPS FOR UNWIND ******************)

(* Constructions with fur_depth and fur_height ******************************)

lemma fur_dapp_append_joins_dx (g) (f) (p):
      (𝟎) = ♭f →
      g＠⧣❨p+♯f❩ = (g●f)＠⧣❨p❩.
#g #f elim f -f //
* [| #k ] #f #IH #p
[ <fur_depth_p_dx #Hf destruct
| <fur_depth_j_dx #Hf
  <list_append_lcons_sn <fur_dapp_j_dx <IH -IH //
]
qed.

lemma fur_map_inv_joins (f):
      ∃∃f2,f1. 𝟏 = f2＠⧣❨𝟏❩ & 𝟎 = ♭f1 & f = f2●f1.
#f elim f -f
[| * [| #k ] #f * #f2 #f1 #Hf2 #Hf1 #H0 destruct ]
[ /2 width=5 by ex3_2_intro/
| @(ex3_2_intro … (⫯(f2●f1)) (𝐢)) //
| /2 width=5 by ex3_2_intro/
]
qed-.

lemma fur_map_ind_joins (Q:predicate …):
      (Q (𝐢)) →
      (∀g. Q g → Q (⫯g)) →
      (∀g,f. 𝟏 = g＠⧣❨𝟏❩ → 𝟎 = ♭f → Q g → Q (g●f)) →
      ∀f. Q f.
#Q #IH1 #IH2 #IH3
@(wf1_ind_nlt … (list_length …)) #n #IH
* //
* [| #k ] #f #H0 destruct
[ /3 width=1 by/
| elim (fur_map_inv_joins f) #f2 #f1 #Hf2 #Hf1 #H0 destruct
  /3 width=1 by/
]
qed-.

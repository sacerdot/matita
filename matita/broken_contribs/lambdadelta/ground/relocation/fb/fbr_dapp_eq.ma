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

include "ground/relocation/fb/fbr_dapp.ma".
include "ground/relocation/fb/fbr_eq.ma".
include "ground/lib/exteq.ma".
include "ground/lib/functions.ma".
include "ground/notation/relations/doteqdot_2.ma".

(* DEPTH APPLICATION FOR FINITE RELOCATION MAPS WITH BOOLEANS **************)

definition fbr_dxeq: relation2 (𝔽𝔹) (𝔽𝔹) ≝
           λf1,f2. fbr_dapp f1 ⊜ fbr_dapp f2.

interpretation
  "depth extensional equivalence (finite relocation maps with booleans)"
  'DotEqDot f1 f2 = (fbr_dxeq f1 f2).

(* Basic constructions with fbr_dxeq ****************************************)

lemma fbr_dxeq_id_push_id:
      (𝐢) ≑ ⫯𝐢.
* //
qed.

(* Basic inversions with fbr_dxeq *******************************************)

lemma fbr_dxeq_inv_rcons_bi (b) (f1) (f2):
      f1◖b ≑ f2◖b → f1 ≑ f2.
* #f1 #f2 #Hf #p
@eq_inv_psucc_bi
[ >fbr_dapp_next_dx >fbr_dapp_next_dx //
| >fbr_dapp_push_dx_succ >fbr_dapp_push_dx_succ //
]
qed-.

lemma fbr_dxeq_inv_id_push (f2):
      (𝐢) ≑ ⫯f2 → (𝐢) ≑ f2.
/2 width=2 by fbr_dxeq_inv_rcons_bi/
qed-.

lemma fbr_dxeq_inv_push_id (f1):
      (⫯f1) ≑ (𝐢) → f1 ≑ (𝐢).
/2 width=2 by fbr_dxeq_inv_rcons_bi/
qed-.

lemma fbr_dxeq_inv_next_push (f1) (f2):
      ↑f1 ≑ ⫯f2 → ⊥.
#f1 #f2 #H0
lapply (H0 (𝟏)) -H0
<fbr_dapp_next_dx <fbr_dapp_push_dx_unit #H0 destruct
qed-.

lemma fbr_dxeq_inv_push_next (f1) (f2):
      (⫯f1) ≑ ↑f2 → ⊥.
#f1 #f2 #H0
lapply (H0 (𝟏)) -H0
<fbr_dapp_push_dx_unit <fbr_dapp_next_dx #H0 destruct
qed-.

lemma fbr_dxeq_inv_next_id (f1):
      ↑f1 ≑ (𝐢) → ⊥.
#f1 #H0
lapply (H0 (𝟏)) -H0
<fbr_dapp_next_dx <fbr_dapp_id #H0 destruct
qed-.

lemma fbr_dxeq_inv_id_next (f2):
      (𝐢) ≑ ↑f2 → ⊥.
#f2 #H0
lapply (H0 (𝟏)) -H0
<fbr_dapp_id <fbr_dapp_next_dx #H0 destruct
qed-.

(* Basic eliminations with fbr_dxeq *****************************************)

lemma fbr_dxeq_ind (Q:relation2 …):
      (Q (𝐢) (𝐢)) →
      (∀f2. (𝐢) ≑ f2 → Q (𝐢) f2 → Q (𝐢) (⫯f2)) →
      (∀f1. f1 ≑ (𝐢) → Q f1 (𝐢) → Q (⫯f1) (𝐢)) →
      (∀b,f1,f2. f1 ≑ f2 → Q f1 f2 → Q (f1◖b) (f2◖b)) →
      ∀f1,f2. f1 ≑ f2 → Q f1 f2.
#Q #IH1 #IH2 #IH3 #IH4
#f1 elim f1 -f1 [| * #f1 #IHa ]
#f2 elim f2 -f2 [2,4,6: * #f2 #IHb ] #H0
[ elim (fbr_dxeq_inv_id_next … H0)
| /4 width=1 by fbr_dxeq_inv_id_push/
| /4 width=2 by fbr_dxeq_inv_rcons_bi/
| elim (fbr_dxeq_inv_next_push … H0)
| elim (fbr_dxeq_inv_push_next … H0)
| /4 width=2 by fbr_dxeq_inv_rcons_bi/
| //
| elim (fbr_dxeq_inv_next_id … H0)
| /4 width=1 by fbr_dxeq_inv_push_id/
]
qed-.

(* Advanced inversions with fbr_dxeq ****************************************)

lemma fbr_dxeq_inv_eq (f1) (f2):
      f1 ≑ f2 → f1 ≐ f2.
#f1 #f2 #Hf @(fbr_dxeq_ind … Hf) -f1 -f2
/2 width=1 by fbr_eq_rcons_bi, fbr_eq_id_push, fbr_eq_push_id/
qed-.

(* Advanced constructions with fbr_dxeq *************************************)

(* Note: this is fbr_dxeq_eq *)
lemma fbr_dapp_eq_repl (p):
      compatible_2_fwd … fbr_eq (eq …) (λf.f＠⧣❨p❩).
#p #f1 #f2 #Hf
generalize in match p; -p
elim Hf -f1 -f2
[ * #f1 #f2 #_ #IH [ #p | * ] //
| #f2 #_ #IH * //
| #f1 #_ #IH * //
| //
]
qed.

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

include "basic_2/rt_computation/cpms_drops.ma".
include "basic_2/dynamic/cnv.ma".

(* EXAMPLES *****************************************************************)

(* Extended validy (λδ-2A) vs. restricted validity (λδ-1B) ******************)

(* Note: extended validity of a closure, height of cnv_appl > 1 *)
lemma cnv_extended (h) (p) (G) (L):
      ∀s. ⦃G,L.ⓛ⋆s.ⓛⓛ{p}⋆s.⋆s.ⓛ#0⦄ ⊢ ⓐ#2.#0 ![h,𝛚].
#h #p #G #L #s
@(cnv_appl … 2 p … (⋆s) … (⋆s))
[ //
| /4 width=1 by cnv_sort, cnv_zero, cnv_lref/
| /4 width=1 by cnv_bind, cnv_zero/
| /5 width=3 by cpm_cpms, cpm_lref, cpm_ell, lifts_sort/
| /5 width=5 by cpm_cpms, cpm_bind, cpm_ell, lifts_uni, lifts_sort, lifts_bind/
]
qed.

(* Note: restricted validity of the η-expanded closure, height of cnv_appl = 1 **)
lemma cnv_restricted (h) (p) (G) (L):
      ∀s. ⦃G,L.ⓛ⋆s.ⓛⓛ{p}⋆s.⋆s.ⓛⓛ{p}⋆s.ⓐ#0.#1⦄ ⊢ ⓐ#2.#0 ![h,𝟐].
#h #p #G #L #s
@(cnv_appl … 1 p … (⋆s) … (ⓐ#0.#2))
[ //
| /4 width=1 by cnv_sort, cnv_zero, cnv_lref/
| @cnv_zero
  @cnv_bind //
  @(cnv_appl … 1 p … (⋆s) … (⋆s))
  [ //
  | /2 width=1 by cnv_sort, cnv_zero/
  | /4 width=1 by cnv_sort, cnv_zero, cnv_lref, cnv_bind/
  | /2 width=3 by cpms_ell, lifts_sort/
  | /4 width=5 by cpms_lref, cpms_ell, lifts_uni, lifts_sort, lifts_bind/
  ]
| /4 width=3 by cpms_lref, cpms_ell, lifts_sort/
| /5 width=7 by cpms_ell, lifts_bind, lifts_flat, lifts_push_lref, lifts_push_zero, lifts_sort/
]
qed.

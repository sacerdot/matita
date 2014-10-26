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

include "basic_2/dynamic/snv.ma".

(* EXAMPLES *****************************************************************)

(* Extended validy (basic?_2) vs. restricted validity (basic_1) *************)

(* extended validity of a closure, last arg of snv_appl > 1 *)
lemma snv_extended: ∀h,g,a,G,L,k. ⦃G, L.ⓛ⋆k.ⓛⓛ{a}⋆k.⋆k.ⓛ#0⦄ ⊢ ⓐ#2.#0 ¡[h, g].
#h #g #a #G #L #k elim (deg_total h g k)
#d #Hd @(snv_appl … a … (⋆k) … (⋆k) (0+1+1))
[ /4 width=5 by snv_lref, drop_drop_lt/
| /4 width=13 by snv_bind, snv_lref/
| /5 width=6 by lstas_scpds, lstas_succ, da_ldec, da_sort, drop_drop_lt/
| @(lstas_scpds … (d+1+1))
  /5 width=11 by lstas_bind, lstas_succ, da_bind, da_ldec, da_sort, lift_bind/
]
qed.

(* restricted validity of the η-expanded closure, last arg of snv_appl = 1 **)
lemma snv_restricted: ∀h,g,a,G,L,k. ⦃G, L.ⓛ⋆k.ⓛⓛ{a}⋆k.⋆k.ⓛⓛ{a}⋆k.ⓐ#0.#1⦄ ⊢ ⓐ#2.#0 ¡[h, g].
#h #g #a #G #L #k elim (deg_total h g k)
#d #Hd @(snv_appl … a … (⋆k) … (ⓐ#0.#2) (0+1))
[ /4 width=5 by snv_lref, drop_drop_lt/
| @snv_lref [4: // |1,2,3: skip ]
  @snv_bind //
  @(snv_appl … a … (⋆k) … (⋆k) (0+1))
  [ @snv_lref [4: // |1,2,3: skip ] //
  | @snv_lref [4: /2 width=1 by drop_drop_lt/ |1,2,3: skip ] @snv_bind //
  | @(lstas_scpds … (d+1)) /3 width=6 by da_sort, da_ldec, lstas_succ/
  | @(lstas_scpds … (d+1)) /3 width=8 by lstas_succ, lstas_bind, drop_drop, lift_bind/
    @da_ldec [3: /2 width=1 by drop_drop_lt/ |1,2: skip ] /3 width=1 by da_sort, da_bind/
  ]
| /5 width=6 by lstas_scpds, lstas_succ, da_ldec, da_sort, drop_drop_lt/
| @(lstas_scpds … (d+1+1)) //
  [ @da_ldec [3: // |1,2: skip ]
    @da_bind @da_flat @da_ldec [3: /2 width=1 by drop_drop_lt/ |1,2: skip ]
    /3 width=1 by da_sort, da_bind/
  | @lstas_succ [4: // |1,2: skip ]
    [2: @lstas_bind | skip ]
    [2: @lstas_appl | skip ]
    [2: @lstas_zero
        [4: /2 width=1 by drop_drop_lt/ |5: /2 width=2 by lstas_bind/ |*: skip ]
    |1: skip ]
    /4 width=2 by lift_flat, lift_bind, lift_lref_ge_minus, lift_lref_lt/
  ]
]
qed.

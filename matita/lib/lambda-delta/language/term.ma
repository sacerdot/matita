(*
    ||M||  This file is part of HELM, an Hypertextual, Electronic
    ||A||  Library of Mathematics, developed at the Computer Science
    ||T||  Department of the University of Bologna, Italy.
    ||I||
    ||T||
    ||A||  This file is distributed under the terms of the
    \   /  GNU General Public License Version 2
     \ /
      V_______________________________________________________________ *)

include "lambda-delta/language/item.ma".

(* TERMS ********************************************************************)

(* terms *)
inductive term: Type[0] ≝
| TSort: nat → term                 (* sort: starting at 0 *)
| TLRef: nat → term                 (* reference by index: starting at 0 *)
| TPair: item2 → term → term → term (* binary item construction *)
.

interpretation "sort (term)" 'Star k = (TSort k).

interpretation "local reference (term)" 'Weight i = (TLRef i).

interpretation "term construction (binary)" 'SItem I T1 T2 = (TPair I T1 T2).

interpretation "term binding construction (binary)" 'SBind I T1 T2 = (TPair (Bind I) T1 T2).

interpretation "term flat construction (binary)" 'SFlat I T1 T2 = (TPair (Flat I) T1 T2).

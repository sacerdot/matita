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

(* Project started Tue Aug 22, 2006 ***************************************)

set "baseuri" "cic:/matita/LAMBDA-TYPES/Unified/P/defs".

(* POLARIZED TERMS
   - Naming policy:
     - natural numbers      : sorts h k, local references i j, lengths l
     - boolean values       : a b
     - generic binding items: x
     - generic flat items   : y
     - generic head items   : z
     - terms                : p q
*)

include "../../RELATIONAL/Nat/defs.ma".
include "../../RELATIONAL/Bool/defs.ma".

inductive Bind: Set \def
   | abbr: Bind
   | abst: Bind
   | excl: Bind
.

inductive Flat: Set \def
   | appl: Flat
   | cast: Flat
.

inductive Head: Set \def
   | bind: Bind \to Head
   | flat: Flat \to Head
.

inductive P: Set \def
   | sort: Nat \to P
   | lref: Nat \to P
   | head: Bool \to Head \to P \to P \to P
.

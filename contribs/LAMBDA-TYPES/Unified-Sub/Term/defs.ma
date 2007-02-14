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

set "baseuri" "cic:/matita/LAMBDA-TYPES/Unified-Sub/Term/defs".

(* POLARIZED TERMS
   - Naming policy:
     - natural numbers      : sorts h k, local references i j, lengths l o
     - boolean values       : p q
     - generic leaf items   : m n
     - generic binding items: r s 
     - generic flat items   : r s
     - generic head items   : m n
     - terms                : t u
*)

include "preamble.ma".

inductive Leaf: Set \def
   | sort: Nat \to Leaf
   | lref: Nat \to Leaf
.

inductive Bind: Set \def
   | abbr: Bind
   | abst: Bind
   | excl: Bind
.

inductive Flat: Set \def
   | appl: Flat
   | cast: Flat
.

inductive IntB: Set \def
   | bind: Bool \to Bind \to IntB
.

inductive IntF: Set \def
   | flat: Bool \to Flat \to IntF
.

inductive Term: Set \def
   | leaf: Leaf \to Term
   | intb: IntB \to Term \to Term \to Term
   | intf: IntF \to Term \to Term \to Term
.

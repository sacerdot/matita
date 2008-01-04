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

set "baseuri" "cic:/matita/LAMBDA-TYPES/Unified-Sub/datatypes/Term".

(* POLARIZED TERMS
   - Naming policy:
     - natural numbers      : sorts h k, local references i j, lengths l o
     - boolean values       : p q
     - generic binding items: r s 
     - generic flat items   : r s
     - generic head items   : m n
     - terms                : t u
*)

include "preamble.ma".

inductive Bind: Type \def
   | abbr: Bind
   | abst: Bind
   | excl: Bind
.

inductive Flat: Type \def
   | appl: Flat
   | cast: Flat
.

inductive IntB: Type \def
   | bind: Bool \to Bind \to IntB
.

inductive IntF: Type \def
   | flat: Bool \to Flat \to IntF
.

inductive Term: Type \def
   | sort: Nat  \to Term
   | lref: Nat  \to Term
   | intb: IntB \to Term \to Term \to Term
   | intf: IntF \to Term \to Term \to Term
.

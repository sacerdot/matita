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

include "Class/defs.ma".

(* QUANTIFICATION DOMAINS
   - These are the categories on which we allow quantification.
   - We set up single quantifiers, parametric on the domain.
*)

record Domain: Type ≝ {
   domain:> Class
}.

(* internal universal quantification *)
inductive dall (D:Domain) (P:D → Prop): Prop ≝
   | dall_intro: (∀d. cin ? d → P d) → dall D P
.

interpretation "internal for all" 'iforall η.x = (dall ? x).

(* internal existential quantification *)
inductive dex (D:Domain) (P:D → Prop): Prop ≝
   | dex_intro: ∀d. cin D d → P d → dex D P
.

interpretation "internal exists" 'iexists η.x = (dex ? x).

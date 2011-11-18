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

include "Basic_2/grammar/term_simple.ma".

(* CANDIDATES OF REDUCIBILITY ***********************************************)

(* abstract conditions for candidates *)

definition CR1: predicate term → predicate term → Prop ≝
                λRD,RC. ∀T. RC T → RD T.

definition CR2: relation term → predicate term → Prop ≝
                λRR,RC. ∀T1,T2. RC T1 → 𝕊[T1] → RR T1 T2 → RC T2.

definition CR3: relation term → predicate term → Prop ≝
                λRR,RC. ∀T1. (∀T2. RR T1 T2 → RC T2) → 𝕊[T1] → RC T1.

(* a candidate *)
record cr (RR:relation term) (RD:predicate term): Type[0] ≝ {
   in_cr: predicate term;
   cr1: CR1 RD in_cr;
   cr2: CR2 RR in_cr;
   cr3: CR3 RR in_cr
}.

interpretation
   "context-free parallel reduction (term)"
   'InSubset T R = (in_cr ? ? R T).

definition in_fun_cr: ∀RR,RD. ∀D,C:(cr RR RD). predicate term ≝
                      λRR,RD,D,C,T. ∀V. V ϵ D → 𝕔{Appl}V.T ϵ C.

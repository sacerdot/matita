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

include "basic_2A/grammar/genv.ma".
include "basic_2A/multiple/drops.ma".

(* GENERIC COMPUTATION PROPERTIES *******************************************)

definition nf ≝ λRR:relation4 genv lenv term term. λRS:relation term.
                λG,L,T. NF … (RR G L) RS T.

definition candidate: Type[0] ≝ relation3 genv lenv term.

definition CP0 ≝ λRR:relation4 genv lenv term term. λRS:relation term.
                 ∀G. d_liftable1 (nf RR RS G) (Ⓕ).

definition CP1 ≝ λRR:relation4 genv lenv term term. λRS:relation term.
                 ∀G,L. ∃k. NF … (RR G L) RS (⋆k).

definition CP2 ≝ λRP:candidate. ∀G. d_liftable1 (RP G) (Ⓕ).

definition CP3 ≝ λRP:candidate.
                 ∀G,L,T,k. RP G L (ⓐ⋆k.T) → RP G L T.

(* requirements for generic computation properties *)
record gcp (RR:relation4 genv lenv term term) (RS:relation term) (RP:candidate) : Prop ≝
{ cp0: CP0 RR RS;
  cp1: CP1 RR RS;
  cp2: CP2 RP;
  cp3: CP3 RP
}.

(* Basic properties *********************************************************)

(* Basic_1: was: nf2_lift1 *)
lemma gcp0_lifts: ∀RR,RS,RP. gcp RR RS RP → ∀G. d_liftables1 (nf RR RS G) (Ⓕ).
#RR #RS #RP #H #G @d1_liftable_liftables @(cp0 … H)
qed.

lemma gcp2_lifts: ∀RR,RS,RP. gcp RR RS RP → ∀G. d_liftables1 (RP G) (Ⓕ).
#RR #RS #RP #H #G @d1_liftable_liftables @(cp2 … H)
qed.

(* Basic_1: was only: sns3_lifts1 *)
lemma gcp2_lifts_all: ∀RR,RS,RP. gcp RR RS RP → ∀G. d_liftables1_all (RP G) (Ⓕ).
#RR #RS #RP #H #G @d1_liftables_liftables_all /2 width=7 by gcp2_lifts/
qed.

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

include "static_2/syntax/genv.ma".
include "static_2/relocation/drops_vector.ma".

(* GENERIC COMPUTATION PROPERTIES *******************************************)

definition nf ≝ λRR:relation4 genv lenv term term. λRS:relation term.
                λG,L,T. NF … (RR G L) RS T.

definition candidate: Type[0] ≝ relation3 genv lenv term.

definition CP0 ≝ λRR:relation4 genv lenv term term. λRS:relation term.
                 ∀G. d_liftable1 (nf RR RS G).

definition CP1 ≝ λRR:relation4 genv lenv term term. λRS:relation term.
                 ∀G,L. ∃s. NF … (RR G L) RS (⋆s).

definition CP2 ≝ λRP:candidate. ∀G. d_liftable1 (RP G).

definition CP3 ≝ λRP:candidate.
                 ∀G,L,T,s. RP G L (ⓐ⋆s.T) → RP G L T.

(* requirements for generic computation properties *)
(* Basic_1: includes: nf2_lift1 *)
(* Basic_2A1: includes: gcp0_lifts *)
(* Basic_2A1: includes: gcp2_lifts *)
record gcp (RR:relation4 genv lenv term term) (RS:relation term) (RP:candidate) : Prop ≝
{ cp0: CP0 RR RS;
  cp1: CP1 RR RS;
  cp2: CP2 RP;
  cp3: CP3 RP
}.

(* Basic properties *********************************************************)

(* Basic_1: was only: sns3_lifts1 *)
(* Basic_2A1: was: gcp2_lifts_all *)
lemma gcp2_all: ∀RR,RS,RP. gcp RR RS RP → ∀G. d_liftable1_all (RP G).
/3 width=7 by cp2, d1_liftable_liftable_all/ qed.

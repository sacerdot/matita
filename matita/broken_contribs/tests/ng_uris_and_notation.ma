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

include "ng_pts.ma".
include "nat/nat.ma".

ndefinition foo: nat ≝ O.

ndefinition goo ≝ cic:/matita/nat/nat/nat.ind#xpointer(1/1/1).

ndefinition goo' ≝ cic:/matita/tests/ng_uris_and_notation/foo.def(1).

ntheorem xx: goo' = cic:/matita/tests/ng_uris_and_notation/foo.def(1).
 nnormalize;
 napply (refl_eq ? O);
nqed.

naxiom ax: nat.

ntheorem yy: ax = cic:/matita/tests/ng_uris_and_notation/ax.dec.
 napply (refl_eq ??);
nqed.

ndefinition nnat: Type ≝ nat.

interpretation "NNatural numbers" 'N = cic:/matita/tests/ng_uris_and_notation/nnat.def(1).

ndefinition nnnat: Type ≝ nnat.

interpretation "NNNatural numbers" 'N = nnnat.

ndefinition try_notation: nnat → nnnat.
 napply (λx.x);
nqed.
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

include "alpha_1/grammar/term.ma".

(* TERMS ********************************************************************)

let rec tappend T U on T ≝ match T with
[ TAtom       ⇒ U
| TUnit I T   ⇒ ①{I}.(tappend T U)
| TPair I V T ⇒ ②{I}V.(tappend T U)
].

interpretation "append (term)" 'Append T U = (tappend T U).

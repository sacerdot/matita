(**************************************************************************)
(*       ___	                                                            *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||       A.Asperti, C.Sacerdoti Coen,                          *)
(*      ||A||       E.Tassi, S.Zacchiroli                                 *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU Lesser General Public License Version 2.1         *)
(*                                                                        *)
(**************************************************************************)

include "Q/ratio/ratio.ma".
include "Q/fraction/finv.ma".

definition rinv : ratio \to ratio \def
\lambda r:ratio.
  match r with
  [one \Rightarrow one
  | (frac f) \Rightarrow frac (finv f)].

theorem rinv_rinv: ∀r. rinv (rinv r) = r.
 intro;
 elim r;
  [ reflexivity
  | simplify;
    rewrite > finv_finv;
    reflexivity]
qed.

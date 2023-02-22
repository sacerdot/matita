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

(* This file was automatically generated: do not edit *********************)

set "baseuri" "cic:/matita/CoRN-Decl/fta/KeyLemma".

include "CoRN.ma".

(* $Id: KeyLemma.v,v 1.5 2004/04/23 10:00:57 lcf Exp $ *)

include "reals/NRootIR.ma".

(*#* printing p3m %\ensuremath{\frac13\hat{\ }}% *)

(*#* printing Halfeps %\ensuremath{\frac\varepsilon2}% *)

(*#* * Technical lemmas for the FTA
** Key Lemma
*)

(* UNEXPORTED
Section Key_Lemma
*)

(*#*
%\begin{convention}% Let [a:nat->IR] and [n:nat] such that [0 < n],
[forall (k : nat) (Zero [<=] (a k))], [(a n) [=] One] and [a_0 : IR],
and [eps : IR] such that [(Zero [<] eps)] and [(eps [<=] a_0)].
%\end{convention}%
*)

alias id "a" = "cic:/CoRN/fta/KeyLemma/Key_Lemma/a.var".

alias id "n" = "cic:/CoRN/fta/KeyLemma/Key_Lemma/n.var".

alias id "gt_n_0" = "cic:/CoRN/fta/KeyLemma/Key_Lemma/gt_n_0.var".

alias id "eps" = "cic:/CoRN/fta/KeyLemma/Key_Lemma/eps.var".

alias id "eps_pos" = "cic:/CoRN/fta/KeyLemma/Key_Lemma/eps_pos.var".

alias id "a_nonneg" = "cic:/CoRN/fta/KeyLemma/Key_Lemma/a_nonneg.var".

alias id "a_n_1" = "cic:/CoRN/fta/KeyLemma/Key_Lemma/a_n_1.var".

alias id "a_0" = "cic:/CoRN/fta/KeyLemma/Key_Lemma/a_0.var".

alias id "eps_le_a_0" = "cic:/CoRN/fta/KeyLemma/Key_Lemma/eps_le_a_0.var".

inline "cic:/CoRN/fta/KeyLemma/a_0_eps_nonneg.con".

inline "cic:/CoRN/fta/KeyLemma/a_0_eps_fuzz.con".

inline "cic:/CoRN/fta/KeyLemma/lem_1a.con".

inline "cic:/CoRN/fta/KeyLemma/lem_1b.con".

inline "cic:/CoRN/fta/KeyLemma/lem_1c.con".

inline "cic:/CoRN/fta/KeyLemma/lem_1.con".

inline "cic:/CoRN/fta/KeyLemma/p3m.con".

inline "cic:/CoRN/fta/KeyLemma/p3m_pos.con".

inline "cic:/CoRN/fta/KeyLemma/p3m_S.con".

(* UNEXPORTED
Hint Resolve p3m_S: algebra.
*)

inline "cic:/CoRN/fta/KeyLemma/p3m_P.con".

inline "cic:/CoRN/fta/KeyLemma/p3m_aux.con".

inline "cic:/CoRN/fta/KeyLemma/p3m_pow.con".

(* UNEXPORTED
Hint Resolve p3m_aux: algebra.
*)

inline "cic:/CoRN/fta/KeyLemma/p3m_0.con".

(* UNEXPORTED
Hint Resolve p3m_0: algebra.
*)

inline "cic:/CoRN/fta/KeyLemma/third_pos.con".

(* UNEXPORTED
Hint Resolve third_pos: algebra.
*)

inline "cic:/CoRN/fta/KeyLemma/third_less_one.con".

(* UNEXPORTED
Hint Resolve third_less_one: algebra.
*)

inline "cic:/CoRN/fta/KeyLemma/p3m_mon.con".

inline "cic:/CoRN/fta/KeyLemma/p3m_mon'.con".

inline "cic:/CoRN/fta/KeyLemma/p3m_small.con".

inline "cic:/CoRN/fta/KeyLemma/p3m_smaller.con".

inline "cic:/CoRN/fta/KeyLemma/chfun.con".

inline "cic:/CoRN/fta/KeyLemma/chfun_1.con".

inline "cic:/CoRN/fta/KeyLemma/chfun_2.con".

inline "cic:/CoRN/fta/KeyLemma/chfun_3.con".

inline "cic:/CoRN/fta/KeyLemma/chfun_4.con".

inline "cic:/CoRN/fta/KeyLemma/Halfeps.con".

inline "cic:/CoRN/fta/KeyLemma/Halfeps_pos.con".

inline "cic:/CoRN/fta/KeyLemma/Halfeps_Halfeps.con".

(* UNEXPORTED
Hint Resolve Halfeps_Halfeps: algebra.
*)

inline "cic:/CoRN/fta/KeyLemma/Halfeps_eps.con".

inline "cic:/CoRN/fta/KeyLemma/Halfeps_trans.con".

inline "cic:/CoRN/fta/KeyLemma/Key_1a.con".

(* UNEXPORTED
Hint Resolve Key_1a: algebra.
*)

inline "cic:/CoRN/fta/KeyLemma/Key_1b.con".

inline "cic:/CoRN/fta/KeyLemma/Key_1.con".

inline "cic:/CoRN/fta/KeyLemma/Key_2.con".

inline "cic:/CoRN/fta/KeyLemma/Key.con".

(* end hide *)

(* UNEXPORTED
End Key_Lemma
*)

(* UNEXPORTED
Hint Resolve p3m_S p3m_P p3m_pow: algebra.
*)


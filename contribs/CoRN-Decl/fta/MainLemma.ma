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

set "baseuri" "cic:/matita/CoRN-Decl/fta/MainLemma".

include "CoRN_notation.ma".

(* $Id: MainLemma.v,v 1.3 2004/04/23 10:00:57 lcf Exp $ *)

(*#* printing two_n %\ensuremath{2n}% #2n# *)

(*#* printing Small %\ensuremath{\frac13^n}% *)

(*#* printing Smaller %\ensuremath{\frac13^{2n^2}}% *)

include "reals/CSumsReals.ma".

include "fta/KeyLemma.ma".

(*#* ** Main Lemma
*)

(* UNEXPORTED
Section Main_Lemma.
*)

(*#*
%\begin{convention}%
Let [a : nat->IR], [n : nat], [a_0 : IR]  and [eps : IR] such that [0 < n],
[(Zero [<] eps)], [forall (k : nat)(Zero [<=] (a k))], [(a n) [=] One], and
[(eps [<=] a_0)].
%\end{convention}%
*)

inline "cic:/CoRN/fta/MainLemma/a.var".

inline "cic:/CoRN/fta/MainLemma/n.var".

inline "cic:/CoRN/fta/MainLemma/gt_n_0.var".

inline "cic:/CoRN/fta/MainLemma/eps.var".

inline "cic:/CoRN/fta/MainLemma/eps_pos.var".

inline "cic:/CoRN/fta/MainLemma/a_nonneg.var".

inline "cic:/CoRN/fta/MainLemma/a_n_1.var".

inline "cic:/CoRN/fta/MainLemma/a_0.var".

inline "cic:/CoRN/fta/MainLemma/eps_le_a_0.var".

inline "cic:/CoRN/fta/MainLemma/a_0_pos.con".

(*#* 
%\begin{convention}% We define the following local abbreviations:
 - [two_n := 2 * n]
 - [Small := p3m n]
 - [Smaller := p3m (two_n * n)]

%\end{convention}%
*)

(* begin hide *)

inline "cic:/CoRN/fta/MainLemma/two_n.con".

inline "cic:/CoRN/fta/MainLemma/Small.con".

inline "cic:/CoRN/fta/MainLemma/Smaller.con".

(* end hide *)

inline "cic:/CoRN/fta/MainLemma/Main_1a'.con".

(* end hide *)

inline "cic:/CoRN/fta/MainLemma/Main_1b'.con".

(* end hide *)

inline "cic:/CoRN/fta/MainLemma/Main_1a.con".

(* end hide *)

inline "cic:/CoRN/fta/MainLemma/Main_1b.con".

(* end hide *)

inline "cic:/CoRN/fta/MainLemma/Main_1.con".

(* end hide *)

inline "cic:/CoRN/fta/MainLemma/Main_2'.con".

inline "cic:/CoRN/fta/MainLemma/Main_2.con".

(* end hide *)

inline "cic:/CoRN/fta/MainLemma/Main_3a.con".

(* end hide *)

inline "cic:/CoRN/fta/MainLemma/Main_3.con".

(* end hide *)

inline "cic:/CoRN/fta/MainLemma/Main.con".

(* end hide *)

(* UNEXPORTED
End Main_Lemma.
*)


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

set "baseuri" "cic:/matita/CoRN-Decl/fta/KneserLemma".

(* $Id: KneserLemma.v,v 1.7 2004/04/23 10:00:57 lcf Exp $ *)

(*#* printing Smallest %\ensuremath{\frac13^{2n^2+n}}% *)

(*#* printing eta_0 %\ensuremath{\eta_0}% #&eta;<SUB>0</SUB># *)

(* INCLUDE
NRootCC
*)

(* INCLUDE
AbsCC
*)

(* INCLUDE
MainLemma
*)

(*#* ** Kneser Lemma *)

(* UNEXPORTED
Section Kneser_Lemma.
*)

(*#*
%\begin{convention}% Let [b : nat->CC], [n : nat] and [c : IR]
such that [0 < n], [b_0 := b 0], [b_n := (b n) [=] One] and
[(AbsCC b_0) [<] c].
%\end{convention}%
*)

inline cic:/CoRN/fta/KneserLemma/b.var.

inline cic:/CoRN/fta/KneserLemma/n.var.

inline cic:/CoRN/fta/KneserLemma/gt_n_0.var.

(* begin hide *)

inline cic:/CoRN/fta/KneserLemma/b_0.con.

inline cic:/CoRN/fta/KneserLemma/b_n.con.

(* end hide *)

inline cic:/CoRN/fta/KneserLemma/b_n_1.var.

inline cic:/CoRN/fta/KneserLemma/c.var.

inline cic:/CoRN/fta/KneserLemma/b_0_lt_c.var.

(*#* 
%\begin{convention}% We define the following local abbreviations:
 - [two_n := 2 * n]
 - [Small := p3m n]
 - [Smaller := p3m (two_n * n)]
 - [Smallest := Small[*]Smaller]
 - [q := One[-]Smallest]
 - [a i := AbsCC (b i)]

%\end{convention}%
*)

(* begin hide *)

inline cic:/CoRN/fta/KneserLemma/two_n.con.

inline cic:/CoRN/fta/KneserLemma/Small.con.

inline cic:/CoRN/fta/KneserLemma/Smaller.con.

inline cic:/CoRN/fta/KneserLemma/Smallest.con.

inline cic:/CoRN/fta/KneserLemma/q.con.

(* end hide *)

inline cic:/CoRN/fta/KneserLemma/b_0'_exists.con.

inline cic:/CoRN/fta/KneserLemma/eta_0.con.

inline cic:/CoRN/fta/KneserLemma/eta_0_pos.con.

inline cic:/CoRN/fta/KneserLemma/eta_exists.con.

inline cic:/CoRN/fta/KneserLemma/eps_exists_1.con.

(* less_cotransitive_unfolded on 
  {Zero  [<]  y[/]x[//]H3[-]Half[*]eps} + 
  {y[/]x[//]H3[-]Half[*]eps  [<]  Half[*]eps}. *)

inline cic:/CoRN/fta/KneserLemma/eps_exists.con.

(* begin hide *)

inline cic:/CoRN/fta/KneserLemma/a.con.

(* end hide *)

inline cic:/CoRN/fta/KneserLemma/z_exists.con.

(* end hide *)

inline cic:/CoRN/fta/KneserLemma/Kneser_1'.con.

inline cic:/CoRN/fta/KneserLemma/Kneser_1''.con.

inline cic:/CoRN/fta/KneserLemma/Kneser_1.con.

inline cic:/CoRN/fta/KneserLemma/Kneser_2a.con.

inline cic:/CoRN/fta/KneserLemma/Kneser_2b.con.

(* end hide *)

inline cic:/CoRN/fta/KneserLemma/Kneser_2c.con.

(* end hide *)

inline cic:/CoRN/fta/KneserLemma/Kneser_2.con.

(* end hide *)

inline cic:/CoRN/fta/KneserLemma/Kneser_3.con.

(* UNEXPORTED
End Kneser_Lemma.
*)

inline cic:/CoRN/fta/KneserLemma/Kneser.con.


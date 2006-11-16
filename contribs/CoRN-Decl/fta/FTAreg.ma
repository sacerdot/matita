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

set "baseuri" "cic:/matita/CoRN-Decl/fta/FTAreg".

include "CoRN.ma".

(* $Id: FTAreg.v,v 1.4 2004/04/23 10:00:57 lcf Exp $ *)

include "fta/KneserLemma.ma".

include "fta/CPoly_Shift.ma".

include "fta/CPoly_Contin1.ma".

(*#* * FTA for regular polynomials
** The Kneser sequence
%\begin{convention}% Let [n] be a positive natural number.
%\end{convention}%
*)

(* UNEXPORTED
Section Seq_Exists.
*)

inline "cic:/CoRN/fta/FTAreg/n.var".

inline "cic:/CoRN/fta/FTAreg/lt0n.var".

(*#*
%\begin{convention}% Let [qK] be a real between 0 and 1, with
[[
forall (p : CCX), (monic n p) -> forall (c : IR), ((AbsCC (p!Zero)) [<] c) ->
 {z:CC | ((AbsCC z) [^]n [<] c) | ((AbsCC (p!z)) [<] qK[*]c)}.
]]
Let [p] be a monic polynomial over the complex numbers with degree 
[n], and let [c0] be such that [(AbsCC (p!Zero)) [<] c0].
%\end{convention}%
*)

(* UNEXPORTED
Section Kneser_Sequence.
*)

inline "cic:/CoRN/fta/FTAreg/qK.var".

inline "cic:/CoRN/fta/FTAreg/zltq.var".

inline "cic:/CoRN/fta/FTAreg/qlt1.var".

inline "cic:/CoRN/fta/FTAreg/q_prop.var".

inline "cic:/CoRN/fta/FTAreg/p.var".

inline "cic:/CoRN/fta/FTAreg/mp.var".

inline "cic:/CoRN/fta/FTAreg/c0.var".

inline "cic:/CoRN/fta/FTAreg/p0ltc0.var".

inline "cic:/CoRN/fta/FTAreg/Knes_tup.ind".

coercion "cic:/matita/CoRN-Decl/fta/FTAreg/z_el.con" 0 (* compounds *).

inline "cic:/CoRN/fta/FTAreg/Knes_tupp.ind".

coercion "cic:/matita/CoRN-Decl/fta/FTAreg/Kntup.con" 0 (* compounds *).

inline "cic:/CoRN/fta/FTAreg/Knes_fun.con".

inline "cic:/CoRN/fta/FTAreg/Knes_fun_it.con".

inline "cic:/CoRN/fta/FTAreg/sK.con".

inline "cic:/CoRN/fta/FTAreg/sK_c.con".

inline "cic:/CoRN/fta/FTAreg/sK_c0.con".

inline "cic:/CoRN/fta/FTAreg/sK_prop1.con".

inline "cic:/CoRN/fta/FTAreg/sK_it.con".

inline "cic:/CoRN/fta/FTAreg/sK_prop2.con".

(* UNEXPORTED
End Kneser_Sequence.
*)

(* UNEXPORTED
Section Seq_Exists_Main.
*)

(*#* **Main results
*)

inline "cic:/CoRN/fta/FTAreg/seq_exists.con".

(* UNEXPORTED
End Seq_Exists_Main.
*)

(* UNEXPORTED
End Seq_Exists.
*)

(* UNEXPORTED
Section N_Exists.
*)

inline "cic:/CoRN/fta/FTAreg/n.var".

inline "cic:/CoRN/fta/FTAreg/lt0n.var".

inline "cic:/CoRN/fta/FTAreg/q.var".

inline "cic:/CoRN/fta/FTAreg/zleq.var".

inline "cic:/CoRN/fta/FTAreg/qlt1.var".

inline "cic:/CoRN/fta/FTAreg/c.var".

inline "cic:/CoRN/fta/FTAreg/zltc.var".

(* begin hide *)

inline "cic:/CoRN/fta/FTAreg/q_.con".

(* end hide *)

inline "cic:/CoRN/fta/FTAreg/e.var".

inline "cic:/CoRN/fta/FTAreg/zlte.var".

inline "cic:/CoRN/fta/FTAreg/N_exists.con".

(* UNEXPORTED
End N_Exists.
*)

(* UNEXPORTED
Section Seq_is_CC_CAuchy.
*)

(*#* ** The Kneser sequence is Cauchy in [CC] *)

inline "cic:/CoRN/fta/FTAreg/n.var".

inline "cic:/CoRN/fta/FTAreg/lt0n.var".

inline "cic:/CoRN/fta/FTAreg/q.var".

inline "cic:/CoRN/fta/FTAreg/zleq.var".

inline "cic:/CoRN/fta/FTAreg/qlt1.var".

inline "cic:/CoRN/fta/FTAreg/c.var".

inline "cic:/CoRN/fta/FTAreg/zltc.var".

(*#* %\begin{convention}% Let:
 - [q_] prove [q[-]One [#] Zero]
 - [nrtq := NRoot q n]
 - [nrtc := Nroot c n]
 - [nrtqlt1] prove [nrtq [<] One]
 - [nrtq_] prove [nrtq[-]One [#] Zero]

%\end{convention}% *)

(* begin hide *)

inline "cic:/CoRN/fta/FTAreg/q_.con".

inline "cic:/CoRN/fta/FTAreg/nrtq.con".

inline "cic:/CoRN/fta/FTAreg/nrtc.con".

inline "cic:/CoRN/fta/FTAreg/nrtqlt1.con".

inline "cic:/CoRN/fta/FTAreg/nrtq_.con".

(* end hide *)

inline "cic:/CoRN/fta/FTAreg/zlt_nrtq.con".

inline "cic:/CoRN/fta/FTAreg/zlt_nrtc.con".

inline "cic:/CoRN/fta/FTAreg/nrt_pow.con".

inline "cic:/CoRN/fta/FTAreg/abs_pow_ltRe.con".

inline "cic:/CoRN/fta/FTAreg/abs_pow_ltIm.con".

inline "cic:/CoRN/fta/FTAreg/SublemmaRe.con".

inline "cic:/CoRN/fta/FTAreg/SublemmaIm.con".

inline "cic:/CoRN/fta/FTAreg/seq_is_CC_Cauchy.con".

(* UNEXPORTED
End Seq_is_CC_CAuchy.
*)

inline "cic:/CoRN/fta/FTAreg/FTA_monic.con".

inline "cic:/CoRN/fta/FTAreg/FTA_reg.con".


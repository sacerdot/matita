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

set "baseuri" "cic:/matita/CoRN-Decl/ftc/RefLemma".

(* $Id: RefLemma.v,v 1.7 2004/04/23 10:01:00 lcf Exp $ *)

(* INCLUDE
RefSeparating
*)

(* INCLUDE
RefSeparated
*)

(* INCLUDE
RefSepRef
*)

(* UNEXPORTED
Section Refinement_Lemma.
*)

(*#* *The Refinement Lemmas

Here we resume the results proved in four different files.  The aim is to prove the following result (last part of Theorem 2.9 of Bishop 1967):

%\noindent\textbf{%#<b>#Theorem#</b>#%}% Let [f] be a continuous function on a
compact interval [[a,b]] with modulus of continuity%\footnote{%# (#From our
point of view, the modulus of continuity is simply the proof that [f] is
continuous.#)#%}% [omega].
Let [P] be a partition of [[a,b]] and [eps [>] Zero] be such that
[mesh(P)  [<]  omega(eps)].
Then
%\[\left|S(f,P)-\int_a^bf(x)dx\right|\leq\varepsilon(b-a),\]%#|S(f,P)-&int;f(x)dx|&le;&epsilon;(b-a)#
where [S(f,P)] denotes any sum of the function [f] respecting the partition
[P] (as previously defined).

The proof of this theorem relies on the fact that for any two partitions [P]
and [R] of [[a,b]] it is possible to define a partition [Q] which is
``almost'' a common refinement of [P] and [R]---that is, given [eps [>] Zero]
it is possible to define [Q] such that for every point [x] of either [P] or
[R] there is a point [y] of [Q] such that [|x[-]y|  [<]  eps].
This requires three separate constructions (done in three separate files)
which are then properly combined to give the final result.  We recommend the
reader to ignore this technical constructions.

First we prove that if [P] and [R] are both
separated (though not necessarily separated from each other) then we can
define a partition [P'] arbitrarily close to [P] (that is, such that given
[alpha [>] Zero] and [xi [>] Zero] [P'] satisfies both
[mesh(P')  [<]  mesh(P) [+] xi] and for every choice of points [x_i] respecting
[P] there is a choice of points [x'_i] respecting [P'] such that
[|S(f,P)-S(f,P')|  [<]  alpha]) that is separated from [R].

Then we prove that given any partition [P]
and assuming [a  [#]  b] we can define a partition [P'] arbitrarily close to
[P] (in the same sense as above) which is separated.

Finally we prove that every two separated
partitions [P] and [R] have a common refinement---as every two points in [P]
and [R] are apart, we can decide which one is smaller.  We use here the
technical results about ordering that we proved in the file [IntegralLemmas.v].

Using the results from these files, we prove our main lemma in several steps
(and versions).

%\begin{convention}% Throughout this section:
 - [a,b:IR] and [I] denotes [[a,b]];
 - [F] is a partial function continuous in [I].

%\end{convention}%
*)

inline cic:/CoRN/ftc/RefLemma/a.var.

inline cic:/CoRN/ftc/RefLemma/b.var.

inline cic:/CoRN/ftc/RefLemma/Hab.var.

(* begin hide *)

inline cic:/CoRN/ftc/RefLemma/I.con.

(* end hide *)

inline cic:/CoRN/ftc/RefLemma/F.var.

inline cic:/CoRN/ftc/RefLemma/contF.var.

inline cic:/CoRN/ftc/RefLemma/incF.var.

(* begin hide *)

inline cic:/CoRN/ftc/RefLemma/contF'.con.

(* end hide *)

(* UNEXPORTED
Section First_Refinement_Lemma.
*)

(*#*
This is the first part of the proof of Theorem 2.9.

%\begin{convention}%
 - [P, Q] are partitions of [I] with, respectively, [n] and [m] points;
 - [Q] is a refinement of [P];
 - [e] is a positive real number;
 - [d] is the modulus of continuity of [F] for [e];
 - the mesh of [P] is less or equal to [d];
 - [fP] and [fQ] are choices of points respecting the partitions [P] and [Q],
respectively.

%\end{convention}%
*)

inline cic:/CoRN/ftc/RefLemma/e.var.

inline cic:/CoRN/ftc/RefLemma/He.var.

(* begin hide *)

inline cic:/CoRN/ftc/RefLemma/d.con.

(* end hide *)

inline cic:/CoRN/ftc/RefLemma/m.var.

inline cic:/CoRN/ftc/RefLemma/n.var.

inline cic:/CoRN/ftc/RefLemma/P.var.

inline cic:/CoRN/ftc/RefLemma/HMesh.var.

inline cic:/CoRN/ftc/RefLemma/Q.var.

inline cic:/CoRN/ftc/RefLemma/Href.var.

inline cic:/CoRN/ftc/RefLemma/fP.var.

inline cic:/CoRN/ftc/RefLemma/HfP.var.

inline cic:/CoRN/ftc/RefLemma/HfP'.var.

inline cic:/CoRN/ftc/RefLemma/fQ.var.

inline cic:/CoRN/ftc/RefLemma/HfQ.var.

inline cic:/CoRN/ftc/RefLemma/HfQ'.var.

(* begin hide *)

inline cic:/CoRN/ftc/RefLemma/sub.con.

inline cic:/CoRN/ftc/RefLemma/RL_sub_0.con.

inline cic:/CoRN/ftc/RefLemma/RL_sub_n.con.

inline cic:/CoRN/ftc/RefLemma/RL_sub_mon.con.

inline cic:/CoRN/ftc/RefLemma/RL_sub_mon'.con.

inline cic:/CoRN/ftc/RefLemma/RL_sub_hyp.con.

inline cic:/CoRN/ftc/RefLemma/RL_sub_S.con.

inline cic:/CoRN/ftc/RefLemma/H.con.

inline cic:/CoRN/ftc/RefLemma/H'.con.

inline cic:/CoRN/ftc/RefLemma/H0.con.

inline cic:/CoRN/ftc/RefLemma/RL_sub_SS.con.

inline cic:/CoRN/ftc/RefLemma/RL_h.con.

inline cic:/CoRN/ftc/RefLemma/RL_g.con.

inline cic:/CoRN/ftc/RefLemma/ref_calc1.con.

inline cic:/CoRN/ftc/RefLemma/ref_calc2.con.

inline cic:/CoRN/ftc/RefLemma/ref_calc3.con.

inline cic:/CoRN/ftc/RefLemma/ref_calc4.con.

inline cic:/CoRN/ftc/RefLemma/ref_calc5.con.

inline cic:/CoRN/ftc/RefLemma/ref_calc6.con.

inline cic:/CoRN/ftc/RefLemma/ref_calc7.con.

inline cic:/CoRN/ftc/RefLemma/ref_calc8.con.

(* end hide *)

inline cic:/CoRN/ftc/RefLemma/first_refinement_lemma.con.

(* UNEXPORTED
End First_Refinement_Lemma.
*)

(* UNEXPORTED
Section Second_Refinement_Lemma.
*)

(*#*
This is inequality (2.6.7).

%\begin{convention}%
 - [P, Q, R] are partitions of [I] with, respectively, [j, n] and [k] points;
 - [Q] is a common refinement of [P] and [R];
 - [e, e'] are positive real numbers;
 - [d, d'] are the moduli of continuity of [F] for [e, e'];
 - the Mesh of [P] is less or equal to [d];
 - the Mesh of [R] is less or equal to [d'];
 - [fP, fQ] and [fR] are choices of points respecting the partitions [P, Q]
and [R], respectively.

%\end{convention}%
*)

inline cic:/CoRN/ftc/RefLemma/n.var.

inline cic:/CoRN/ftc/RefLemma/j.var.

inline cic:/CoRN/ftc/RefLemma/k.var.

inline cic:/CoRN/ftc/RefLemma/P.var.

inline cic:/CoRN/ftc/RefLemma/Q.var.

inline cic:/CoRN/ftc/RefLemma/R.var.

inline cic:/CoRN/ftc/RefLemma/HrefP.var.

inline cic:/CoRN/ftc/RefLemma/HrefR.var.

inline cic:/CoRN/ftc/RefLemma/e.var.

inline cic:/CoRN/ftc/RefLemma/e'.var.

inline cic:/CoRN/ftc/RefLemma/He.var.

inline cic:/CoRN/ftc/RefLemma/He'.var.

(* begin hide *)

inline cic:/CoRN/ftc/RefLemma/d.con.

inline cic:/CoRN/ftc/RefLemma/d'.con.

(* end hide *)

inline cic:/CoRN/ftc/RefLemma/HMeshP.var.

inline cic:/CoRN/ftc/RefLemma/HMeshR.var.

inline cic:/CoRN/ftc/RefLemma/fP.var.

inline cic:/CoRN/ftc/RefLemma/HfP.var.

inline cic:/CoRN/ftc/RefLemma/HfP'.var.

inline cic:/CoRN/ftc/RefLemma/fR.var.

inline cic:/CoRN/ftc/RefLemma/HfR.var.

inline cic:/CoRN/ftc/RefLemma/HfR'.var.

inline cic:/CoRN/ftc/RefLemma/second_refinement_lemma.con.

(* UNEXPORTED
End Second_Refinement_Lemma.
*)

(* UNEXPORTED
Section Third_Refinement_Lemma.
*)

(*#*
This is an approximation of inequality (2.6.7), but without assuming the existence of a common refinement of [P] and [R].

%\begin{convention}%
 - [P, R] are partitions of [I] with, respectively, [n] and [m] points;
 - [e, e'] are positive real numbers;
 - [d, d'] are the moduli of continuity of [F] for [e, e'];
 - the Mesh of [P] is less than [d];
 - the Mesh of [R] is less than [d'];
 - [fP] and [fR] are choices of points respecting the partitions [P] and [R],
respectively;
 - [beta] is a positive real number.

%\end{convention}%
*)

inline cic:/CoRN/ftc/RefLemma/n.var.

inline cic:/CoRN/ftc/RefLemma/m.var.

inline cic:/CoRN/ftc/RefLemma/P.var.

inline cic:/CoRN/ftc/RefLemma/R.var.

inline cic:/CoRN/ftc/RefLemma/e.var.

inline cic:/CoRN/ftc/RefLemma/e'.var.

inline cic:/CoRN/ftc/RefLemma/He.var.

inline cic:/CoRN/ftc/RefLemma/He'.var.

(* begin hide *)

inline cic:/CoRN/ftc/RefLemma/d.con.

inline cic:/CoRN/ftc/RefLemma/d'.con.

(* end hide *)

inline cic:/CoRN/ftc/RefLemma/HMeshP.var.

inline cic:/CoRN/ftc/RefLemma/HMeshR.var.

inline cic:/CoRN/ftc/RefLemma/fP.var.

inline cic:/CoRN/ftc/RefLemma/HfP.var.

inline cic:/CoRN/ftc/RefLemma/HfP'.var.

inline cic:/CoRN/ftc/RefLemma/fR.var.

inline cic:/CoRN/ftc/RefLemma/HfR.var.

inline cic:/CoRN/ftc/RefLemma/HfR'.var.

inline cic:/CoRN/ftc/RefLemma/Hab'.var.

inline cic:/CoRN/ftc/RefLemma/beta.var.

inline cic:/CoRN/ftc/RefLemma/Hbeta.var.

(* begin hide *)

inline cic:/CoRN/ftc/RefLemma/alpha.con.

inline cic:/CoRN/ftc/RefLemma/RL_alpha.con.

inline cic:/CoRN/ftc/RefLemma/csi1.con.

inline cic:/CoRN/ftc/RefLemma/RL_csi1.con.

inline cic:/CoRN/ftc/RefLemma/delta1.con.

inline cic:/CoRN/ftc/RefLemma/RL_delta1.con.

inline cic:/CoRN/ftc/RefLemma/P'.con.

inline cic:/CoRN/ftc/RefLemma/RL_P'_sep.con.

inline cic:/CoRN/ftc/RefLemma/RL_P'_Mesh.con.

inline cic:/CoRN/ftc/RefLemma/fP'.con.

inline cic:/CoRN/ftc/RefLemma/RL_fP'_in_P'.con.

inline cic:/CoRN/ftc/RefLemma/RL_P'_P_sum.con.

inline cic:/CoRN/ftc/RefLemma/csi2.con.

inline cic:/CoRN/ftc/RefLemma/RL_csi2.con.

inline cic:/CoRN/ftc/RefLemma/delta2.con.

inline cic:/CoRN/ftc/RefLemma/RL_delta2.con.

inline cic:/CoRN/ftc/RefLemma/R'.con.

inline cic:/CoRN/ftc/RefLemma/RL_R'_sep.con.

inline cic:/CoRN/ftc/RefLemma/RL_R'_Mesh.con.

inline cic:/CoRN/ftc/RefLemma/fR'.con.

inline cic:/CoRN/ftc/RefLemma/RL_fR'_in_R'.con.

inline cic:/CoRN/ftc/RefLemma/RL_R'_R_sum.con.

inline cic:/CoRN/ftc/RefLemma/csi3.con.

inline cic:/CoRN/ftc/RefLemma/RL_csi3.con.

inline cic:/CoRN/ftc/RefLemma/Q.con.

inline cic:/CoRN/ftc/RefLemma/RL_Q_Mesh.con.

inline cic:/CoRN/ftc/RefLemma/RL_Q_sep.con.

inline cic:/CoRN/ftc/RefLemma/fQ.con.

inline cic:/CoRN/ftc/RefLemma/RL_fQ_in_Q.con.

inline cic:/CoRN/ftc/RefLemma/RL_Q_P'_sum.con.

(* end hide *)

inline cic:/CoRN/ftc/RefLemma/third_refinement_lemma.con.

(* UNEXPORTED
End Third_Refinement_Lemma.
*)

(* UNEXPORTED
Section Fourth_Refinement_Lemma.
*)

(* begin hide *)

inline cic:/CoRN/ftc/RefLemma/Fa.con.

inline cic:/CoRN/ftc/RefLemma/RL_sum_lemma_aux.con.

(* end hide *)

(*#*
Finally, this is inequality (2.6.7) exactly as stated (same conventions as
above)
*)

inline cic:/CoRN/ftc/RefLemma/n.var.

inline cic:/CoRN/ftc/RefLemma/m.var.

inline cic:/CoRN/ftc/RefLemma/P.var.

inline cic:/CoRN/ftc/RefLemma/R.var.

inline cic:/CoRN/ftc/RefLemma/e.var.

inline cic:/CoRN/ftc/RefLemma/e'.var.

inline cic:/CoRN/ftc/RefLemma/He.var.

inline cic:/CoRN/ftc/RefLemma/He'.var.

(* begin hide *)

inline cic:/CoRN/ftc/RefLemma/d.con.

inline cic:/CoRN/ftc/RefLemma/d'.con.

(* end hide *)

inline cic:/CoRN/ftc/RefLemma/HMeshP.var.

inline cic:/CoRN/ftc/RefLemma/HMeshR.var.

inline cic:/CoRN/ftc/RefLemma/fP.var.

inline cic:/CoRN/ftc/RefLemma/HfP.var.

inline cic:/CoRN/ftc/RefLemma/HfP'.var.

inline cic:/CoRN/ftc/RefLemma/fR.var.

inline cic:/CoRN/ftc/RefLemma/HfR.var.

inline cic:/CoRN/ftc/RefLemma/HfR'.var.

(* begin show *)

inline cic:/CoRN/ftc/RefLemma/Hab'.var.

(* end show *)

inline cic:/CoRN/ftc/RefLemma/fourth_refinement_lemma.con.

(* UNEXPORTED
End Fourth_Refinement_Lemma.
*)

(* UNEXPORTED
Section Main_Refinement_Lemma.
*)

(*#* We finish by presenting Theorem 9. *)

inline cic:/CoRN/ftc/RefLemma/n.var.

inline cic:/CoRN/ftc/RefLemma/m.var.

inline cic:/CoRN/ftc/RefLemma/P.var.

inline cic:/CoRN/ftc/RefLemma/R.var.

inline cic:/CoRN/ftc/RefLemma/e.var.

inline cic:/CoRN/ftc/RefLemma/e'.var.

inline cic:/CoRN/ftc/RefLemma/He.var.

inline cic:/CoRN/ftc/RefLemma/He'.var.

(* begin hide *)

inline cic:/CoRN/ftc/RefLemma/d.con.

inline cic:/CoRN/ftc/RefLemma/d'.con.

(* end hide *)

inline cic:/CoRN/ftc/RefLemma/HMeshP.var.

inline cic:/CoRN/ftc/RefLemma/HMeshR.var.

inline cic:/CoRN/ftc/RefLemma/fP.var.

inline cic:/CoRN/ftc/RefLemma/HfP.var.

inline cic:/CoRN/ftc/RefLemma/HfP'.var.

inline cic:/CoRN/ftc/RefLemma/fR.var.

inline cic:/CoRN/ftc/RefLemma/HfR.var.

inline cic:/CoRN/ftc/RefLemma/HfR'.var.

inline cic:/CoRN/ftc/RefLemma/refinement_lemma.con.

(* UNEXPORTED
End Main_Refinement_Lemma.
*)

(* UNEXPORTED
End Refinement_Lemma.
*)


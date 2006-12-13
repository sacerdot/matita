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

set "baseuri" "cic:/matita/CoRN-Decl/ftc/Partitions".

include "CoRN.ma".

(* $Id: Partitions.v,v 1.7 2004/04/23 10:01:00 lcf Exp $ *)

include "ftc/Continuity.ma".

(*#* printing Partition_Sum %\ensuremath{\sum_P}% #&sum;<sub>P</sub># *)

(* UNEXPORTED
Section Definitions
*)

(*#* *Partitions

We now begin to lay the way for the definition of Riemann integral.  This will
be done through the definition of a sequence of
sums that is proved to be convergent; in order to do that, we first
need to do a bit of work on partitions.

**Definitions

A partition is defined as a record type.  For each compact interval [[a,b]]
and each natural number [n], a partition of [[a,b]] with [n+1] points is a
choice of real numbers [a [=] a0 [<=] a1 [<=] an [=] b]; the following
specification works as follows:
 - [Pts] is the function that chooses the points (it is declared as a
coercion);
 - [prf1] states that [Pts] is a setoid function;
 - [prf2] states that the points are ordered;
 - [start] requires that [a0 [=] a] and
 - [finish] requires that [an [=] b].

*)

inline "cic:/CoRN/ftc/Partitions/Partition.ind".

coercion cic:/matita/CoRN-Decl/ftc/Partitions/Pts.con 0 (* compounds *).

(*#* Two immediate consequences of this are that [ai [<=] aj] whenever
[i < j] and that [ai] is in [[a,b]] for all [i].
*)

inline "cic:/CoRN/ftc/Partitions/Partition_mon.con".

inline "cic:/CoRN/ftc/Partitions/Partition_in_compact.con".

(*#*
Each partition of [[a,b]] implies a partition of the interval
$[a,a_{n-1}]$#[a,a<sub>n-1</sub>]#.  This partition will play an
important role in much of our future work, so we take some care to
define it.
*)

inline "cic:/CoRN/ftc/Partitions/part_pred_lemma.con".

inline "cic:/CoRN/ftc/Partitions/Partition_Dom.con".

(*#*
The mesh of a partition is the greatest distance between two
consecutive points.  For convenience's sake we also define the dual
concept, which is very helpful in some situations.  In order to do
this, we begin by building a list with all the distances between
consecutive points; next we only need to extract the maximum and the
minimum of this list. Notice that this list is nonempty except in the
case when [a [=] b] and [n = 0]; this means that the convention we took
of defining the minimum and maximum of the empty list to be [0] actually
helps us in this case.
*)

inline "cic:/CoRN/ftc/Partitions/Part_Mesh_List.con".

inline "cic:/CoRN/ftc/Partitions/Mesh.con".

inline "cic:/CoRN/ftc/Partitions/AntiMesh.con".

(*#*
Even partitions (partitions where all the points are evenly spaced)
will also play a central role in our work; the first two lemmas are
presented simply to make the definition of even partition lighter.
*)

inline "cic:/CoRN/ftc/Partitions/even_part_1.con".

inline "cic:/CoRN/ftc/Partitions/even_part_2.con".

inline "cic:/CoRN/ftc/Partitions/Even_Partition.con".

(* UNEXPORTED
Section Refinements
*)

alias id "a" = "cic:/CoRN/ftc/Partitions/Definitions/Refinements/a.var".

alias id "b" = "cic:/CoRN/ftc/Partitions/Definitions/Refinements/b.var".

alias id "Hab" = "cic:/CoRN/ftc/Partitions/Definitions/Refinements/Hab.var".

alias id "m" = "cic:/CoRN/ftc/Partitions/Definitions/Refinements/m.var".

alias id "n" = "cic:/CoRN/ftc/Partitions/Definitions/Refinements/n.var".

alias id "P" = "cic:/CoRN/ftc/Partitions/Definitions/Refinements/P.var".

alias id "Q" = "cic:/CoRN/ftc/Partitions/Definitions/Refinements/Q.var".

(*#*
We now define what it means for a partition [Q] to be a refinement of
[P] and prove the main property of refinements.
*)

inline "cic:/CoRN/ftc/Partitions/Refinement.con".

inline "cic:/CoRN/ftc/Partitions/Refinement_prop.con".

(*#*
We will also need to consider arbitrary sums %of the form
\[\sum_{i=0}^{n-1}f(x_i)(a_{i+1}-a_i)\]%#of
f(x<sub>i</sub>)(a<sub>i+1</sub>-a<sub>i</sub>)# where
$x_i\in[a_i,a_{i+1}]$#x<sub>i</sub>&isin;[a<sub>i</sub>,a<sub>i+1</sub>]#.
For this, we again need a choice function [x] which has to satisfy
some condition.  We define the condition and the sum for a fixed [P]:
*)

inline "cic:/CoRN/ftc/Partitions/Points_in_Partition.con".

inline "cic:/CoRN/ftc/Partitions/Pts_part_lemma.con".

inline "cic:/CoRN/ftc/Partitions/Partition_Sum.con".

(* UNEXPORTED
End Refinements
*)

(* UNEXPORTED
Implicit Arguments Points_in_Partition [a b Hab n].
*)

(* UNEXPORTED
Implicit Arguments Partition_Sum [a b Hab n P g F].
*)

(*#* **Constructions

We now formalize some trivial and helpful constructions.

%\begin{convention}% We will assume a fixed compact interval [[a,b]], denoted by [I].
%\end{convention}%
*)

alias id "a" = "cic:/CoRN/ftc/Partitions/Definitions/a.var".

alias id "b" = "cic:/CoRN/ftc/Partitions/Definitions/b.var".

alias id "Hab" = "cic:/CoRN/ftc/Partitions/Definitions/Hab.var".

(* begin hide *)

inline "cic:/CoRN/ftc/Partitions/Definitions/I.con" "Definitions__".

(* end hide *)

(* UNEXPORTED
Section Getting_Points
*)

(*#*
From a partition we always have a canonical choice of points at which
to evaluate a function: just take all but the last points of the
partition.

%\begin{convention}% Let [Q] be a partition of [I] with [m] points.
%\end{convention}%
*)

alias id "m" = "cic:/CoRN/ftc/Partitions/Definitions/Getting_Points/m.var".

alias id "Q" = "cic:/CoRN/ftc/Partitions/Definitions/Getting_Points/Q.var".

inline "cic:/CoRN/ftc/Partitions/Partition_imp_points.con".

inline "cic:/CoRN/ftc/Partitions/Partition_imp_points_1.con".

inline "cic:/CoRN/ftc/Partitions/Partition_imp_points_2.con".

(* UNEXPORTED
End Getting_Points
*)

(*#*
As a corollary, given any continuous function [F] and a natural number we have an immediate choice of a sum of [F] in [[a,b]].
*)

alias id "F" = "cic:/CoRN/ftc/Partitions/Definitions/F.var".

alias id "contF" = "cic:/CoRN/ftc/Partitions/Definitions/contF.var".

inline "cic:/CoRN/ftc/Partitions/Even_Partition_Sum.con".

(* UNEXPORTED
End Definitions
*)

(* UNEXPORTED
Implicit Arguments Partition [a b].
*)

(* UNEXPORTED
Implicit Arguments Partition_Dom [a b Hab n].
*)

(* UNEXPORTED
Implicit Arguments Mesh [a b Hab n].
*)

(* UNEXPORTED
Implicit Arguments AntiMesh [a b Hab n].
*)

(* UNEXPORTED
Implicit Arguments Pts [a b Hab lng].
*)

(* UNEXPORTED
Implicit Arguments Part_Mesh_List [n a b Hab].
*)

(* UNEXPORTED
Implicit Arguments Points_in_Partition [a b Hab n].
*)

(* UNEXPORTED
Implicit Arguments Partition_Sum [a b Hab n P g F].
*)

(* UNEXPORTED
Implicit Arguments Even_Partition [a b].
*)

(* UNEXPORTED
Implicit Arguments Even_Partition_Sum [a b].
*)

(* UNEXPORTED
Implicit Arguments Refinement [a b Hab n m].
*)

(* UNEXPORTED
Hint Resolve start finish: algebra.
*)

(* UNEXPORTED
Section Lemmas
*)

(*#* ** Properties of the mesh

If a partition has more than one point then its mesh list is nonempty.
*)

inline "cic:/CoRN/ftc/Partitions/length_Part_Mesh_List.con".

(*#*
Any element of the auxiliary list defined to calculate the mesh of a partition has a very specific form.
*)

inline "cic:/CoRN/ftc/Partitions/Part_Mesh_List_lemma.con".

(*#*
Mesh and antimesh are always nonnegative.
*)

inline "cic:/CoRN/ftc/Partitions/Mesh_nonneg.con".

inline "cic:/CoRN/ftc/Partitions/AntiMesh_nonneg.con".

(*#*
Most important, [AntiMesh] and [Mesh] provide lower and upper bounds
for the distance between any two consecutive points in a partition.

%\begin{convention}% Let [I] be [[a,b]] and [P] be a partition of [I]
with [n] points.
%\end{convention}%
*)

alias id "a" = "cic:/CoRN/ftc/Partitions/Lemmas/a.var".

alias id "b" = "cic:/CoRN/ftc/Partitions/Lemmas/b.var".

(* begin hide *)

inline "cic:/CoRN/ftc/Partitions/Lemmas/I.con" "Lemmas__".

(* end hide *)

alias id "Hab" = "cic:/CoRN/ftc/Partitions/Lemmas/Hab.var".

alias id "n" = "cic:/CoRN/ftc/Partitions/Lemmas/n.var".

alias id "P" = "cic:/CoRN/ftc/Partitions/Lemmas/P.var".

inline "cic:/CoRN/ftc/Partitions/Mesh_lemma.con".

inline "cic:/CoRN/ftc/Partitions/AntiMesh_lemma.con".

inline "cic:/CoRN/ftc/Partitions/Mesh_leEq.con".

(* UNEXPORTED
End Lemmas
*)

(* UNEXPORTED
Section Even_Partitions
*)

(*#* More technical stuff.  Two equal partitions have the same mesh.
*)

inline "cic:/CoRN/ftc/Partitions/Mesh_wd.con".

inline "cic:/CoRN/ftc/Partitions/Mesh_wd'.con".

(*#*
The mesh of an even partition is easily calculated.
*)

inline "cic:/CoRN/ftc/Partitions/even_partition_Mesh.con".

(*#* ** Miscellaneous
%\begin{convention}% Throughout this section, let [a,b:IR] and [I] be [[a,b]].
%\end{convention}%
*)

alias id "a" = "cic:/CoRN/ftc/Partitions/Even_Partitions/a.var".

alias id "b" = "cic:/CoRN/ftc/Partitions/Even_Partitions/b.var".

(* begin hide *)

inline "cic:/CoRN/ftc/Partitions/Even_Partitions/I.con" "Even_Partitions__".

(* end hide *)

alias id "Hab" = "cic:/CoRN/ftc/Partitions/Even_Partitions/Hab.var".

(*#*
An interesting property: in a partition, if [ai [<] aj] then [i < j].
*)

inline "cic:/CoRN/ftc/Partitions/Partition_Points_mon.con".

inline "cic:/CoRN/ftc/Partitions/refinement_resp_mult.con".

(*#*
%\begin{convention}% Assume [m,n] are positive natural numbers and
denote by [P] and [Q] the even partitions with, respectively, [m] and
[n] points.
%\end{convention}%

Even partitions always have a common refinement.
*)

alias id "m" = "cic:/CoRN/ftc/Partitions/Even_Partitions/m.var".

alias id "n" = "cic:/CoRN/ftc/Partitions/Even_Partitions/n.var".

alias id "Hm" = "cic:/CoRN/ftc/Partitions/Even_Partitions/Hm.var".

alias id "Hn" = "cic:/CoRN/ftc/Partitions/Even_Partitions/Hn.var".

(* begin hide *)

inline "cic:/CoRN/ftc/Partitions/Even_Partitions/P.con" "Even_Partitions__".

inline "cic:/CoRN/ftc/Partitions/Even_Partitions/Q.con" "Even_Partitions__".

(* end hide *)

inline "cic:/CoRN/ftc/Partitions/even_partition_refinement.con".

(* UNEXPORTED
End Even_Partitions
*)

(* UNEXPORTED
Section More_Definitions
*)

(*#* ** Separation

Some auxiliary definitions.  A partition is said to be separated if all its points are distinct.
*)

alias id "a" = "cic:/CoRN/ftc/Partitions/More_Definitions/a.var".

alias id "b" = "cic:/CoRN/ftc/Partitions/More_Definitions/b.var".

alias id "Hab" = "cic:/CoRN/ftc/Partitions/More_Definitions/Hab.var".

inline "cic:/CoRN/ftc/Partitions/_Separated.con".

(*#*
Two partitions are said to be (mutually) separated if they are both
separated and all their points are distinct (except for the
endpoints).

%\begin{convention}% Let [P,Q] be partitions of [I] with,
respectively, [n] and [m] points.
%\end{convention}%
*)

alias id "n" = "cic:/CoRN/ftc/Partitions/More_Definitions/n.var".

alias id "m" = "cic:/CoRN/ftc/Partitions/More_Definitions/m.var".

alias id "P" = "cic:/CoRN/ftc/Partitions/More_Definitions/P.var".

alias id "Q" = "cic:/CoRN/ftc/Partitions/More_Definitions/Q.var".

inline "cic:/CoRN/ftc/Partitions/Separated.con".

(* UNEXPORTED
End More_Definitions
*)

(* UNEXPORTED
Implicit Arguments _Separated [a b Hab n].
*)

(* UNEXPORTED
Implicit Arguments Separated [a b Hab n m].
*)

(* UNEXPORTED
Section Sep_Partitions
*)

alias id "a" = "cic:/CoRN/ftc/Partitions/Sep_Partitions/a.var".

alias id "b" = "cic:/CoRN/ftc/Partitions/Sep_Partitions/b.var".

(* begin hide *)

inline "cic:/CoRN/ftc/Partitions/Sep_Partitions/I.con" "Sep_Partitions__".

(* end hide *)

alias id "Hab" = "cic:/CoRN/ftc/Partitions/Sep_Partitions/Hab.var".

(*#*
The antimesh of a separated partition is always positive.
*)

inline "cic:/CoRN/ftc/Partitions/pos_AntiMesh.con".

(*#*
A partition can have only one point iff the endpoints of the interval
are the same; moreover, if the partition is separated and the
endpoints of the interval are the same then it must have one point.
*)

inline "cic:/CoRN/ftc/Partitions/partition_length_zero.con".

inline "cic:/CoRN/ftc/Partitions/_Separated_imp_length_zero.con".

inline "cic:/CoRN/ftc/Partitions/partition_less_imp_gt_zero.con".

(* UNEXPORTED
End Sep_Partitions
*)


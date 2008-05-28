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

set "baseuri" "cic:/matita/CoRN-Decl/algebra/CSetoidFun".

include "CoRN.ma".

(* $Id: CSetoidFun.v,v 1.10 2004/04/23 10:00:53 lcf Exp $ *)

include "algebra/CSetoids.ma".

(* UNEXPORTED
Section unary_function_composition
*)

(*#* ** Composition of Setoid functions

Let [S1],  [S2] and [S3] be setoids, [f] a
setoid function from [S1] to [S2], and [g] from [S2]
to [S3] in the following definition of composition.  *)

alias id "S1" = "cic:/CoRN/algebra/CSetoidFun/unary_function_composition/S1.var".

alias id "S2" = "cic:/CoRN/algebra/CSetoidFun/unary_function_composition/S2.var".

alias id "S3" = "cic:/CoRN/algebra/CSetoidFun/unary_function_composition/S3.var".

alias id "f" = "cic:/CoRN/algebra/CSetoidFun/unary_function_composition/f.var".

alias id "g" = "cic:/CoRN/algebra/CSetoidFun/unary_function_composition/g.var".

inline "cic:/CoRN/algebra/CSetoidFun/compose_CSetoid_fun.con".

(* UNEXPORTED
End unary_function_composition
*)

(* UNEXPORTED
Section unary_and_binary_function_composition
*)

inline "cic:/CoRN/algebra/CSetoidFun/compose_CSetoid_bin_un_fun.con".

inline "cic:/CoRN/algebra/CSetoidFun/compose_CSetoid_bin_fun.con".

inline "cic:/CoRN/algebra/CSetoidFun/compose_CSetoid_un_bin_fun.con".

(* UNEXPORTED
End unary_and_binary_function_composition
*)

(*#* ***Projections
*)

(* UNEXPORTED
Section function_projection
*)

inline "cic:/CoRN/algebra/CSetoidFun/proj_bin_fun.con".

inline "cic:/CoRN/algebra/CSetoidFun/projected_bin_fun.con".

(* UNEXPORTED
End function_projection
*)

(* UNEXPORTED
Section BinProj
*)

alias id "S" = "cic:/CoRN/algebra/CSetoidFun/BinProj/S.var".

inline "cic:/CoRN/algebra/CSetoidFun/binproj1.con".

inline "cic:/CoRN/algebra/CSetoidFun/binproj1_strext.con".

inline "cic:/CoRN/algebra/CSetoidFun/cs_binproj1.con".

(* UNEXPORTED
End BinProj
*)

(*#* **Combining operations
%\begin{convention}% Let [S1], [S2] and [S3] be setoids.
%\end{convention}%
*)

(* UNEXPORTED
Section CombiningOperations
*)

alias id "S1" = "cic:/CoRN/algebra/CSetoidFun/CombiningOperations/S1.var".

alias id "S2" = "cic:/CoRN/algebra/CSetoidFun/CombiningOperations/S2.var".

alias id "S3" = "cic:/CoRN/algebra/CSetoidFun/CombiningOperations/S3.var".

(*#*
In the following definition, we assume [f] is a setoid function from
[S1] to [S2], and [op] is an unary operation on [S2].
Then [opOnFun] is the composition [op] after [f].
*)

(* UNEXPORTED
Section CombiningUnaryOperations
*)

alias id "f" = "cic:/CoRN/algebra/CSetoidFun/CombiningOperations/CombiningUnaryOperations/f.var".

alias id "op" = "cic:/CoRN/algebra/CSetoidFun/CombiningOperations/CombiningUnaryOperations/op.var".

inline "cic:/CoRN/algebra/CSetoidFun/opOnFun.con".

(* UNEXPORTED
End CombiningUnaryOperations
*)

(* UNEXPORTED
End CombiningOperations
*)

(*#* **Partial Functions

In this section we define a concept of partial function for an
arbitrary setoid.  Essentially, a partial function is what would be
expected---a predicate on the setoid in question and a total function
from the set of points satisfying that predicate to the setoid.  There
is one important limitations to this approach: first, the record we
obtain has type [Type], meaning that we can't use, for instance,
elimination of existential quantifiers.

Furthermore, for reasons we will explain ahead, partial functions will
not be defined via the [CSetoid_fun] record, but the whole structure
will be incorporated in a new record.

Finally, notice that to be completely general the domains of the
functions have to be characterized by a [CProp]-valued predicate;
otherwise, the use you can make of a function will be %\emph{%#<i>#a
priori#</i>#%}% restricted at the moment it is defined.

Before we state our definitions we need to do some work on domains.
*)

(* UNEXPORTED
Section SubSets_of_G
*)

(*#* ***Subsets of Setoids

Subsets of a setoid will be identified with predicates from the
carrier set of the setoid into [CProp].  At this stage, we do not make
any assumptions about these predicates.

We will begin by defining elementary operations on predicates, along
with their basic properties.  In particular, we will work with well
defined predicates, so we will prove that these operations preserve
welldefinedness.

%\begin{convention}% Let [S:CSetoid] and [P,Q:S->CProp].
%\end{convention}%
*)

alias id "S" = "cic:/CoRN/algebra/CSetoidFun/SubSets_of_G/S.var".

(* UNEXPORTED
Section Conjunction
*)

alias id "P" = "cic:/CoRN/algebra/CSetoidFun/SubSets_of_G/Conjunction/P.var".

alias id "Q" = "cic:/CoRN/algebra/CSetoidFun/SubSets_of_G/Conjunction/Q.var".

inline "cic:/CoRN/algebra/CSetoidFun/conjP.con".

inline "cic:/CoRN/algebra/CSetoidFun/prj1.con".

inline "cic:/CoRN/algebra/CSetoidFun/prj2.con".

inline "cic:/CoRN/algebra/CSetoidFun/conj_wd.con".

(* UNEXPORTED
End Conjunction
*)

(* UNEXPORTED
Section Disjunction
*)

alias id "P" = "cic:/CoRN/algebra/CSetoidFun/SubSets_of_G/Disjunction/P.var".

alias id "Q" = "cic:/CoRN/algebra/CSetoidFun/SubSets_of_G/Disjunction/Q.var".

(*#*
Although at this stage we never use it, for completeness's sake we also treat disjunction (corresponding to union of subsets).
*)

inline "cic:/CoRN/algebra/CSetoidFun/disj.con".

inline "cic:/CoRN/algebra/CSetoidFun/inj1.con".

inline "cic:/CoRN/algebra/CSetoidFun/inj2.con".

inline "cic:/CoRN/algebra/CSetoidFun/disj_wd.con".

(* UNEXPORTED
End Disjunction
*)

(* UNEXPORTED
Section Extension
*)

(*#*
The next definition is a bit tricky, and is useful for choosing among the elements that satisfy a predicate [P] those that also satisfy [R] in the case where [R] is only defined for elements satisfying [P]---consider [R] to be a condition on the image of an object via a function with domain [P].  We chose to call this operation [extension].
*)

alias id "P" = "cic:/CoRN/algebra/CSetoidFun/SubSets_of_G/Extension/P.var".

alias id "R" = "cic:/CoRN/algebra/CSetoidFun/SubSets_of_G/Extension/R.var".

inline "cic:/CoRN/algebra/CSetoidFun/extend.con".

inline "cic:/CoRN/algebra/CSetoidFun/ext1.con".

inline "cic:/CoRN/algebra/CSetoidFun/ext2_a.con".

inline "cic:/CoRN/algebra/CSetoidFun/ext2.con".

inline "cic:/CoRN/algebra/CSetoidFun/extension_wd.con".

(* UNEXPORTED
End Extension
*)

(* UNEXPORTED
End SubSets_of_G
*)

(* NOTATION
Notation Conj := (conjP _).
*)

(* UNEXPORTED
Implicit Arguments disj [S].
*)

(* UNEXPORTED
Implicit Arguments extend [S].
*)

(* UNEXPORTED
Implicit Arguments ext1 [S P R x].
*)

(* UNEXPORTED
Implicit Arguments ext2 [S P R x].
*)

(*#* ***Operations

We are now ready to define the concept of partial function between arbitrary setoids.
*)

inline "cic:/CoRN/algebra/CSetoidFun/BinPartFunct.ind".

coercion cic:/matita/CoRN-Decl/algebra/CSetoidFun/bpfpfun.con 0 (* compounds *).

(* NOTATION
Notation BDom := (bpfdom _ _).
*)

(* UNEXPORTED
Implicit Arguments bpfpfun [S1 S2].
*)

(*#*
The next lemma states that every partial function is well defined.
*)

inline "cic:/CoRN/algebra/CSetoidFun/bpfwdef.con".

(*#* Similar for automorphisms. *)

inline "cic:/CoRN/algebra/CSetoidFun/PartFunct.ind".

coercion cic:/matita/CoRN-Decl/algebra/CSetoidFun/pfpfun.con 0 (* compounds *).

(* NOTATION
Notation Dom := (pfdom _).
*)

(* NOTATION
Notation Part := (pfpfun _).
*)

(* UNEXPORTED
Implicit Arguments pfpfun [S].
*)

(*#*
The next lemma states that every partial function is well defined.
*)

inline "cic:/CoRN/algebra/CSetoidFun/pfwdef.con".

(*#*
A few characteristics of this definition should be explained:
 - The domain of the partial function is characterized by a predicate
that is required to be well defined but not strongly extensional.  The
motivation for this choice comes from two facts: first, one very
important subset of real numbers is the compact interval
[[a,b]]---characterized by the predicate [ fun x : IR => a [<=] x /\ x
[<=] b], which is not strongly extensional; on the other hand, if we
can apply a function to an element [s] of a setoid [S] it seems
reasonable (and at some point we do have to do it) to apply that same
function to any element [s'] which is equal to [s] from the point of
view of the setoid equality.
 - The last two conditions state that [pfpfun] is really a subsetoid
function.  The reason why we do not write it that way is the
following: when applying a partial function [f] to an element [s] of
[S] we also need a proof object [H]; with this definition the object
we get is [f(s,H)], where the proof is kept separate from the object.
Using subsetoid notation, we would get $f(\langle
s,H\rangle)$#f(&lang;s,H&rang;)#; from this we need to apply two
projections to get either the original object or the proof, and we
need to apply an extra constructor to get $f(\langle
s,H\rangle)$#f(&lang;s,H&rang;)# from [s] and [H].  This amounts
to spending more resources when actually working with these objects.
 - This record has type [Type], which is very unfortunate, because it
means in particular that we cannot use the well behaved set
existential quantification over partial functions; however, later on
we will manage to avoid this problem in a way that also justifies that
we don't really need to use that kind of quantification.  Another
approach to this definition that completely avoid this complication
would be to make [PartFunct] a dependent type, receiving the predicate
as an argument.  This does work in that it allows us to give
[PartFunct] type [Set] and do some useful stuff with it; however, we
are not able to define something as simple as an operator that gets a
function and returns its domain (because of the restrictions in the
type elimination rules).  This sounds very unnatural, and soon gets us
into strange problems that yield very unlikely definitions, which is
why we chose to altogether do away with this approach.

%\begin{convention}% All partial functions will henceforth be denoted by capital letters.
%\end{convention}%

We now present some methods for defining partial functions.
*)

(* UNEXPORTED
Hint Resolve CI: core.
*)

(* UNEXPORTED
Section CSetoid_Ops
*)

alias id "S" = "cic:/CoRN/algebra/CSetoidFun/CSetoid_Ops/S.var".

(*#*
To begin with, we want to be able to ``see'' each total function as a partial function.
*)

inline "cic:/CoRN/algebra/CSetoidFun/total_eq_part.con".

(* UNEXPORTED
Section Part_Function_Const
*)

(*#*
In any setoid we can also define constant functions (one for each element of the setoid) and an identity function:

%\begin{convention}% Let [c:S].
%\end{convention}%
*)

alias id "c" = "cic:/CoRN/algebra/CSetoidFun/CSetoid_Ops/Part_Function_Const/c.var".

inline "cic:/CoRN/algebra/CSetoidFun/Fconst.con".

(* UNEXPORTED
End Part_Function_Const
*)

(* UNEXPORTED
Section Part_Function_Id
*)

inline "cic:/CoRN/algebra/CSetoidFun/Fid.con".

(* UNEXPORTED
End Part_Function_Id
*)

(*#*
(These happen to be always total functions, but that is more or less obvious, as we have no information on the setoid; however, we will be able to define partial functions just applying other operators to these ones.)

If we have two setoid functions [F] and [G] we can always compose them.  The domain of our new function will be the set of points [s] in the domain of [F] for which [F(s)] is in the domain of [G]#. #%\footnote{%Notice that the use of extension here is essential.%}.%  The inversion in the order of the variables is done to maintain uniformity with the usual mathematical notation.

%\begin{convention}% Let [G,F:(PartFunct S)] and denote by [Q] and [P], respectively, the predicates characterizing their domains.
%\end{convention}%
*)

(* UNEXPORTED
Section Part_Function_Composition
*)

alias id "G" = "cic:/CoRN/algebra/CSetoidFun/CSetoid_Ops/Part_Function_Composition/G.var".

alias id "F" = "cic:/CoRN/algebra/CSetoidFun/CSetoid_Ops/Part_Function_Composition/F.var".

(* begin hide *)

inline "cic:/CoRN/algebra/CSetoidFun/CSetoid_Ops/Part_Function_Composition/P.con" "CSetoid_Ops__Part_Function_Composition__".

inline "cic:/CoRN/algebra/CSetoidFun/CSetoid_Ops/Part_Function_Composition/Q.con" "CSetoid_Ops__Part_Function_Composition__".

(* end hide *)

inline "cic:/CoRN/algebra/CSetoidFun/CSetoid_Ops/Part_Function_Composition/R.con" "CSetoid_Ops__Part_Function_Composition__".

inline "cic:/CoRN/algebra/CSetoidFun/part_function_comp_strext.con".

inline "cic:/CoRN/algebra/CSetoidFun/part_function_comp_dom_wd.con".

inline "cic:/CoRN/algebra/CSetoidFun/Fcomp.con".

(* UNEXPORTED
End Part_Function_Composition
*)

(* UNEXPORTED
End CSetoid_Ops
*)

(*#*
%\begin{convention}% Let [F:(BinPartFunct S1 S2)] and [G:(PartFunct S2 S3)], and denote by [Q] and [P], respectively, the predicates characterizing their domains.
%\end{convention}%
*)

(* UNEXPORTED
Section BinPart_Function_Composition
*)

alias id "S1" = "cic:/CoRN/algebra/CSetoidFun/BinPart_Function_Composition/S1.var".

alias id "S2" = "cic:/CoRN/algebra/CSetoidFun/BinPart_Function_Composition/S2.var".

alias id "S3" = "cic:/CoRN/algebra/CSetoidFun/BinPart_Function_Composition/S3.var".

alias id "G" = "cic:/CoRN/algebra/CSetoidFun/BinPart_Function_Composition/G.var".

alias id "F" = "cic:/CoRN/algebra/CSetoidFun/BinPart_Function_Composition/F.var".

(* begin hide *)

inline "cic:/CoRN/algebra/CSetoidFun/BinPart_Function_Composition/P.con" "BinPart_Function_Composition__".

inline "cic:/CoRN/algebra/CSetoidFun/BinPart_Function_Composition/Q.con" "BinPart_Function_Composition__".

(* end hide *)

inline "cic:/CoRN/algebra/CSetoidFun/BinPart_Function_Composition/R.con" "BinPart_Function_Composition__".

inline "cic:/CoRN/algebra/CSetoidFun/bin_part_function_comp_strext.con".

inline "cic:/CoRN/algebra/CSetoidFun/bin_part_function_comp_dom_wd.con".

inline "cic:/CoRN/algebra/CSetoidFun/BinFcomp.con".

(* UNEXPORTED
End BinPart_Function_Composition
*)

(* Different tokens for compatibility with coqdoc *)

(* UNEXPORTED
Implicit Arguments Fconst [S].
*)

(* NOTATION
Notation "[-C-] x" := (Fconst x) (at level 2, right associativity).
*)

(* NOTATION
Notation FId := (Fid _).
*)

(* UNEXPORTED
Implicit Arguments Fcomp [S].
*)

(* NOTATION
Infix "[o]" := Fcomp (at level 65, no associativity).
*)

(* UNEXPORTED
Hint Resolve pfwdef bpfwdef: algebra.
*)

(* UNEXPORTED
Section bijections
*)

(*#* **Bijections *)

inline "cic:/CoRN/algebra/CSetoidFun/injective.con".

inline "cic:/CoRN/algebra/CSetoidFun/injective_weak.con".

inline "cic:/CoRN/algebra/CSetoidFun/surjective.con".

(* UNEXPORTED
Implicit Arguments injective [A B].
*)

(* UNEXPORTED
Implicit Arguments injective_weak [A B].
*)

(* UNEXPORTED
Implicit Arguments surjective [A B].
*)

inline "cic:/CoRN/algebra/CSetoidFun/injective_imp_injective_weak.con".

inline "cic:/CoRN/algebra/CSetoidFun/bijective.con".

(* UNEXPORTED
Implicit Arguments bijective [A B].
*)

inline "cic:/CoRN/algebra/CSetoidFun/id_is_bij.con".

inline "cic:/CoRN/algebra/CSetoidFun/comp_resp_bij.con".

inline "cic:/CoRN/algebra/CSetoidFun/inv.con".

(* UNEXPORTED
Implicit Arguments inv [A B].
*)

inline "cic:/CoRN/algebra/CSetoidFun/invfun.con".

(* UNEXPORTED
Implicit Arguments invfun [A B].
*)

inline "cic:/CoRN/algebra/CSetoidFun/inv1.con".

inline "cic:/CoRN/algebra/CSetoidFun/inv2.con".

inline "cic:/CoRN/algebra/CSetoidFun/inv_strext.con".

inline "cic:/CoRN/algebra/CSetoidFun/Inv.con".

(* UNEXPORTED
Implicit Arguments Inv [A B].
*)

inline "cic:/CoRN/algebra/CSetoidFun/Inv_bij.con".

(* UNEXPORTED
End bijections
*)

(* UNEXPORTED
Implicit Arguments bijective [A B].
*)

(* UNEXPORTED
Implicit Arguments injective [A B].
*)

(* UNEXPORTED
Implicit Arguments injective_weak [A B].
*)

(* UNEXPORTED
Implicit Arguments surjective [A B].
*)

(* UNEXPORTED
Implicit Arguments inv [A B].
*)

(* UNEXPORTED
Implicit Arguments invfun [A B].
*)

(* UNEXPORTED
Implicit Arguments Inv [A B].
*)

(* UNEXPORTED
Implicit Arguments conj_wd [S P Q].
*)

(* NOTATION
Notation Prj1 := (prj1 _ _ _ _).
*)

(* NOTATION
Notation Prj2 := (prj2 _ _ _ _).
*)


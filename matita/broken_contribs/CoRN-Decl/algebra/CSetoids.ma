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

set "baseuri" "cic:/matita/CoRN-Decl/algebra/CSetoids".

include "CoRN.ma".

(* $Id.v,v 1.18 2002/11/25 14:43:42 lcf Exp $ *)

(*#* printing [=] %\ensuremath{\equiv}% #&equiv;# *)

(*#* printing [~=] %\ensuremath{\mathrel{\not\equiv}}% #&ne;# *)

(*#* printing [#] %\ensuremath{\mathrel\#}% *)

(*#* printing ex_unq %\ensuremath{\exists^1}% #&exist;<sup>1</sup># *)

(*#* printing [o] %\ensuremath\circ% #&sdot;# *)

(*#* printing [-C-] %\ensuremath\diamond% *)

(* Begin_SpecReals *)

(*#* *Setoids
Definition of a constructive setoid with apartness,
i.e.%\% a set with an equivalence relation and an apartness relation compatible with it.
*)

include "algebra/CLogic.ma".

include "tactics/Step.ma".

inline "cic:/CoRN/algebra/CSetoids/Relation.con".

(* End_SpecReals *)

(* UNEXPORTED
Implicit Arguments Treflexive [A].
*)

(* UNEXPORTED
Implicit Arguments Creflexive [A].
*)

(* Begin_SpecReals *)

(* UNEXPORTED
Implicit Arguments Tsymmetric [A].
*)

(* UNEXPORTED
Implicit Arguments Csymmetric [A].
*)

(* UNEXPORTED
Implicit Arguments Ttransitive [A].
*)

(* UNEXPORTED
Implicit Arguments Ctransitive [A].
*)

(* begin hide *)

(* UNEXPORTED
Set Implicit Arguments.
*)

(* UNEXPORTED
Unset Strict Implicit.
*)

(* end hide *)

(*#* **Relations necessary for Setoids
%\begin{convention}% Let [A:Type].
%\end{convention}%

Notice that their type depends on the main logical connective.
*)

(* UNEXPORTED
Section Properties_of_relations
*)

alias id "A" = "cic:/CoRN/algebra/CSetoids/Properties_of_relations/A.var".

inline "cic:/CoRN/algebra/CSetoids/irreflexive.con".

inline "cic:/CoRN/algebra/CSetoids/cotransitive.con".

inline "cic:/CoRN/algebra/CSetoids/tight_apart.con".

inline "cic:/CoRN/algebra/CSetoids/antisymmetric.con".

(* UNEXPORTED
End Properties_of_relations
*)

(* begin hide *)

(* UNEXPORTED
Set Strict Implicit.
*)

(* UNEXPORTED
Unset Implicit Arguments.
*)

(* end hide *)

(*#* **Definition of Setoid

Apartness, being the main relation, needs to be [CProp]-valued.  Equality,
as it is characterized by a negative statement, lives in [Prop]. *)

inline "cic:/CoRN/algebra/CSetoids/is_CSetoid.ind".

inline "cic:/CoRN/algebra/CSetoids/CSetoid.ind".

coercion cic:/matita/CoRN-Decl/algebra/CSetoids/cs_crr.con 0 (* compounds *).

(* UNEXPORTED
Implicit Arguments cs_eq [c].
*)

(* UNEXPORTED
Implicit Arguments cs_ap [c].
*)

(* NOTATION
Infix "[=]" := cs_eq (at level 70, no associativity).
*)

(* NOTATION
Infix "[#]" := cs_ap (at level 70, no associativity).
*)

(* End_SpecReals *)

inline "cic:/CoRN/algebra/CSetoids/cs_neq.con".

(* UNEXPORTED
Implicit Arguments cs_neq [S].
*)

(* NOTATION
Infix "[~=]" := cs_neq (at level 70, no associativity).
*)

(*#*
%\begin{nameconvention}%
In the names of lemmas, we refer to [ [=] ] by [eq], [ [~=] ] by
[neq], and [ [#] ] by [ap].
%\end{nameconvention}%

** Setoid axioms
We want concrete lemmas that state the axiomatic properties of a setoid.
%\begin{convention}%
Let [S] be a setoid.
%\end{convention}%
*)

(* Begin_SpecReals *)

(* UNEXPORTED
Section CSetoid_axioms
*)

alias id "S" = "cic:/CoRN/algebra/CSetoids/CSetoid_axioms/S.var".

inline "cic:/CoRN/algebra/CSetoids/CSetoid_is_CSetoid.con".

inline "cic:/CoRN/algebra/CSetoids/ap_irreflexive.con".

inline "cic:/CoRN/algebra/CSetoids/ap_symmetric.con".

inline "cic:/CoRN/algebra/CSetoids/ap_cotransitive.con".

inline "cic:/CoRN/algebra/CSetoids/ap_tight.con".

(* UNEXPORTED
End CSetoid_axioms
*)

(* End_SpecReals *)

(*#* **Setoid basics%\label{section:setoid-basics}%
%\begin{convention}% Let [S] be a setoid.
%\end{convention}%
*)

(* Begin_SpecReals *)

(* UNEXPORTED
Section CSetoid_basics
*)

alias id "S" = "cic:/CoRN/algebra/CSetoids/CSetoid_basics/S.var".

(* End_SpecReals *)

(*#*
In `there exists a unique [a:S] such that %\ldots%#...#', we now mean unique with respect to the setoid equality. We use [ex_unq] to denote unique existence.
*)

inline "cic:/CoRN/algebra/CSetoids/ex_unq.con".

inline "cic:/CoRN/algebra/CSetoids/eq_reflexive.con".

inline "cic:/CoRN/algebra/CSetoids/eq_symmetric.con".

inline "cic:/CoRN/algebra/CSetoids/eq_transitive.con".

(*#*
%\begin{shortcoming}%
The lemma [eq_reflexive] above is convertible to
[eq_reflexive_unfolded] below. We need the second version too,
because the first cannot be applied when an instance of reflexivity is needed.
(``I have complained bitterly about this.'' RP)
%\end{shortcoming}%

%\begin{nameconvention}%
If lemma [a] is just an unfolding of lemma [b], the name of [a] is the name
[b] with the suffix ``[_unfolded]''.
%\end{nameconvention}%
*)

inline "cic:/CoRN/algebra/CSetoids/eq_reflexive_unfolded.con".

inline "cic:/CoRN/algebra/CSetoids/eq_symmetric_unfolded.con".

inline "cic:/CoRN/algebra/CSetoids/eq_transitive_unfolded.con".

inline "cic:/CoRN/algebra/CSetoids/eq_wdl.con".

(* Begin_SpecReals *)

inline "cic:/CoRN/algebra/CSetoids/ap_irreflexive_unfolded.con".

(* End_SpecReals *)

inline "cic:/CoRN/algebra/CSetoids/ap_cotransitive_unfolded.con".

inline "cic:/CoRN/algebra/CSetoids/ap_symmetric_unfolded.con".

(*#*
%\begin{shortcoming}%
We would like to write
[[
Lemma eq_equiv_not_ap : forall (x y:S), x [=] y Iff ~(x [#] y).
]]
In Coq, however, this lemma cannot be easily applied.
Therefore we have to split the lemma into the following two lemmas [eq_imp_not_ap] and [not_ap_imp_eq].
%\end{shortcoming}%
*)

inline "cic:/CoRN/algebra/CSetoids/eq_imp_not_ap.con".

inline "cic:/CoRN/algebra/CSetoids/not_ap_imp_eq.con".

inline "cic:/CoRN/algebra/CSetoids/neq_imp_notnot_ap.con".

inline "cic:/CoRN/algebra/CSetoids/notnot_ap_imp_neq.con".

inline "cic:/CoRN/algebra/CSetoids/ap_imp_neq.con".

inline "cic:/CoRN/algebra/CSetoids/not_neq_imp_eq.con".

inline "cic:/CoRN/algebra/CSetoids/eq_imp_not_neq.con".

(* Begin_SpecReals *)

(* UNEXPORTED
End CSetoid_basics
*)

(* End_SpecReals *)

(* UNEXPORTED
Section product_csetoid
*)

(*#* **The product of setoids *)

inline "cic:/CoRN/algebra/CSetoids/prod_ap.con".

inline "cic:/CoRN/algebra/CSetoids/prod_eq.con".

inline "cic:/CoRN/algebra/CSetoids/prodcsetoid_is_CSetoid.con".

inline "cic:/CoRN/algebra/CSetoids/ProdCSetoid.con".

(* UNEXPORTED
End product_csetoid
*)

(* UNEXPORTED
Implicit Arguments ex_unq [S].
*)

(* UNEXPORTED
Hint Resolve eq_reflexive_unfolded: algebra_r.
*)

(* UNEXPORTED
Hint Resolve eq_symmetric_unfolded: algebra_s.
*)

(* UNEXPORTED
Declare Left Step eq_wdl.
*)

(* UNEXPORTED
Declare Right Step eq_transitive_unfolded.
*)

(* Begin_SpecReals *)

(*#* **Relations and predicates
Here we define the notions of well-definedness and strong extensionality
on predicates and relations.

%\begin{convention}% Let [S] be a setoid.
%\end{convention}%

%\begin{nameconvention}%
- ``well-defined'' is abbreviated to [well_def] (or [wd]).
- ``strongly extensional'' is abbreviated to [strong_ext] (or [strext]).

%\end{nameconvention}%
*)

(* UNEXPORTED
Section CSetoid_relations_and_predicates
*)

alias id "S" = "cic:/CoRN/algebra/CSetoids/CSetoid_relations_and_predicates/S.var".

(* End_SpecReals *)

(*#* ***Predicates

At this stage, we consider [CProp]- and [Prop]-valued predicates on setoids.

%\begin{convention}% Let [P] be a predicate on (the carrier of) [S].
%\end{convention}%
*)

(* UNEXPORTED
Section CSetoidPredicates
*)

alias id "P" = "cic:/CoRN/algebra/CSetoids/CSetoid_relations_and_predicates/CSetoidPredicates/P.var".

inline "cic:/CoRN/algebra/CSetoids/pred_strong_ext.con".

inline "cic:/CoRN/algebra/CSetoids/pred_wd.con".

(* UNEXPORTED
End CSetoidPredicates
*)

inline "cic:/CoRN/algebra/CSetoids/CSetoid_predicate.ind".

coercion cic:/matita/CoRN-Decl/algebra/CSetoids/csp_pred.con 0 (* compounds *).

inline "cic:/CoRN/algebra/CSetoids/csp_wd.con".

(*#* Similar, with [Prop] instead of [CProp]. *)

(* UNEXPORTED
Section CSetoidPPredicates
*)

alias id "P" = "cic:/CoRN/algebra/CSetoids/CSetoid_relations_and_predicates/CSetoidPPredicates/P.var".

inline "cic:/CoRN/algebra/CSetoids/pred_strong_ext'.con".

inline "cic:/CoRN/algebra/CSetoids/pred_wd'.con".

(* UNEXPORTED
End CSetoidPPredicates
*)

(*#* ***Definition of a setoid predicate *)

inline "cic:/CoRN/algebra/CSetoids/CSetoid_predicate'.ind".

coercion cic:/matita/CoRN-Decl/algebra/CSetoids/csp'_pred.con 0 (* compounds *).

inline "cic:/CoRN/algebra/CSetoids/csp'_wd.con".

(* Begin_SpecReals *)

(*#* ***Relations
%\begin{convention}%
Let [R] be a relation on (the carrier of) [S].
%\end{convention}% *)

(* UNEXPORTED
Section CsetoidRelations
*)

alias id "R" = "cic:/CoRN/algebra/CSetoids/CSetoid_relations_and_predicates/CsetoidRelations/R.var".

inline "cic:/CoRN/algebra/CSetoids/rel_wdr.con".

inline "cic:/CoRN/algebra/CSetoids/rel_wdl.con".

inline "cic:/CoRN/algebra/CSetoids/rel_strext.con".

(* End_SpecReals *)

inline "cic:/CoRN/algebra/CSetoids/rel_strext_lft.con".

inline "cic:/CoRN/algebra/CSetoids/rel_strext_rht.con".

inline "cic:/CoRN/algebra/CSetoids/rel_strext_imp_lftarg.con".

inline "cic:/CoRN/algebra/CSetoids/rel_strext_imp_rhtarg.con".

inline "cic:/CoRN/algebra/CSetoids/rel_strextarg_imp_strext.con".

(* Begin_SpecReals *)

(* UNEXPORTED
End CsetoidRelations
*)

(*#* ***Definition of a setoid relation
The type of relations over a setoid.  *)

inline "cic:/CoRN/algebra/CSetoids/CSetoid_relation.ind".

coercion cic:/matita/CoRN-Decl/algebra/CSetoids/csr_rel.con 0 (* compounds *).

(*#* ***[CProp] Relations
%\begin{convention}%
Let [R] be a relation on (the carrier of) [S].
%\end{convention}%
*)

(* UNEXPORTED
Section CCsetoidRelations
*)

alias id "R" = "cic:/CoRN/algebra/CSetoids/CSetoid_relations_and_predicates/CCsetoidRelations/R.var".

inline "cic:/CoRN/algebra/CSetoids/Crel_wdr.con".

inline "cic:/CoRN/algebra/CSetoids/Crel_wdl.con".

inline "cic:/CoRN/algebra/CSetoids/Crel_strext.con".

(* End_SpecReals *)

inline "cic:/CoRN/algebra/CSetoids/Crel_strext_lft.con".

inline "cic:/CoRN/algebra/CSetoids/Crel_strext_rht.con".

inline "cic:/CoRN/algebra/CSetoids/Crel_strext_imp_lftarg.con".

inline "cic:/CoRN/algebra/CSetoids/Crel_strext_imp_rhtarg.con".

inline "cic:/CoRN/algebra/CSetoids/Crel_strextarg_imp_strext.con".

(* Begin_SpecReals *)

(* UNEXPORTED
End CCsetoidRelations
*)

(*#* ***Definition of a [CProp] setoid relation

The type of relations over a setoid.  *)

inline "cic:/CoRN/algebra/CSetoids/CCSetoid_relation.ind".

coercion cic:/matita/CoRN-Decl/algebra/CSetoids/Ccsr_rel.con 0 (* compounds *).

inline "cic:/CoRN/algebra/CSetoids/Ccsr_wdr.con".

inline "cic:/CoRN/algebra/CSetoids/Ccsr_wdl.con".

(* End_SpecReals *)

inline "cic:/CoRN/algebra/CSetoids/ap_wdr.con".

inline "cic:/CoRN/algebra/CSetoids/ap_wdl.con".

inline "cic:/CoRN/algebra/CSetoids/ap_wdr_unfolded.con".

inline "cic:/CoRN/algebra/CSetoids/ap_wdl_unfolded.con".

inline "cic:/CoRN/algebra/CSetoids/ap_strext.con".

inline "cic:/CoRN/algebra/CSetoids/predS_well_def.con".

(* Begin_SpecReals *)

(* UNEXPORTED
End CSetoid_relations_and_predicates
*)

(* UNEXPORTED
Declare Left Step ap_wdl_unfolded.
*)

(* UNEXPORTED
Declare Right Step ap_wdr_unfolded.
*)

(* End_SpecReals *)

(*#* **Functions between setoids
Such functions must preserve the setoid equality
and be strongly extensional w.r.t.%\% the apartness, i.e.%\%
if [f(x,y) [#] f(x1,y1)], then  [x [#] x1 + y [#] y1].
For every arity this has to be defined separately.
%\begin{convention}%
Let [S1], [S2] and [S3] be setoids.
%\end{convention}%

First we consider unary functions.  *)

(* Begin_SpecReals *)

(* UNEXPORTED
Section CSetoid_functions
*)

alias id "S1" = "cic:/CoRN/algebra/CSetoids/CSetoid_functions/S1.var".

alias id "S2" = "cic:/CoRN/algebra/CSetoids/CSetoid_functions/S2.var".

alias id "S3" = "cic:/CoRN/algebra/CSetoids/CSetoid_functions/S3.var".

(* UNEXPORTED
Section unary_functions
*)

(*#*
In the following two definitions,
[f] is a function from (the carrier of) [S1] to
(the carrier of) [S2].  *)

alias id "f" = "cic:/CoRN/algebra/CSetoids/CSetoid_functions/unary_functions/f.var".

inline "cic:/CoRN/algebra/CSetoids/fun_wd.con".

inline "cic:/CoRN/algebra/CSetoids/fun_strext.con".

(* End_SpecReals *)

inline "cic:/CoRN/algebra/CSetoids/fun_strext_imp_wd.con".

(* Begin_SpecReals *)

(* UNEXPORTED
End unary_functions
*)

inline "cic:/CoRN/algebra/CSetoids/CSetoid_fun.ind".

coercion cic:/matita/CoRN-Decl/algebra/CSetoids/csf_fun.con 0 (* compounds *).

inline "cic:/CoRN/algebra/CSetoids/csf_wd.con".

(* End_SpecReals *)

inline "cic:/CoRN/algebra/CSetoids/Const_CSetoid_fun.con".

(* Begin_SpecReals *)

(* UNEXPORTED
Section binary_functions
*)

(*#*
Now we consider binary functions.
In the following two definitions,
[f] is a function from [S1] and [S2] to [S3].
*)

alias id "f" = "cic:/CoRN/algebra/CSetoids/CSetoid_functions/binary_functions/f.var".

inline "cic:/CoRN/algebra/CSetoids/bin_fun_wd.con".

inline "cic:/CoRN/algebra/CSetoids/bin_fun_strext.con".

(* End_SpecReals *)

inline "cic:/CoRN/algebra/CSetoids/bin_fun_strext_imp_wd.con".

(* Begin_SpecReals *)

(* UNEXPORTED
End binary_functions
*)

inline "cic:/CoRN/algebra/CSetoids/CSetoid_bin_fun.ind".

coercion cic:/matita/CoRN-Decl/algebra/CSetoids/csbf_fun.con 0 (* compounds *).

inline "cic:/CoRN/algebra/CSetoids/csbf_wd.con".

inline "cic:/CoRN/algebra/CSetoids/csf_wd_unfolded.con".

inline "cic:/CoRN/algebra/CSetoids/csf_strext_unfolded.con".

inline "cic:/CoRN/algebra/CSetoids/csbf_wd_unfolded.con".

(* UNEXPORTED
End CSetoid_functions
*)

(* End_SpecReals *)

(* UNEXPORTED
Hint Resolve csf_wd_unfolded csbf_wd_unfolded: algebra_c.
*)

(* UNEXPORTED
Implicit Arguments fun_wd [S1 S2].
*)

(* UNEXPORTED
Implicit Arguments fun_strext [S1 S2].
*)

(* Begin_SpecReals *)

(*#* **The unary and binary (inner) operations on a csetoid
An operation is a function with domain(s) and co-domain equal.

%\begin{nameconvention}%
The word ``unary operation'' is abbreviated to [un_op];
``binary operation'' is abbreviated to [bin_op].
%\end{nameconvention}%

%\begin{convention}%
Let [S] be a setoid.
%\end{convention}%
*)

(* UNEXPORTED
Section csetoid_inner_ops
*)

alias id "S" = "cic:/CoRN/algebra/CSetoids/csetoid_inner_ops/S.var".

(*#* Properties of binary operations *)

inline "cic:/CoRN/algebra/CSetoids/commutes.con".

inline "cic:/CoRN/algebra/CSetoids/associative.con".

(*#* Well-defined unary operations on a setoid.  *)

inline "cic:/CoRN/algebra/CSetoids/un_op_wd.con".

inline "cic:/CoRN/algebra/CSetoids/un_op_strext.con".

inline "cic:/CoRN/algebra/CSetoids/CSetoid_un_op.con".

inline "cic:/CoRN/algebra/CSetoids/Build_CSetoid_un_op.con".

(* End_SpecReals *)

inline "cic:/CoRN/algebra/CSetoids/id_strext.con".

inline "cic:/CoRN/algebra/CSetoids/id_pres_eq.con".

inline "cic:/CoRN/algebra/CSetoids/id_un_op.con".

(* begin hide *)

coercion cic:/matita/CoRN-Decl/algebra/CSetoids/un_op_fun.con 0 (* compounds *).

(* end hide *)

(* Begin_SpecReals *)

inline "cic:/CoRN/algebra/CSetoids/cs_un_op_strext.con".

(* End_SpecReals *)

inline "cic:/CoRN/algebra/CSetoids/un_op_wd_unfolded.con".

inline "cic:/CoRN/algebra/CSetoids/un_op_strext_unfolded.con".

(*#* Well-defined binary operations on a setoid.  *)

inline "cic:/CoRN/algebra/CSetoids/bin_op_wd.con".

inline "cic:/CoRN/algebra/CSetoids/bin_op_strext.con".

(* Begin_SpecReals *)

inline "cic:/CoRN/algebra/CSetoids/CSetoid_bin_op.con".

inline "cic:/CoRN/algebra/CSetoids/Build_CSetoid_bin_op.con".

(* End_SpecReals *)

inline "cic:/CoRN/algebra/CSetoids/cs_bin_op_wd.con".

inline "cic:/CoRN/algebra/CSetoids/cs_bin_op_strext.con".

(* Begin_SpecReals *)

(* begin hide *)

coercion cic:/matita/CoRN-Decl/algebra/CSetoids/bin_op_bin_fun.con 0 (* compounds *).

(* end hide *)

(* End_SpecReals *)

inline "cic:/CoRN/algebra/CSetoids/bin_op_wd_unfolded.con".

inline "cic:/CoRN/algebra/CSetoids/bin_op_strext_unfolded.con".

inline "cic:/CoRN/algebra/CSetoids/bin_op_is_wd_un_op_lft.con".

inline "cic:/CoRN/algebra/CSetoids/bin_op_is_wd_un_op_rht.con".

inline "cic:/CoRN/algebra/CSetoids/bin_op_is_strext_un_op_lft.con".

inline "cic:/CoRN/algebra/CSetoids/bin_op_is_strext_un_op_rht.con".

inline "cic:/CoRN/algebra/CSetoids/bin_op2un_op_rht.con".

inline "cic:/CoRN/algebra/CSetoids/bin_op2un_op_lft.con".

(* Begin_SpecReals *)

(* UNEXPORTED
End csetoid_inner_ops
*)

(* End_SpecReals *)

(* UNEXPORTED
Implicit Arguments commutes [S].
*)

(* Begin_SpecReals *)

(* UNEXPORTED
Implicit Arguments associative [S].
*)

(* End_SpecReals *)

(* UNEXPORTED
Hint Resolve bin_op_wd_unfolded un_op_wd_unfolded: algebra_c.
*)

(*#* **The binary outer operations on a csetoid
%\begin{convention}%
Let [S1] and [S2] be setoids.
%\end{convention}%
*)

(* UNEXPORTED
Section csetoid_outer_ops
*)

alias id "S1" = "cic:/CoRN/algebra/CSetoids/csetoid_outer_ops/S1.var".

alias id "S2" = "cic:/CoRN/algebra/CSetoids/csetoid_outer_ops/S2.var".

(*#*
Well-defined outer operations on a setoid.
*)

inline "cic:/CoRN/algebra/CSetoids/outer_op_well_def.con".

inline "cic:/CoRN/algebra/CSetoids/outer_op_strext.con".

inline "cic:/CoRN/algebra/CSetoids/CSetoid_outer_op.con".

inline "cic:/CoRN/algebra/CSetoids/Build_CSetoid_outer_op.con".

inline "cic:/CoRN/algebra/CSetoids/csoo_wd.con".

inline "cic:/CoRN/algebra/CSetoids/csoo_strext.con".

(* begin hide *)

coercion cic:/matita/CoRN-Decl/algebra/CSetoids/outer_op_bin_fun.con 0 (* compounds *).

(* end hide *)

inline "cic:/CoRN/algebra/CSetoids/csoo_wd_unfolded.con".

(* UNEXPORTED
End csetoid_outer_ops
*)

(* UNEXPORTED
Hint Resolve csoo_wd_unfolded: algebra_c.
*)

(* Begin_SpecReals *)

(*#* **Subsetoids
%\begin{convention}%
Let [S] be a setoid, and [P] a predicate on the carrier of [S].
%\end{convention}%
*)

(* UNEXPORTED
Section SubCSetoids
*)

alias id "S" = "cic:/CoRN/algebra/CSetoids/SubCSetoids/S.var".

alias id "P" = "cic:/CoRN/algebra/CSetoids/SubCSetoids/P.var".

inline "cic:/CoRN/algebra/CSetoids/subcsetoid_crr.ind".

coercion cic:/matita/CoRN-Decl/algebra/CSetoids/scs_elem.con 0 (* compounds *).

(*#* Though [scs_elem] is declared as a coercion, it does not satisfy the
uniform inheritance condition and will not be inserted.  However it will
also not be printed, which is handy.
*)

inline "cic:/CoRN/algebra/CSetoids/restrict_relation.con".

inline "cic:/CoRN/algebra/CSetoids/Crestrict_relation.con".

inline "cic:/CoRN/algebra/CSetoids/subcsetoid_eq.con".

inline "cic:/CoRN/algebra/CSetoids/subcsetoid_ap.con".

(* End_SpecReals *)

inline "cic:/CoRN/algebra/CSetoids/subcsetoid_equiv.con".

(* Begin_SpecReals *)

inline "cic:/CoRN/algebra/CSetoids/subcsetoid_is_CSetoid.con".

inline "cic:/CoRN/algebra/CSetoids/Build_SubCSetoid.con".

(* End_SpecReals *)

(*#* ***Subsetoid unary operations
%\begin{convention}%
Let [f] be a unary setoid operation on [S].
%\end{convention}%
*)

(* UNEXPORTED
Section SubCSetoid_unary_operations
*)

alias id "f" = "cic:/CoRN/algebra/CSetoids/SubCSetoids/SubCSetoid_unary_operations/f.var".

inline "cic:/CoRN/algebra/CSetoids/un_op_pres_pred.con".

(*#*
%\begin{convention}%
Assume [pr:un_op_pres_pred].
%\end{convention}% *)

alias id "pr" = "cic:/CoRN/algebra/CSetoids/SubCSetoids/SubCSetoid_unary_operations/pr.var".

inline "cic:/CoRN/algebra/CSetoids/restr_un_op.con".

inline "cic:/CoRN/algebra/CSetoids/restr_un_op_wd.con".

inline "cic:/CoRN/algebra/CSetoids/restr_un_op_strext.con".

inline "cic:/CoRN/algebra/CSetoids/Build_SubCSetoid_un_op.con".

(* UNEXPORTED
End SubCSetoid_unary_operations
*)

(*#* ***Subsetoid binary operations
%\begin{convention}%
Let [f] be a binary setoid operation on [S].
%\end{convention}%
*)

(* UNEXPORTED
Section SubCSetoid_binary_operations
*)

alias id "f" = "cic:/CoRN/algebra/CSetoids/SubCSetoids/SubCSetoid_binary_operations/f.var".

inline "cic:/CoRN/algebra/CSetoids/bin_op_pres_pred.con".

(*#*
%\begin{convention}%
Assume [bin_op_pres_pred].
%\end{convention}%
*)

alias id "pr" = "cic:/CoRN/algebra/CSetoids/SubCSetoids/SubCSetoid_binary_operations/pr.var".

inline "cic:/CoRN/algebra/CSetoids/restr_bin_op.con".

inline "cic:/CoRN/algebra/CSetoids/restr_bin_op_well_def.con".

inline "cic:/CoRN/algebra/CSetoids/restr_bin_op_strext.con".

inline "cic:/CoRN/algebra/CSetoids/Build_SubCSetoid_bin_op.con".

inline "cic:/CoRN/algebra/CSetoids/restr_f_assoc.con".

(* UNEXPORTED
End SubCSetoid_binary_operations
*)

(* Begin_SpecReals *)

(* UNEXPORTED
End SubCSetoids
*)

(* End_SpecReals *)

(* begin hide *)

(* UNEXPORTED
Ltac Step_final x := apply eq_transitive_unfolded with x; Algebra.
*)

(* end hide *)

(* UNEXPORTED
Tactic Notation "Step_final" constr(c) :=  Step_final c.
*)

(*#* **Miscellaneous
*)

inline "cic:/CoRN/algebra/CSetoids/proper_caseZ_diff_CS.con".

(*#*
Finally, we characterize functions defined on the natural numbers also as setoid functions, similarly to what we already did for predicates.
*)

inline "cic:/CoRN/algebra/CSetoids/nat_less_n_fun.con".

inline "cic:/CoRN/algebra/CSetoids/nat_less_n_fun'.con".

(* UNEXPORTED
Implicit Arguments nat_less_n_fun [S n].
*)

(* UNEXPORTED
Implicit Arguments nat_less_n_fun' [S n].
*)


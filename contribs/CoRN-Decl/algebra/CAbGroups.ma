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

set "baseuri" "cic:/matita/CoRN-Decl/algebra/CAbGroups".

include "CoRN.ma".

include "algebra/CGroups.ma".

(* UNEXPORTED
Section Abelian_Groups
*)

(*#*
* Abelian Groups
Now we introduce commutativity and add some results.
*)

inline "cic:/CoRN/algebra/CAbGroups/is_CAbGroup.con".

inline "cic:/CoRN/algebra/CAbGroups/CAbGroup.ind".

coercion cic:/matita/CoRN-Decl/algebra/CAbGroups/cag_crr.con 0 (* compounds *).

(* UNEXPORTED
Section AbGroup_Axioms
*)

alias id "G" = "cic:/CoRN/algebra/CAbGroups/Abelian_Groups/AbGroup_Axioms/G.var".

(*#*
%\begin{convention}% Let [G] be an Abelian Group.
%\end{convention}%
*)

inline "cic:/CoRN/algebra/CAbGroups/CAbGroup_is_CAbGroup.con".

inline "cic:/CoRN/algebra/CAbGroups/cag_commutes.con".

inline "cic:/CoRN/algebra/CAbGroups/cag_commutes_unfolded.con".

(* UNEXPORTED
End AbGroup_Axioms
*)

(* UNEXPORTED
Section SubCAbGroups
*)

(*#*
** Subgroups of an Abelian Group
*)

alias id "G" = "cic:/CoRN/algebra/CAbGroups/Abelian_Groups/SubCAbGroups/G.var".

alias id "P" = "cic:/CoRN/algebra/CAbGroups/Abelian_Groups/SubCAbGroups/P.var".

alias id "Punit" = "cic:/CoRN/algebra/CAbGroups/Abelian_Groups/SubCAbGroups/Punit.var".

alias id "op_pres_P" = "cic:/CoRN/algebra/CAbGroups/Abelian_Groups/SubCAbGroups/op_pres_P.var".

alias id "inv_pres_P" = "cic:/CoRN/algebra/CAbGroups/Abelian_Groups/SubCAbGroups/inv_pres_P.var".

(*#*
%\begin{convention}%
Let [G] be an Abelian Group and [P] be a ([CProp]-valued) predicate on [G]
that contains [Zero] and is closed under [[+]] and [[--]].
%\end{convention}%
*)

inline "cic:/CoRN/algebra/CAbGroups/Abelian_Groups/SubCAbGroups/subcrr.con" "Abelian_Groups__SubCAbGroups__".

inline "cic:/CoRN/algebra/CAbGroups/isabgrp_scrr.con".

inline "cic:/CoRN/algebra/CAbGroups/Build_SubCAbGroup.con".

(* UNEXPORTED
End SubCAbGroups
*)

(* UNEXPORTED
Section Various
*)

(*#*
** Basic properties of Abelian groups
*)

(* UNEXPORTED
Hint Resolve cag_commutes_unfolded: algebra.
*)

alias id "G" = "cic:/CoRN/algebra/CAbGroups/Abelian_Groups/Various/G.var".

(*#*
%\begin{convention}% Let [G] be an Abelian Group.
%\end{convention}%
*)

inline "cic:/CoRN/algebra/CAbGroups/cag_op_inv.con".

(* UNEXPORTED
Hint Resolve cag_op_inv: algebra.
*)

inline "cic:/CoRN/algebra/CAbGroups/assoc_1.con".

inline "cic:/CoRN/algebra/CAbGroups/minus_plus.con".

inline "cic:/CoRN/algebra/CAbGroups/op_lft_resp_ap.con".

inline "cic:/CoRN/algebra/CAbGroups/cag_ap_cancel_lft.con".

inline "cic:/CoRN/algebra/CAbGroups/plus_cancel_ap_lft.con".

(* UNEXPORTED
End Various
*)

(* UNEXPORTED
End Abelian_Groups
*)

(* UNEXPORTED
Hint Resolve cag_commutes_unfolded: algebra.
*)

(* UNEXPORTED
Hint Resolve cag_op_inv assoc_1 zero_minus minus_plus op_lft_resp_ap: algebra.
*)

(* UNEXPORTED
Section Nice_Char
*)

(*#*
** Building an abelian group

In order to actually define concrete abelian groups,
it is not in general practical to construct first a semigroup,
then a monoid, then a group and finally an abelian group.  The
presence of commutativity, for example, makes many of the monoid
proofs trivial.  In this section, we provide a constructor that
will allow us to go directly from a setoid to an abelian group.

We start from a setoid S with an element [unit], a
commutative and associative binary operation [plus] which
is strongly extensional in its first argument and admits [unit]
as a left unit, and a unary setoid
function [inv] which inverts elements respective to [plus].
*)

alias id "S" = "cic:/CoRN/algebra/CAbGroups/Nice_Char/S.var".

alias id "unit" = "cic:/CoRN/algebra/CAbGroups/Nice_Char/unit.var".

alias id "plus" = "cic:/CoRN/algebra/CAbGroups/Nice_Char/plus.var".

(*#*
%\begin{convention}%
Let [S] be a Setoid and [unit:S], [plus:S->S->S] and [inv] a unary
setoid operation on [S].
Assume that [plus] is commutative, associative and `left-strongly-extensional
([(plus x z) [#] (plus y z) -> x [#] y]), that [unit] is a left-unit
for [plus] and [(inv x)] is a right-inverse of [x] w.r.t.%\% [plus].
%\end{convention}%
*)

alias id "plus_lext" = "cic:/CoRN/algebra/CAbGroups/Nice_Char/plus_lext.var".

alias id "plus_lunit" = "cic:/CoRN/algebra/CAbGroups/Nice_Char/plus_lunit.var".

alias id "plus_comm" = "cic:/CoRN/algebra/CAbGroups/Nice_Char/plus_comm.var".

alias id "plus_assoc" = "cic:/CoRN/algebra/CAbGroups/Nice_Char/plus_assoc.var".

alias id "inv" = "cic:/CoRN/algebra/CAbGroups/Nice_Char/inv.var".

alias id "inv_inv" = "cic:/CoRN/algebra/CAbGroups/Nice_Char/inv_inv.var".

inline "cic:/CoRN/algebra/CAbGroups/plus_rext.con".

inline "cic:/CoRN/algebra/CAbGroups/plus_runit.con".

inline "cic:/CoRN/algebra/CAbGroups/plus_is_fun.con".

inline "cic:/CoRN/algebra/CAbGroups/inv_inv'.con".

inline "cic:/CoRN/algebra/CAbGroups/plus_fun.con".

inline "cic:/CoRN/algebra/CAbGroups/Build_CSemiGroup'.con".

inline "cic:/CoRN/algebra/CAbGroups/Build_CMonoid'.con".

inline "cic:/CoRN/algebra/CAbGroups/Build_CGroup'.con".

inline "cic:/CoRN/algebra/CAbGroups/Build_CAbGroup'.con".

(* UNEXPORTED
End Nice_Char
*)

(*#* ** Iteration

For reflection the following is needed; hopefully it is also useful.
*)

(* UNEXPORTED
Section Group_Extras
*)

alias id "G" = "cic:/CoRN/algebra/CAbGroups/Group_Extras/G.var".

inline "cic:/CoRN/algebra/CAbGroups/nmult.con".

inline "cic:/CoRN/algebra/CAbGroups/nmult_wd.con".

inline "cic:/CoRN/algebra/CAbGroups/nmult_one.con".

inline "cic:/CoRN/algebra/CAbGroups/nmult_Zero.con".

inline "cic:/CoRN/algebra/CAbGroups/nmult_plus.con".

inline "cic:/CoRN/algebra/CAbGroups/nmult_mult.con".

inline "cic:/CoRN/algebra/CAbGroups/nmult_inv.con".

inline "cic:/CoRN/algebra/CAbGroups/nmult_plus'.con".

(* UNEXPORTED
Hint Resolve nmult_wd nmult_Zero nmult_inv nmult_plus nmult_plus': algebra.
*)

inline "cic:/CoRN/algebra/CAbGroups/zmult.con".

(*
Lemma Zeq_imp_nat_eq : forall m n:nat, m = n -> m = n.
auto.
intro m; induction m.
intro n; induction n; auto.

intro; induction n.
intro. inversion H.
intros.
rewrite (IHm n).
auto.
repeat rewrite inj_S in H.
auto with zarith.
Qed.
*)

inline "cic:/CoRN/algebra/CAbGroups/zmult_char.con".

inline "cic:/CoRN/algebra/CAbGroups/zmult_wd.con".

inline "cic:/CoRN/algebra/CAbGroups/zmult_one.con".

inline "cic:/CoRN/algebra/CAbGroups/zmult_min_one.con".

inline "cic:/CoRN/algebra/CAbGroups/zmult_zero.con".

inline "cic:/CoRN/algebra/CAbGroups/zmult_Zero.con".

(* UNEXPORTED
Hint Resolve zmult_zero: algebra.
*)

inline "cic:/CoRN/algebra/CAbGroups/zmult_plus.con".

inline "cic:/CoRN/algebra/CAbGroups/zmult_mult.con".

inline "cic:/CoRN/algebra/CAbGroups/zmult_plus'.con".

(* UNEXPORTED
End Group_Extras
*)

(* UNEXPORTED
Hint Resolve nmult_wd nmult_one nmult_Zero nmult_plus nmult_inv nmult_mult
  nmult_plus' zmult_wd zmult_one zmult_min_one zmult_zero zmult_Zero
  zmult_plus zmult_mult zmult_plus': algebra.
*)

(* UNEXPORTED
Implicit Arguments nmult [G].
*)

(* UNEXPORTED
Implicit Arguments zmult [G].
*)


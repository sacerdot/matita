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

set "baseuri" "cic:/matita/CoRN-Decl/algebra/CLogic".

include "CoRN.ma".

(* $Id: CLogic.v,v 1.10 2004/04/09 15:58:31 lcf Exp $ *)

(*#* printing Not %\ensuremath\neg% #~# *)

(*#* printing CNot %\ensuremath\neg% #~# *)

(*#* printing Iff %\ensuremath\Leftrightarrow% #&hArr;# *)

(*#* printing CFalse %\ensuremath\bot% #&perp;# *)

(*#* printing False %\ensuremath\bot% #&perp;# *)

(*#* printing CTrue %\ensuremath\top% *)

(*#* printing True %\ensuremath\top% *)

(*#* printing or %\ensuremath{\mathrel\vee}% *)

(*#* printing and %\ensuremath{\mathrel\wedge}% *)

include "algebra/Basics.ma".

(*#* *Extending the Coq Logic
Because notions of apartness and order have computational meaning, we
will have to define logical connectives in [Type].  In order to
keep a syntactic distinction between types of terms, we define [CProp]
as an alias for [Type], to be used as type of (computationally meaningful)
propositions.

Falsehood and negation will typically not be needed in [CProp], as
they are used to refer to negative statements, which carry no
computational meaning.  Therefore, we will simply define a negation
operator from [Type] to [Prop] .

Conjunction, disjunction and existential quantification will have to come in
multiple varieties.  For conjunction, we will need four operators of type
[s1->s2->s3], where [s3] is [Prop] if both [s1] and [s2]
are [Prop] and [CProp] otherwise.
We here take advantage of the inclusion of [Prop] in [Type].

Disjunction is slightly different, as it will always return a value in [CProp] even
if both arguments are propositions.  This is because in general
it may be computationally important to know which of the two branches of the
disjunction actually holds.

Existential quantification will similarly always return a value in [CProp].

- [CProp]-valued conjuction will be denoted as [and];
- [Crop]-valued conjuction will be denoted as [or];
- Existential quantification will be written as [{x:A & B}] or [{x:A | B}],
according to whether [B] is respectively of type [CProp] or [Prop].

In a few specific situations we do need truth, false and negation in [CProp],
so we will also introduce them; this should be a temporary option.

Finally, for other formulae that might occur in our [CProp]-valued
propositions, such as [(le m n)], we have to introduce a [CProp]-valued
version.
*)

inline "cic:/CoRN/algebra/CLogic/CProp.con".

(* UNEXPORTED
Section Basics
*)

(*#* ** Basics
Here we treat conversion from [Prop] to [CProp] and vice versa,
and some basic connectives in [CProp].
*)

inline "cic:/CoRN/algebra/CLogic/Not.con".

inline "cic:/CoRN/algebra/CLogic/CAnd.ind".

inline "cic:/CoRN/algebra/CLogic/Iff.con".

inline "cic:/CoRN/algebra/CLogic/CFalse.ind".

inline "cic:/CoRN/algebra/CLogic/CTrue.ind".

inline "cic:/CoRN/algebra/CLogic/proj1_sigT.con".

inline "cic:/CoRN/algebra/CLogic/proj2_sigT.con".

inline "cic:/CoRN/algebra/CLogic/sig2T.ind".

inline "cic:/CoRN/algebra/CLogic/proj1_sig2T.con".

inline "cic:/CoRN/algebra/CLogic/proj2a_sig2T.con".

inline "cic:/CoRN/algebra/CLogic/proj2b_sig2T.con".

inline "cic:/CoRN/algebra/CLogic/toCProp.ind".

inline "cic:/CoRN/algebra/CLogic/toCProp_e.con".

inline "cic:/CoRN/algebra/CLogic/CNot.con".

inline "cic:/CoRN/algebra/CLogic/Ccontrapos'.con".

inline "cic:/CoRN/algebra/CLogic/COr.ind".

(*#* 
Some lemmas to make it possible to use [Step] when reasoning with
biimplications.*)

(* NOTATION
Infix "IFF" := Iff (at level 60, right associativity).
*)

inline "cic:/CoRN/algebra/CLogic/Iff_left.con".

inline "cic:/CoRN/algebra/CLogic/Iff_right.con".

inline "cic:/CoRN/algebra/CLogic/Iff_refl.con".

inline "cic:/CoRN/algebra/CLogic/Iff_sym.con".

inline "cic:/CoRN/algebra/CLogic/Iff_trans.con".

inline "cic:/CoRN/algebra/CLogic/Iff_imp_imp.con".

(* UNEXPORTED
Declare Right Step Iff_right.
*)

(* UNEXPORTED
Declare Left Step Iff_left.
*)

(* UNEXPORTED
Hint Resolve Iff_trans Iff_sym Iff_refl Iff_right Iff_left Iff_imp_imp : algebra.
*)

(* UNEXPORTED
End Basics
*)

(* begin hide *)

(* NOTATION
Infix "or" := COr (at level 85, right associativity).
*)

(* NOTATION
Infix "and" := CAnd (at level 80, right associativity).
*)

(* end hide *)

inline "cic:/CoRN/algebra/CLogic/not_r_cor_rect.con".

inline "cic:/CoRN/algebra/CLogic/not_l_cor_rect.con".

(* begin hide *)

(* NOTATION
Notation "{ x : A  |  P }" := (sigT (fun x : A => P):CProp)
  (at level 0, x at level 99) : type_scope.
*)

(* NOTATION
Notation "{ x : A  |  P  |  Q }" :=
  (sig2T A (fun x : A => P) (fun x : A => Q)) (at level 0, x at level 99) :
  type_scope.
*)

(* end hide *)

(*
Section test.

Variable A:Type.
Variables P,Q:A->Prop.
Variables X,Y:A->CProp.

Check {x:A | (P x)}.
Check {x:A |(X x)}.
Check {x:A | (X x) | (Y x)}.
Check {x:A | (P x) | (Q x)}.
Check {x:A | (P x) | (X x)}.
Check {x:A | (X x) | (P x)}.

End test.
*)

(* UNEXPORTED
Hint Resolve CI CAnd_intro Cinleft Cinright existT exist2T: core.
*)

(* UNEXPORTED
Section Choice
*)

(* **Choice
Let [P] be a predicate on $\NN^2$#N times N#.
*)

alias id "P" = "cic:/CoRN/algebra/CLogic/Choice/P.var".

inline "cic:/CoRN/algebra/CLogic/choice.con".

(* UNEXPORTED
End Choice
*)

(* UNEXPORTED
Section Logical_Remarks
*)

(*#* We prove a few logical results which are helpful to have as lemmas
when [A], [B] and [C] are non trivial.
*)

inline "cic:/CoRN/algebra/CLogic/CNot_Not_or.con".

inline "cic:/CoRN/algebra/CLogic/CdeMorgan_ex_all.con".

(* UNEXPORTED
End Logical_Remarks
*)

(* UNEXPORTED
Section CRelation_Definition
*)

(*#* ** [CProp]-valued Relations
Similar to Relations.v in Coq's standard library.

%\begin{convention}% Let [A:Type] and [R:Crelation].
%\end{convention}%
*)

alias id "A" = "cic:/CoRN/algebra/CLogic/CRelation_Definition/A.var".

inline "cic:/CoRN/algebra/CLogic/Crelation.con".

alias id "R" = "cic:/CoRN/algebra/CLogic/CRelation_Definition/R.var".

inline "cic:/CoRN/algebra/CLogic/Creflexive.con".

inline "cic:/CoRN/algebra/CLogic/Ctransitive.con".

inline "cic:/CoRN/algebra/CLogic/Csymmetric.con".

inline "cic:/CoRN/algebra/CLogic/Cequiv.con".

(* UNEXPORTED
End CRelation_Definition
*)

(* UNEXPORTED
Section TRelation_Definition
*)

(*#* ** [Prop]-valued Relations
Analogous.

%\begin{convention}% Let [A:Type] and [R:Trelation].
%\end{convention}%
*)

alias id "A" = "cic:/CoRN/algebra/CLogic/TRelation_Definition/A.var".

inline "cic:/CoRN/algebra/CLogic/Trelation.con".

alias id "R" = "cic:/CoRN/algebra/CLogic/TRelation_Definition/R.var".

inline "cic:/CoRN/algebra/CLogic/Treflexive.con".

inline "cic:/CoRN/algebra/CLogic/Ttransitive.con".

inline "cic:/CoRN/algebra/CLogic/Tsymmetric.con".

inline "cic:/CoRN/algebra/CLogic/Tequiv.con".

(* UNEXPORTED
End TRelation_Definition
*)

inline "cic:/CoRN/algebra/CLogic/eqs.ind".

(* UNEXPORTED
Section le_odd
*)

(*#* ** The relation [le], [lt], [odd] and [even] in [CProp]
*)

inline "cic:/CoRN/algebra/CLogic/Cle.ind".

inline "cic:/CoRN/algebra/CLogic/Cnat_double_ind.con".

inline "cic:/CoRN/algebra/CLogic/my_Cle_ind.con".

inline "cic:/CoRN/algebra/CLogic/Cle_n_S.con".

inline "cic:/CoRN/algebra/CLogic/toCle.con".

(* UNEXPORTED
Hint Resolve toCle.
*)

inline "cic:/CoRN/algebra/CLogic/Cle_to.con".

inline "cic:/CoRN/algebra/CLogic/Clt.con".

inline "cic:/CoRN/algebra/CLogic/toCProp_lt.con".

inline "cic:/CoRN/algebra/CLogic/Clt_to.con".

inline "cic:/CoRN/algebra/CLogic/Cle_le_S_eq.con".

inline "cic:/CoRN/algebra/CLogic/Cnat_total_order.con".

inline "cic:/CoRN/algebra/CLogic/Codd.ind".

inline "cic:/CoRN/algebra/CLogic/Codd_even_to.con".

inline "cic:/CoRN/algebra/CLogic/Codd_to.con".

inline "cic:/CoRN/algebra/CLogic/Ceven_to.con".

inline "cic:/CoRN/algebra/CLogic/to_Codd_even.con".

inline "cic:/CoRN/algebra/CLogic/to_Codd.con".

inline "cic:/CoRN/algebra/CLogic/to_Ceven.con".

(* UNEXPORTED
End le_odd
*)

(* UNEXPORTED
Section Misc
*)

(*#* **Miscellaneous
*)

inline "cic:/CoRN/algebra/CLogic/CZ_exh.con".

inline "cic:/CoRN/algebra/CLogic/Cnats_Z_ind.con".

inline "cic:/CoRN/algebra/CLogic/Cdiff_Z_ind.con".

inline "cic:/CoRN/algebra/CLogic/Cpred_succ_Z_ind.con".

inline "cic:/CoRN/algebra/CLogic/not_r_sum_rec.con".

inline "cic:/CoRN/algebra/CLogic/not_l_sum_rec.con".

(* UNEXPORTED
End Misc
*)

(*#* **Results about the natural numbers

We now define a class of predicates on a finite subset of natural
numbers that will be important throughout all our work.  Essentially,
these are simply setoid predicates, but for clarity we will never
write them in that form but we will single out the preservation of the
setoid equality.
*)

inline "cic:/CoRN/algebra/CLogic/nat_less_n_pred.con".

inline "cic:/CoRN/algebra/CLogic/nat_less_n_pred'.con".

(* UNEXPORTED
Implicit Arguments nat_less_n_pred [n].
*)

(* UNEXPORTED
Implicit Arguments nat_less_n_pred' [n].
*)

(* UNEXPORTED
Section Odd_and_Even
*)

(*#*
For our work we will many times need to distinguish cases between even or odd numbers.
We begin by proving that this case distinction is decidable.
Next, we prove the usual results about sums of even and odd numbers:
*)

inline "cic:/CoRN/algebra/CLogic/even_plus_n_n.con".

inline "cic:/CoRN/algebra/CLogic/even_or_odd_plus.con".

(*#* Finally, we prove that an arbitrary natural number can be written in some canonical way.
*)

inline "cic:/CoRN/algebra/CLogic/even_or_odd_plus_gt.con".

(* UNEXPORTED
End Odd_and_Even
*)

(* UNEXPORTED
Hint Resolve even_plus_n_n: arith.
*)

(* UNEXPORTED
Hint Resolve toCle: core.
*)

(* UNEXPORTED
Section Natural_Numbers
*)

(*#* **Algebraic Properties

We now present a series of trivial things proved with [Omega] that are
stated as lemmas to make proofs shorter and to aid in auxiliary
definitions.  Giving a name to these results allows us to use them in
definitions keeping conciseness.
*)

inline "cic:/CoRN/algebra/CLogic/Clt_le_weak.con".

inline "cic:/CoRN/algebra/CLogic/lt_5.con".

inline "cic:/CoRN/algebra/CLogic/lt_8.con".

inline "cic:/CoRN/algebra/CLogic/pred_lt.con".

inline "cic:/CoRN/algebra/CLogic/lt_10.con".

inline "cic:/CoRN/algebra/CLogic/lt_pred'.con".

inline "cic:/CoRN/algebra/CLogic/le_1.con".

inline "cic:/CoRN/algebra/CLogic/le_2.con".

inline "cic:/CoRN/algebra/CLogic/plus_eq_one_imp_eq_zero.con".

inline "cic:/CoRN/algebra/CLogic/not_not_lt.con".

inline "cic:/CoRN/algebra/CLogic/plus_pred_pred_plus.con".

(*#* We now prove some properties of functions on the natural numbers.

%\begin{convention}% Let [H:nat->nat].
%\end{convention}%
*)

alias id "h" = "cic:/CoRN/algebra/CLogic/Natural_Numbers/h.var".

(*#*
First we characterize monotonicity by a local condition: if [h(n) < h(n+1)]
for every natural number [n] then [h] is monotonous.  An analogous result
holds for weak monotonicity.
*)

inline "cic:/CoRN/algebra/CLogic/nat_local_mon_imp_mon.con".

inline "cic:/CoRN/algebra/CLogic/nat_local_mon_imp_mon_le.con".

(*#* A strictly increasing function is injective: *)

inline "cic:/CoRN/algebra/CLogic/nat_mon_imp_inj.con".

(*#* And (not completely trivial) a function that preserves [lt] also preserves [le]. *)

inline "cic:/CoRN/algebra/CLogic/nat_mon_imp_mon'.con".

(*#*
The last lemmas in this section state that a monotonous function in the
 natural numbers completely covers the natural numbers, that is, for every
natural number [n] there is an [i] such that [h(i) <= n<(n+1) <= h(i+1)].
These are useful for integration.
*)

inline "cic:/CoRN/algebra/CLogic/mon_fun_covers.con".

inline "cic:/CoRN/algebra/CLogic/weird_mon_covers.con".

(* UNEXPORTED
End Natural_Numbers
*)

(*#*
Useful for the Fundamental Theorem of Algebra.
*)

inline "cic:/CoRN/algebra/CLogic/kseq_prop.con".

(* UNEXPORTED
Section Predicates_to_CProp
*)

(*#* **Logical Properties

This section contains lemmas that aid in logical reasoning with
natural numbers.  First, we present some principles of induction, both
for [CProp]- and [Prop]-valued predicates.  We begin by presenting the
results for [CProp]-valued predicates:
*)

inline "cic:/CoRN/algebra/CLogic/even_induction.con".

inline "cic:/CoRN/algebra/CLogic/odd_induction.con".

inline "cic:/CoRN/algebra/CLogic/four_induction.con".

inline "cic:/CoRN/algebra/CLogic/nat_complete_double_induction.con".

inline "cic:/CoRN/algebra/CLogic/odd_double_ind.con".

(*#* For subsetoid predicates in the natural numbers we can eliminate
disjunction (and existential quantification) as follows.
*)

inline "cic:/CoRN/algebra/CLogic/finite_or_elim.con".

inline "cic:/CoRN/algebra/CLogic/str_finite_or_elim.con".

(* UNEXPORTED
End Predicates_to_CProp
*)

(* UNEXPORTED
Section Predicates_to_Prop
*)

(*#* Finally, analogous results for [Prop]-valued predicates are presented for
completeness's sake.
*)

inline "cic:/CoRN/algebra/CLogic/even_ind.con".

inline "cic:/CoRN/algebra/CLogic/odd_ind.con".

inline "cic:/CoRN/algebra/CLogic/nat_complete_double_ind.con".

inline "cic:/CoRN/algebra/CLogic/four_ind.con".

(* UNEXPORTED
End Predicates_to_Prop
*)

(*#* **Integers

Similar results for integers.
*)

(* begin hide *)

(* UNEXPORTED
Tactic Notation "ElimCompare" constr(c) constr(d) :=  elim_compare c d.
*)

(* end hide *)

inline "cic:/CoRN/algebra/CLogic/Zlts.con".

inline "cic:/CoRN/algebra/CLogic/toCProp_Zlt.con".

inline "cic:/CoRN/algebra/CLogic/CZlt_to.con".

inline "cic:/CoRN/algebra/CLogic/Zsgn_1.con".

inline "cic:/CoRN/algebra/CLogic/Zsgn_2.con".

inline "cic:/CoRN/algebra/CLogic/Zsgn_3.con".

(*#* The following have unusual names, in line with the series of lemmata in
fast_integers.v.
*)

inline "cic:/CoRN/algebra/CLogic/ZL4'.con".

inline "cic:/CoRN/algebra/CLogic/ZL9.con".

inline "cic:/CoRN/algebra/CLogic/Zsgn_4.con".

inline "cic:/CoRN/algebra/CLogic/Zsgn_5.con".

inline "cic:/CoRN/algebra/CLogic/nat_nat_pos.con".

inline "cic:/CoRN/algebra/CLogic/S_predn.con".

inline "cic:/CoRN/algebra/CLogic/absolu_1.con".

inline "cic:/CoRN/algebra/CLogic/absolu_2.con".

inline "cic:/CoRN/algebra/CLogic/Zgt_mult_conv_absorb_l.con".

inline "cic:/CoRN/algebra/CLogic/Zgt_mult_reg_absorb_l.con".

inline "cic:/CoRN/algebra/CLogic/Zmult_Sm_Sn.con".

(* NOTATION
Notation ProjT1 := (proj1_sigT _ _).
*)

(* NOTATION
Notation ProjT2 := (proj2_sigT _ _).
*)


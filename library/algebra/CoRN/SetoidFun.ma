(**************************************************************************)
(*       ___                                                              *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||       A.Asperti, C.Sacerdoti Coen,                          *)
(*      ||A||       E.Tassi, S.Zacchiroli                                 *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU Lesser General Public License Version 2.1         *)
(*                                                                        *)
(**************************************************************************)

(* $Id: CSetoidFun.v,v 1.12 2004/09/22 11:06:10 loeb Exp $ *)

set "baseuri" "cic:/matita/algebra/CoRN/SetoidFun".
include "algebra/CoRN/Setoids.ma".


definition ap_fun : \forall A,B : CSetoid. \forall f,g : CSetoid_fun A B. Prop \def
\lambda A,B : CSetoid. \lambda f,g : CSetoid_fun A B.
 \exists a:A. (csf_fun A B f) a \neq (csf_fun A B g) a.
(* Definition ap_fun (A B : CSetoid) (f g : CSetoid_fun A B) :=
  {a : A | f a[#]g a}. *)

definition eq_fun : \forall A,B : CSetoid. \forall f,g : CSetoid_fun A B. Prop \def
\lambda A,B : CSetoid. \lambda f,g : CSetoid_fun A B.
 \forall a:A. (csf_fun A B f) a = (csf_fun A B g) a.
(* Definition eq_fun (A B : CSetoid) (f g : CSetoid_fun A B) :=
  forall a : A, f a[=]g a. *)   
  
lemma irrefl_apfun : \forall A,B : CSetoid. 
 irreflexive (CSetoid_fun A B) (ap_fun A B).
intros.
unfold irreflexive. intro f.
unfold ap_fun.
unfold.
intro.
elim H.
cut (csf_fun A B f a = csf_fun A B f a)
[ 
 apply eq_imp_not_ap.
 apply A.
 assumption. 
 assumption.
 auto. 
 auto 
|
 apply eq_reflexive_unfolded 
]
qed.

(*
Lemma irrefl_apfun : forall A B : CSetoid, irreflexive (ap_fun A B).
intros A B.
unfold irreflexive in |- *.
intros f.
unfold ap_fun in |- *.
red in |- *.
intro H.
elim H.
intros a H0.
set (H1 := ap_irreflexive_unfolded B (f a)) in *.
intuition.
Qed.
*)


(*
lemma cotrans_apfun : \forall A,B : CSetoid. cotransitive (CSetoid_fun A B) (ap_fun A B).
intros (A B).
unfold.
unfold ap_fun.
intros (f g H h).
decompose.
apply ap_cotransitive.
apply (ap_imp_neq B (csf_fun A B x a) (csf_fun A B y a) H1).
(* letin foo \def (\exist a:A.csf_fun A B x a\neq csf_fun A B z a). *)


apply (ap_cotransitive B ? ? H1 ?).

split.
left.
elim H.
clear H.
intros a H.
set (H1 := ap_cotransitive B (f a) (g a) H (h a)) in *.
elim H1.
clear H1.
intros H1.
left.
exists a.
exact H1.

clear H1.
intro H1.
right.
exists a.
exact H1.
Qed.
*)

(*
Lemma cotrans_apfun : forall A B : CSetoid, cotransitive (ap_fun A B).
intros A B.
unfold cotransitive in |- *.
unfold ap_fun in |- *.
intros f g H h.
elim H.
clear H.
intros a H.
set (H1 := ap_cotransitive B (f a) (g a) H (h a)) in *.
elim H1.
clear H1.
intros H1.
left.
exists a.
exact H1.

clear H1.
intro H1.
right.
exists a.
exact H1.
Qed.
*)

lemma ta_apfun : \forall A, B : CSetoid. tight_apart (CSetoid_fun A B) (eq_fun A B) (ap_fun A B).
unfold tight_apart.
intros (A B f g).
unfold ap_fun.
unfold eq_fun.
split
[ intros. elim H. unfold in H.
generalize in match H. reduce. simplify .unfold.
 
 |
]
intros.
red in H.
apply not_ap_imp_eq.
red in |- *.
intros H0.
apply H.
exists a.
exact H0.
intros H.
red in |- *.

intro H1.
elim H1.
intros a X.
set (H2 := eq_imp_not_ap B (f a) (g a) (H a) X) in *.
exact H2.
Qed.

(*
Lemma ta_apfun : forall A B : CSetoid, tight_apart (eq_fun A B) (ap_fun A B).
unfold tight_apart in |- *.
unfold ap_fun in |- *.
unfold eq_fun in |- *.
intros A B f g.
split.
intros H a.
red in H.
apply not_ap_imp_eq.
red in |- *.
intros H0.
apply H.
exists a.
exact H0.
intros H.
red in |- *.

intro H1.
elim H1.
intros a X.
set (H2 := eq_imp_not_ap B (f a) (g a) (H a) X) in *.
exact H2.
Qed.
*)

Lemma sym_apfun : forall A B : CSetoid, Csymmetric (ap_fun A B).
unfold Csymmetric in |- *.
unfold ap_fun in |- *.
intros A B f g H.
elim H.
clear H.
intros a H.
exists a.
apply ap_symmetric_unfolded.
exact H.
Qed.

Definition FS_is_CSetoid (A B : CSetoid) :=
  Build_is_CSetoid (CSetoid_fun A B) (eq_fun A B) (ap_fun A B)
  (irrefl_apfun A B) (sym_apfun A B) (cotrans_apfun A B) (ta_apfun A B).

Definition FS_as_CSetoid (A B : CSetoid) :=
  Build_CSetoid (CSetoid_fun A B) (eq_fun A B) (ap_fun A B)
    (FS_is_CSetoid A B).

(** **Nullary and n-ary operations
*)

Definition is_nullary_operation (S:CSetoid) (s:S):Prop := True.

Fixpoint n_ary_operation (n:nat)(V:CSetoid){struct n}:CSetoid:=
match n with
|0 => V
|(S m)=> (FS_as_CSetoid V (n_ary_operation m V))
end.

Section unary_function_composition.

(** ** Composition of Setoid functions

Let [S1],  [S2] and [S3] be setoids, [f] a
setoid function from [S1] to [S2], and [g] from [S2]
to [S3] in the following definition of composition.  *)

Variables S1 S2 S3 : CSetoid.
Variable f : CSetoid_fun S1 S2.
Variable g : CSetoid_fun S2 S3.

Definition compose_CSetoid_fun : CSetoid_fun S1 S3.
apply (Build_CSetoid_fun _ _ (fun x : S1 => g (f x))).
(* str_ext *)
unfold fun_strext in |- *; intros x y H.
apply (csf_strext _ _ f). apply (csf_strext _ _ g). assumption.
Defined.

End unary_function_composition.

(** ***Composition as operation
*)
Definition comp (A B C : CSetoid) :
  FS_as_CSetoid A B -> FS_as_CSetoid B C -> FS_as_CSetoid A C.
intros A B C f g.
set (H := compose_CSetoid_fun A B C f g) in *.
exact H.
Defined.

Definition comp_as_bin_op (A:CSetoid) : CSetoid_bin_op (FS_as_CSetoid A A).
intro A.
unfold CSetoid_bin_op in |- *.
eapply Build_CSetoid_bin_fun with (comp A A A).
unfold bin_fun_strext in |- *.
unfold comp in |- *.
intros f1 f2 g1 g2.
simpl in |- *.
unfold ap_fun in |- *.
unfold compose_CSetoid_fun in |- *.
simpl in |- *.
elim f1.
unfold fun_strext in |- *.
clear f1.
intros f1 Hf1.
elim f2.
unfold fun_strext in |- *.
clear f2.
intros f2 Hf2.
elim g1.
unfold fun_strext in |- *.
clear g1.
intros g1 Hg1.
elim g2.
unfold fun_strext in |- *.
clear g2.
intros g2 Hg2.
simpl in |- *.
intro H.
elim H.
clear H.
intros a H.
set (H0 := ap_cotransitive A (g1 (f1 a)) (g2 (f2 a)) H (g2 (f1 a))) in *.
elim H0.
clear H0.
intro H0.
right.
exists (f1 a).
exact H0.

clear H0.
intro H0.
left.
exists a.
apply Hg2.
exact H0.
Defined.

Lemma assoc_comp : forall A : CSetoid, associative (comp_as_bin_op A).
unfold associative in |- *.
unfold comp_as_bin_op in |- *.
intros A f g h.
simpl in |- *.
unfold eq_fun in |- *.
simpl in |- *.
intuition.
Qed.

Section unary_and_binary_function_composition.

Definition compose_CSetoid_bin_un_fun (A B C : CSetoid)
  (f : CSetoid_bin_fun B B C) (g : CSetoid_fun A B) : CSetoid_bin_fun A A C.
intros A B C f g.
apply (Build_CSetoid_bin_fun A A C (fun a0 a1 : A => f (g a0) (g a1))).
intros x1 x2 y1 y2 H0.
assert (H10:= csbf_strext B B C f).
red in H10.
assert (H40 := csf_strext A B g).
red in H40.
elim (H10 (g x1) (g x2) (g y1) (g y2) H0); [left | right]; auto.
Defined.

Definition compose_CSetoid_bin_fun A B C (f g : CSetoid_fun A B)
  (h : CSetoid_bin_fun B B C) : CSetoid_fun A C.
intros A B C f g h.
apply (Build_CSetoid_fun A C (fun a : A => h (f a) (g a))).
intros x y H.
elim (csbf_strext _ _ _ _ _ _ _ _ H); apply csf_strext.
Defined.

Definition compose_CSetoid_un_bin_fun A B C (f : CSetoid_bin_fun B B C)
 (g : CSetoid_fun C A) : CSetoid_bin_fun B B A.
intros A0 B0 C f g.
apply Build_CSetoid_bin_fun with (fun x y : B0 => g (f x y)).
intros x1 x2 y1 y2.
case f.
simpl in |- *.
unfold bin_fun_strext in |- *.
case g.
simpl in |- *.
unfold fun_strext in |- *.
intros gu gstrext fu fstrext H.
apply fstrext.
apply gstrext.
exact H.
Defined.

End unary_and_binary_function_composition.

(** ***Projections
*)

Section function_projection.

Lemma proj_bin_fun : forall A B C (f : CSetoid_bin_fun A B C) a, fun_strext (f a).
intros A B C f a.
red in |- *.
elim f.
intro fo.
simpl.
intros csbf_strext0 x y H.
elim (csbf_strext0 _ _ _ _ H); intro H0.
 elim (ap_irreflexive_unfolded _ _ H0).
exact H0.
Qed.

Definition projected_bin_fun A B C (f : CSetoid_bin_fun A B C) (a : A) :=
 Build_CSetoid_fun B C (f a) (proj_bin_fun A B C f a).

End function_projection.

Section BinProj.

Variable S : CSetoid.

Definition binproj1 (x y:S) := x.

Lemma binproj1_strext : bin_fun_strext _ _ _ binproj1.
red in |- *; auto.
Qed.

Definition cs_binproj1 : CSetoid_bin_op S.
red in |- *; apply Build_CSetoid_bin_op with binproj1.
apply binproj1_strext.
Defined.

End BinProj.

(** **Combining operations
%\begin{convention}% Let [S1], [S2] and [S3] be setoids.
%\end{convention}%
*)

Section CombiningOperations.
Variables S1 S2 S3 : CSetoid.

(**
In the following definition, we assume [f] is a setoid function from
[S1] to [S2], and [op] is an unary operation on [S2].
Then [opOnFun] is the composition [op] after [f].
*)
Section CombiningUnaryOperations.
Variable f : CSetoid_fun S1 S2.
Variable op : CSetoid_un_op S2.

Definition opOnFun : CSetoid_fun S1 S2.
apply (Build_CSetoid_fun S1 S2 (fun x : S1 => op (f x))).
(* str_ext *)
unfold fun_strext in |- *; intros x y H.
apply (csf_strext _ _ f x y).
apply (csf_strext _ _ op _ _ H).
Defined.

End CombiningUnaryOperations.

End CombiningOperations.

Section p66E2b4.

(** **The Free Setoid
%\begin{convention}% Let [A:CSetoid].
%\end{convention}%
*)
Variable A:CSetoid.

Definition Astar := (list A).

Definition empty_word := (nil A).

Definition appA:= (app A).

Fixpoint eq_fm (m:Astar)(k:Astar){struct m}:Prop:=
match m with
|nil => match k with
        |nil => True
        |cons a l => False
        end
|cons b n => match k with
        |nil => False
        |cons a l => b[=]a /\ (eq_fm n l)
        end
end.                                 

Fixpoint ap_fm (m:Astar)(k:Astar){struct m}: CProp :=
match m with
|nil => match k with
        |nil => CFalse
        |cons a l => CTrue
        end
|cons b n => match k with
        |nil => CTrue  
        |cons a l => b[#]a or (ap_fm n l)
        end
end.                                

Lemma ap_fm_irreflexive: (irreflexive ap_fm).
unfold irreflexive.
intro x.
induction x.
simpl.
red.
intuition.

simpl.
red.
intro H.
apply IHx.
elim H.
clear H.
generalize (ap_irreflexive A a).
unfold Not.
intuition.

intuition.
Qed.


Lemma ap_fm_symmetric: Csymmetric ap_fm.
unfold Csymmetric.
intros x.
induction x.
intro y.
case  y.
simpl.
intuition.

simpl.
intuition.
simpl.
intro y.
case y.
simpl.
intuition.

simpl.
intros c l  H0.
elim H0.
generalize (ap_symmetric A a c).
intuition.
clear H0.
intro H0.
right.
apply IHx.
exact H0.
Qed.

Lemma ap_fm_cotransitive : (cotransitive ap_fm).
unfold cotransitive.
intro x.
induction x.
simpl.
intro y.
case y.
intuition.

intros c l H z.
case z.
simpl.
intuition.

intuition.

simpl.
intro y.
case y.
intros H z.
case z.
intuition.

simpl.
intuition.

intros c l H z.
case z.
intuition.

simpl.
intros c0 l0.
elim H.
clear H.
intro H.
generalize (ap_cotransitive A a c H c0).
intuition.

clear H.
intro H.
generalize (IHx l H l0).
intuition.
Qed.

Lemma ap_fm_tight : (tight_apart eq_fm ap_fm).
unfold tight_apart.
intros x.
induction x.
simpl.
intro y.
case y.
red.
unfold Not.
intuition.

intuition.

intro y.
simpl.
case y.
intuition.

intros c l.
generalize (IHx l).
red.
intro H0.
elim H0.
intros H1 H2.
split.
intro H3.
split.
red in H3.
generalize (ap_tight A a c).
intuition.

apply H1.
intro H4.
apply H3.
right.
exact H4.

intro H3.
elim H3.
clear H3.
intros H3 H4.
intro H5.
elim H5.
generalize (ap_tight A a c).
intuition.

apply H2.
exact H4.
Qed.

Definition free_csetoid_is_CSetoid:(is_CSetoid Astar eq_fm ap_fm):=
  (Build_is_CSetoid Astar eq_fm ap_fm ap_fm_irreflexive ap_fm_symmetric 
  ap_fm_cotransitive ap_fm_tight).

Definition free_csetoid_as_csetoid:CSetoid:=
(Build_CSetoid Astar eq_fm ap_fm free_csetoid_is_CSetoid).

Lemma app_strext:
  (bin_fun_strext free_csetoid_as_csetoid free_csetoid_as_csetoid 
   free_csetoid_as_csetoid appA).
unfold bin_fun_strext.
intros x1.
induction x1.
simpl.
intro x2.
case x2.
simpl.
intuition.

intuition.

intros x2 y1 y2.
simpl.
case x2.
case y2.
simpl.
intuition.

simpl.
intuition.

case y2.
simpl.
simpl in IHx1.
intros c l H.
elim H.
intuition.

clear H.
generalize (IHx1 l y1 (nil A)).
intuition.

simpl.
intros c l c0 l0.
intro H.
elim H.
intuition.

generalize (IHx1 l0 y1 (cons c l)).
intuition.
Qed.

Definition app_as_csb_fun: 
(CSetoid_bin_fun free_csetoid_as_csetoid free_csetoid_as_csetoid 
  free_csetoid_as_csetoid):=
  (Build_CSetoid_bin_fun free_csetoid_as_csetoid free_csetoid_as_csetoid 
   free_csetoid_as_csetoid appA app_strext).

Lemma eq_fm_reflexive: forall (x:Astar), (eq_fm x x).
intro x.
induction x.
simpl.
intuition.

simpl.
intuition.
Qed.

End p66E2b4.

(** **Partial Functions

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

Section SubSets_of_G.

(** ***Subsets of Setoids

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

Variable S : CSetoid.

Section Conjunction.

Variables P Q : S -> CProp.

Definition conjP (x : S) : CProp := P x and Q x.

Lemma prj1 : forall x : S, conjP x -> P x.
intros x H; inversion_clear H; assumption.
Qed.

Lemma prj2 : forall x : S, conjP x -> Q x.
intros x H; inversion_clear H; assumption.
Qed.

Lemma conj_wd : pred_wd _ P -> pred_wd _ Q -> pred_wd _ conjP.
intros H H0.
red in |- *; intros x y H1 H2.
inversion_clear H1; split.

apply H with x; assumption.

apply H0 with x; assumption.
Qed.

End Conjunction.

Section Disjunction.

Variables P Q : S -> CProp.

(**
Although at this stage we never use it, for completeness's sake we also treat disjunction (corresponding to union of subsets).
*)

Definition disj (x : S) : CProp := P x or Q x.

Lemma inj1 : forall x : S, P x -> disj x.
intros; left; assumption.
Qed.

Lemma inj2 : forall x : S, Q x -> disj x.
intros; right; assumption.
Qed.

Lemma disj_wd : pred_wd _ P -> pred_wd _ Q -> pred_wd _ disj.
intros H H0.
red in |- *; intros x y H1 H2.
inversion_clear H1.

left; apply H with x; assumption.

right; apply H0 with x; assumption.
Qed.

End Disjunction.

Section Extension.

(**
The next definition is a bit tricky, and is useful for choosing among the elements that satisfy a predicate [P] those that also satisfy [R] in the case where [R] is only defined for elements satisfying [P]---consider [R] to be a condition on the image of an object via a function with domain [P].  We chose to call this operation [extension].
*)

Variable P : S -> CProp.
Variable R : forall x : S, P x -> CProp.

Definition extend (x : S) : CProp := P x and (forall H : P x, R x H).

Lemma ext1 : forall x : S, extend x -> P x.
intros x H; inversion_clear H; assumption.
Qed.

Lemma ext2_a : forall x : S, extend x -> {H : P x | R x H}.
intros x H; inversion_clear H.
exists X; auto.
Qed.

Lemma ext2 : forall (x : S) (Hx : extend x), R x (ProjT1 (ext2_a x Hx)).
intros; apply projT2.
Qed.

Lemma extension_wd : pred_wd _ P ->
 (forall (x y : S) Hx Hy, x [=] y -> R x Hx -> R y Hy) -> pred_wd _ extend.
intros H H0.
red in |- *; intros x y H1 H2.
elim H1; intros H3 H4; split.

apply H with x; assumption.

intro H5; apply H0 with x H3; [ apply H2 | apply H4 ].
Qed.

End Extension.

End SubSets_of_G.

Notation Conj := (conjP _).
Implicit Arguments disj [S].

Implicit Arguments extend [S].
Implicit Arguments ext1 [S P R x].
Implicit Arguments ext2 [S P R x].

(** ***Operations

We are now ready to define the concept of partial function between arbitrary setoids.
*)

Record BinPartFunct (S1 S2 : CSetoid) : Type := 
  {bpfdom  :  S1 -> CProp;
   bdom_wd :  pred_wd S1 bpfdom;
   bpfpfun :> forall x : S1, bpfdom x -> S2;
   bpfstrx :  forall x y Hx Hy, bpfpfun x Hx [#] bpfpfun y Hy -> x [#] y}.


Notation BDom := (bpfdom _ _).
Implicit Arguments bpfpfun [S1 S2].

(**
The next lemma states that every partial function is well defined.
*)

Lemma bpfwdef : forall S1 S2 (F : BinPartFunct S1 S2) x y Hx Hy,
 x [=] y -> F x Hx [=] F y Hy.
intros.
apply not_ap_imp_eq; intro H0.
generalize (bpfstrx _ _ _ _ _ _ _ H0).
exact (eq_imp_not_ap _ _ _ H).
Qed.

(** Similar for automorphisms. *)

Record PartFunct (S : CSetoid) : Type := 
  {pfdom  :  S -> CProp;
   dom_wd :  pred_wd S pfdom;
   pfpfun :> forall x : S, pfdom x -> S;
   pfstrx :  forall x y Hx Hy, pfpfun x Hx [#] pfpfun y Hy -> x [#] y}.

Notation Dom := (pfdom _).
Notation Part := (pfpfun _).
Implicit Arguments pfpfun [S].

(**
The next lemma states that every partial function is well defined.
*)

Lemma pfwdef : forall S (F : PartFunct S) x y Hx Hy, x [=] y -> F x Hx [=] F y Hy.
intros.
apply not_ap_imp_eq; intro H0.
generalize (pfstrx _ _ _ _ _ _ H0).
exact (eq_imp_not_ap _ _ _ H).
Qed.

(**
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

Hint Resolve CI: core.

Section CSetoid_Ops.

Variable S : CSetoid.

(**
To begin with, we want to be able to ``see'' each total function as a partial function.
*)

Definition total_eq_part : CSetoid_un_op S -> PartFunct S.
intros f.
apply
 Build_PartFunct with (fun x : S => CTrue) (fun (x : S) (H : CTrue) => f x).
red in |- *; intros; auto.
intros x y Hx Hy H.
exact (csf_strext_unfolded _ _ f _ _ H).
Defined.

Section Part_Function_Const.

(**
In any setoid we can also define constant functions (one for each element of the setoid) and an identity function:

%\begin{convention}% Let [c:S].
%\end{convention}%
*)

Variable c : S.

Definition Fconst := total_eq_part (Const_CSetoid_fun _ _ c).

End Part_Function_Const.

Section Part_Function_Id.

Definition Fid := total_eq_part (id_un_op S).

End Part_Function_Id.

(**
(These happen to be always total functions, but that is more or less obvious, as we have no information on the setoid; however, we will be able to define partial functions just applying other operators to these ones.)

If we have two setoid functions [F] and [G] we can always compose them.  The domain of our new function will be the set of points [s] in the domain of [F] for which [F(s)] is in the domain of [G]#. #%\footnote{%Notice that the use of extension here is essential.%}.%  The inversion in the order of the variables is done to maintain uniformity with the usual mathematical notation.

%\begin{convention}% Let [G,F:(PartFunct S)] and denote by [Q] and [P], respectively, the predicates characterizing their domains.
%\end{convention}%
*)

Section Part_Function_Composition.

Variables G F : PartFunct S.

(* begin hide *)
Let P := Dom F.
Let Q := Dom G.
(* end hide *)
Let R x := {Hx : P x | Q (F x Hx)}.

Lemma part_function_comp_strext : forall x y (Hx : R x) (Hy : R y),
 G (F x (ProjT1 Hx)) (ProjT2 Hx) [#] G (F y (ProjT1 Hy)) (ProjT2 Hy) -> x [#] y.
intros x y Hx Hy H.
exact (pfstrx _ _ _ _ _ _ (pfstrx _ _ _ _ _ _ H)).
Qed.

Lemma part_function_comp_dom_wd : pred_wd S R.
red in |- *; intros x y H H0.
unfold R in |- *; inversion_clear H.
exists (dom_wd _ F x y x0 H0).
apply (dom_wd _ G) with (F x x0).
assumption.
apply pfwdef; assumption.
Qed.

Definition Fcomp := Build_PartFunct _ R part_function_comp_dom_wd
  (fun x (Hx : R x) => G (F x (ProjT1 Hx)) (ProjT2 Hx))
  part_function_comp_strext.

End Part_Function_Composition.

End CSetoid_Ops.

(**
%\begin{convention}% Let [F:(BinPartFunct S1 S2)] and [G:(PartFunct S2 S3)], and denote by [Q] and [P], respectively, the predicates characterizing their domains.
%\end{convention}%
*)

Section BinPart_Function_Composition.

Variables S1 S2 S3 : CSetoid.

Variable G : BinPartFunct S2 S3.
Variable F : BinPartFunct S1 S2.

(* begin hide *)
Let P := BDom F.
Let Q := BDom G.
(* end hide *)
Let R x := {Hx : P x | Q (F x Hx)}.

Lemma bin_part_function_comp_strext : forall x y (Hx : R x) (Hy : R y),
 G (F x (ProjT1 Hx)) (ProjT2 Hx) [#] G (F y (ProjT1 Hy)) (ProjT2 Hy) -> x [#] y.
intros x y Hx Hy H.
exact (bpfstrx _ _ _ _ _ _ _ (bpfstrx _ _ _ _ _ _ _ H)).
Qed.

Lemma bin_part_function_comp_dom_wd : pred_wd S1 R.
red in |- *; intros x y H H0.
unfold R in |- *; inversion_clear H.
exists (bdom_wd _ _ F x y x0 H0).
apply (bdom_wd _ _ G) with (F x x0).
assumption.
apply bpfwdef; assumption.
Qed.

Definition BinFcomp := Build_BinPartFunct _ _ R bin_part_function_comp_dom_wd
  (fun x (Hx : R x) => G (F x (ProjT1 Hx)) (ProjT2 Hx))
  bin_part_function_comp_strext.

End BinPart_Function_Composition.

(* Different tokens for compatibility with coqdoc *)

Implicit Arguments Fconst [S].
Notation "[-C-] x" := (Fconst x) (at level 2, right associativity).

Notation FId := (Fid _).

Implicit Arguments Fcomp [S].
Infix "[o]" := Fcomp (at level 65, no associativity).

Hint Resolve pfwdef bpfwdef: algebra.

Section bijections.
(** **Bijections *)

Definition injective A B (f : CSetoid_fun A B) := (forall a0 a1 : A,
 a0 [#] a1 -> f a0 [#] f a1):CProp.

Definition injective_weak A B (f : CSetoid_fun A B) := forall a0 a1 : A,
 f a0 [=] f a1 -> a0 [=] a1.

Definition surjective A B (f : CSetoid_fun A B) := (forall b : B, {a : A | f a [=] b}):CProp.

Implicit Arguments injective [A B].
Implicit Arguments injective_weak [A B].
Implicit Arguments surjective [A B].

Lemma injective_imp_injective_weak : forall A B (f : CSetoid_fun A B),
 injective f -> injective_weak f.
intros A B f.
unfold injective in |- *.
intro H.
unfold injective_weak in |- *.
intros a0 a1 H0.
apply not_ap_imp_eq.
red in |- *.
intro H1.
set (H2 := H a0 a1 H1) in *.
set (H3 := ap_imp_neq B (f a0) (f a1) H2) in *.
set (H4 := eq_imp_not_neq B (f a0) (f a1) H0) in *.
apply H4.
exact H3.
Qed.

Definition bijective A B (f:CSetoid_fun A B) := injective f and surjective f.

Implicit Arguments bijective [A B].

Lemma id_is_bij : forall A, bijective (id_un_op A).
intro A.
split.
 red; simpl; auto.
intro b; exists b; apply eq_reflexive.
Qed.

Lemma comp_resp_bij : forall A B C f g, bijective f -> bijective g ->
 bijective (compose_CSetoid_fun A B C f g).
intros A B C f g.
intros H0 H1.
elim H0; clear H0; intros H00 H01.
elim H1; clear H1; intros H10 H11.
split.
 intros a0 a1; simpl; intro.
 apply H10; apply H00; auto.
intro c; simpl.
elim (H11 c); intros b H20.
elim (H01 b); intros a H30.
exists a.
Step_final (g b).
Qed.

Lemma inv : forall A B (f:CSetoid_fun A B),
 bijective f -> forall b : B, {a : A | f a [=] b}.
unfold bijective in |- *.
unfold surjective in |- *.
intuition.
Qed.

Implicit Arguments inv [A B].

Definition invfun A B (f : CSetoid_fun A B) (H : bijective f) : B -> A.
intros A B f H H0.
elim (inv f H H0); intros a H2.
apply a.
Defined.

Implicit Arguments invfun [A B].

Lemma inv1 : forall A B (f : CSetoid_fun A B) (H : bijective f) (b : B),
 f (invfun f H b) [=] b.
intros A B f H b.
unfold invfun in |- *; case inv.
simpl; auto.
Qed.

Lemma inv2 : forall A B (f : CSetoid_fun A B) (H : bijective f) (a : A),
 invfun f H (f a) [=] a.
intros.
unfold invfun in |- *; case inv; simpl.
elim H; clear H; intros H0 H1.
intro x.
apply injective_imp_injective_weak.
auto.
Qed.

Lemma inv_strext : forall A B (f : CSetoid_fun A B) (H : bijective f),
 fun_strext (invfun f H).
intros A B f H x y.
intro H1.
elim H; intros H00 H01.
elim (H01 x); intros a0 H2.
elim (H01 y); intros a1 H3.
astepl (f a0).
astepr (f a1).
apply H00.
astepl (invfun f H x).
astepr (invfun f H y).
exact H1.
astepl (invfun f H (f a1)).
apply inv2.
apply injective_imp_injective_weak with (f := f); auto.
astepl (f a1).
astepl y.
apply eq_symmetric.
apply inv1.
apply eq_symmetric.
apply inv1.
astepl (invfun f H (f a0)).
apply inv2.

apply injective_imp_injective_weak with (f := f); auto.
astepl (f a0).
astepl x.
apply eq_symmetric; apply inv1.
apply eq_symmetric; apply inv1.
Qed.

Definition Inv A B f (H : bijective f) :=
  Build_CSetoid_fun B A (invfun f H) (inv_strext A B f H).

Implicit Arguments Inv [A B].

Definition Inv_bij : forall A B (f : CSetoid_fun A B) (H : bijective f),
  bijective (Inv f H).
intros A B f H.
unfold bijective in |- *.
split.
unfold injective in |- *.
unfold bijective in H.
unfold surjective in H.
elim H.
intros H0 H1.
intros b0 b1 H2.
elim (H1 b0).
intros a0 H3.
elim (H1 b1).
intros a1 H4.
astepl (Inv f (CAnd_intro _ _ H0 H1) (f a0)).
astepr (Inv f (CAnd_intro _ _ H0 H1) (f a1)).
cut (fun_strext f).
unfold fun_strext in |- *.
intros H5.
apply H5.
astepl (f a0).
astepr (f a1).
astepl b0.
astepr b1.
exact H2.
apply eq_symmetric.
unfold Inv in |- *.
simpl in |- *.
apply inv1.
apply eq_symmetric.
unfold Inv in |- *.
simpl in |- *.
apply inv1.
elim f.
intuition.

unfold surjective in |- *.
intro a.
exists (f a).
unfold Inv in |- *.
simpl in |- *.
apply inv2.
Qed.


End bijections.
Implicit Arguments bijective [A B].
Implicit Arguments injective [A B].
Implicit Arguments injective_weak [A B].
Implicit Arguments surjective [A B].
Implicit Arguments inv [A B].
Implicit Arguments invfun [A B].
Implicit Arguments Inv [A B].

Implicit Arguments conj_wd [S P Q].

Notation Prj1 := (prj1 _ _ _ _).
Notation Prj2 := (prj2 _ _ _ _).

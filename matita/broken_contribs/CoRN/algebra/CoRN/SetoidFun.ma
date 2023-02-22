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
include "higher_order_defs/relations.ma".

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
[ apply (eq_imp_not_ap A)
 [
  assumption|assumption|apply eq_reflexive_unfolded|
  apply (csf_strext_unfolded A B f).
  exact H1
 ]
|apply eq_reflexive_unfolded 
]
qed.

lemma cotrans_apfun : \forall A,B : CSetoid. cotransitive (CSetoid_fun A B) (ap_fun A B).
intros (A B).
unfold.
unfold ap_fun.
intros (f g H h).
elim H.
lapply (ap_cotransitive ? ? ? H1 (csf_fun A B h a)).
elim Hletin.
left.
apply (ex_intro ? ? a H2).
right.
apply (ex_intro ? ? a H2).
qed.

lemma ta_apfun : \forall A, B : CSetoid. tight_apart (CSetoid_fun A B) (eq_fun A B) (ap_fun A B).
unfold tight_apart.
intros (A B f g).
unfold ap_fun.
unfold eq_fun.
split
[ intros. apply not_ap_imp_eq.
unfold.intro.apply H.
apply (ex_intro ? ? a).assumption.
 | intros.unfold.intro.
   elim H1.
   apply (eq_imp_not_ap ? ? ? ? H2).
   apply H.
]
qed.

lemma sym_apfun : \forall A, B : CSetoid. symmetric ? (ap_fun A B).
unfold symmetric.
unfold ap_fun.
intros 5 (A B f g H).
elim H 0.
clear H.
intros 2 (a H).
apply (ex_intro ? ? a).
apply ap_symmetric_unfolded.
exact H.
qed.

definition FS_is_CSetoid : \forall A, B : CSetoid. ? \def
  \lambda A, B : CSetoid.
    mk_is_CSetoid (CSetoid_fun A B) (eq_fun A B) (ap_fun A B)
    (irrefl_apfun A B) (sym_apfun A B) (cotrans_apfun A B) (ta_apfun A B).

definition FS_as_CSetoid : \forall A, B : CSetoid. ? \def
  \lambda A, B : CSetoid.
    mk_CSetoid (CSetoid_fun A B) (eq_fun A B) (ap_fun A B) 
    (FS_is_CSetoid A B).

(* Nullary and n-ary operations *)

definition is_nullary_operation : \forall S:CSetoid. \forall s:S. Prop \def 
\lambda S:CSetoid. \lambda s:S. True.

let rec n_ary_operation (n:nat) (V:CSetoid) on n : CSetoid \def
match n with
[ O \Rightarrow V
|(S m) \Rightarrow (FS_as_CSetoid V (n_ary_operation m V))].


(* Section unary_function_composition. *)

(* Composition of Setoid functions

Let [S1],  [S2] and [S3] be setoids, [f] a
setoid function from [S1] to [S2], and [g] from [S2]
to [S3] in the following definition of composition.  *)

(* Variables S1 S2 S3 : CSetoid.
Variable f : CSetoid_fun S1 S2.
Variable g : CSetoid_fun S2 S3. *)


definition compose_CSetoid_fun : \forall S1,S2,S3 :CSetoid. \forall f: (CSetoid_fun S1 S2). \forall g: (CSetoid_fun S2 S3). 
CSetoid_fun S1 S3.
intros (S1 S2 S3 f g).
apply (mk_CSetoid_fun ? ? (\lambda x :cs_crr S1. csf_fun S2 S3 g (csf_fun S1 S2 f x))).
unfold fun_strext.
intros (x y H).
apply (csf_strext ? ? f).
apply (csf_strext ? ? g).
assumption.
qed.

(* End unary_function_composition. *)

(* Composition as operation *)
definition comp : \forall A, B, C : CSetoid.
FS_as_CSetoid A B \to FS_as_CSetoid B C \to FS_as_CSetoid A C.
intros (A B C f g).
letin H \def (compose_CSetoid_fun A B C f g).
exact H.
qed.

definition comp_as_bin_op : \forall A:CSetoid.  CSetoid_bin_op (FS_as_CSetoid A A).
intro A.
unfold CSetoid_bin_op.
apply (mk_CSetoid_bin_fun ? ? ? (comp A A A)).
unfold bin_fun_strext.
unfold comp.
intros  4 (f1 f2 g1 g2).
simplify.
unfold compose_CSetoid_fun.
simplify.
elim f1 0.
unfold fun_strext.
clear f1.
intros 2 (f1 Hf1).
elim f2 0.
unfold fun_strext.
clear f2.
intros 2 (f2 Hf2).
elim g1 0.
unfold fun_strext.
clear g1.
intros 2 (g1 Hg1).
elim g2 0.
unfold fun_strext.
clear g2.
intros 2 (g2 Hg2).
simplify.
intro H.
elim H 0. 
clear H.
intros 2 (a H).
letin H0 \def (ap_cotransitive A (g1 (f1 a)) (g2 (f2 a)) H (g2 (f1 a))).
elim H0 0.
clear H0.
intro H0.
right.
exists.
apply (f1 a).
exact H0.

clear H0.
intro H0.
left.
exists.
apply a.
apply Hg2.
exact H0.
qed.


(* Questa coercion composta non e' stata generata autobatchmaticamente *)
lemma mycor: ∀S. CSetoid_bin_op S → (S → S → S).
 intros;
 unfold in c;
 apply (c c1 c2).
qed.
coercion cic:/matita/algebra/CoRN/SetoidFun/mycor.con 2.

(* Mettendola a mano con una beta-espansione funzionerebbe *)
(*lemma assoc_comp : \forall A : CSetoid. (CSassociative ? (\lambda e.mycor ? (comp_as_bin_op A) e)).*)
(* Questo sarebbe anche meglio: senza beta-espansione *)
(*lemma assoc_comp : \forall A : CSetoid. (CSassociative ? (mycor ? (comp_as_bin_op A))).*)
(* QUESTO E' QUELLO ORIGINALE MA NON FUNZIONANTE *)
(* lemma assoc_comp : \forall A : CSetoid. (CSassociative ? (comp_as_bin_op A)). *)
lemma assoc_comp : \forall A : CSetoid. (CSassociative ? (mycor ? (comp_as_bin_op A))).
unfold CSassociative.
unfold comp_as_bin_op.
intros 4 (A f g h).
simplify.
elim f.
elim g.
elim h.
whd.intros.
simplify.
apply eq_reflexive_unfolded.
qed.

definition compose_CSetoid_bin_un_fun: \forall A,B,C : CSetoid. 
\forall f : CSetoid_bin_fun B B C. \forall g : CSetoid_fun A B.  
CSetoid_bin_fun A A C.
intros 5 (A B C f g).
apply (mk_CSetoid_bin_fun A A C (\lambda a0,a1 : cs_crr A. f (csf_fun ? ? g a0) (csf_fun ? ? g a1))).
unfold.
intros 5 (x1 x2 y1 y2 H0).
letin H10 \def (csbf_strext B B C f).
unfold in H10.
letin H40 \def (csf_strext A B g).
unfold in H40.
elim (H10 (csf_fun ? ? g x1) (csf_fun ? ? g x2) (csf_fun ? ? g y1) (csf_fun ? ? g y2) H0); 
[left | right]; autobatch.
qed.

definition compose_CSetoid_bin_fun: \forall A, B, C : CSetoid. 
\forall f,g : CSetoid_fun A B.\forall h : CSetoid_bin_fun B B C.
CSetoid_fun A C.
intros (A B C f g h).
apply (mk_CSetoid_fun A C (λa : cs_crr A. csbf_fun ? ? ? h (csf_fun ? ? f a) (csf_fun ? ? g a))).
unfold.
intros (x y H).
elim (csbf_strext ? ? ? ? ? ? ? ? H)[
 apply (csf_strext A B f).exact H1
 |apply (csf_strext A B g).exact H1]
qed.

definition compose_CSetoid_un_bin_fun: \forall A,B,C :CSetoid. \forall f : CSetoid_bin_fun B B C.
 ∀ g : CSetoid_fun C A. CSetoid_bin_fun B B A.
intros (A0 B0 C f g).
apply (mk_CSetoid_bin_fun ? ? ? (\lambda x,y : B0. csf_fun ? ? g (f x y))).
unfold.
intros 4 (x1 x2 y1 y2).
elim f 0.
unfold bin_fun_strext.
elim g 0.
unfold fun_strext.
intros 5 (gu gstrext fu fstrext H).
apply fstrext.
apply gstrext.
exact H.
qed.

(* End unary_and_binary_function_composition.*)

(*Projections*)

(*Section function_projection.*)

lemma proj_bin_fun : \forall A, B, C: CSetoid. 
\forall f : CSetoid_bin_fun A B C. \forall a: ?. 
fun_strext ? ? (f a).
intros (A B C f a).
unfold.
elim f 0.
intro fo.
simplify.
intros 4 (csbf_strext0 x y H).
elim (csbf_strext0 ? ? ? ? H) 0; intro H0.
 elim (ap_irreflexive_unfolded ? ? H0).
exact H0.
qed.


definition projected_bin_fun: \forall A,B,C : CSetoid. \forall f : CSetoid_bin_fun A B C.
\forall a : A. ? \def
\lambda A,B,C : CSetoid. \lambda f : CSetoid_bin_fun A B C.
\lambda a : A.
 mk_CSetoid_fun B C (f a) (proj_bin_fun A B C f a).

(* End function_projection. *)

(* Section BinProj. *)

(* Variable S : CSetoid. *)

definition binproj1 : \forall S: CSetoid. \forall x,y:S. ? \def
\lambda S:CSetoid. \lambda x,y:S.
 x.
 
lemma binproj1_strext :\forall S:CSetoid. bin_fun_strext ? ? ? (binproj1 S).
intro.unfold;
intros 4.unfold binproj1.intros.left.exact H.
qed.

definition cs_binproj1 :\forall S:CSetoid. CSetoid_bin_op S.
intro.
unfold.
apply (mk_CSetoid_bin_op ? (binproj1 S)).
apply binproj1_strext.
qed.

(* End BinProj. *)

(*Combining operations
%\begin{convention}% Let [S1], [S2] and [S3] be setoids.
%\end{convention}%
*)

(* Section CombiningOperations.
Variables S1 S2 S3 : CSetoid.*)

(*
In the following definition, we assume [f] is a setoid function from
[S1] to [S2], and [op] is an unary operation on [S2].
Then [opOnFun] is the composition [op] after [f].
*)

(* Section CombiningUnaryOperations.
Variable f : CSetoid_fun S1 S2.
Variable op : CSetoid_un_op S2. *)

definition opOnFun : \forall S1,S2,S3 :CSetoid. \forall f : CSetoid_fun S1 S2.
  \forall op : CSetoid_un_op S2.
  CSetoid_fun S1 S2.
intros (S1 S2 S3 f op).
apply (mk_CSetoid_fun S1 S2 (\lambda x :  cs_crr S1. csf_fun ? ? op (csf_fun ? ? f x))).
unfold fun_strext; intros (x y H).
apply (csf_strext ? ? f x y).
apply (csf_strext ? ? op ? ? H).
qed.
(*
End CombiningUnaryOperations.

End CombiningOperations.

Section p66E2b4.
*)
(* The Free Setoid
%\begin{convention}% Let [A:CSetoid].
%\end{convention}%
*)

(* Variable A:CSetoid. *)

(* TODO from listtype.ma!!!!!!!! *)
inductive Tlist (A : Type) : Type \def
    Tnil : Tlist A
  | Tcons : A \to Tlist A  \to Tlist A.

definition Astar: \forall A: CSetoid. ? \def
\lambda A:CSetoid.
 Tlist A.


definition empty_word : \forall A: Type. ? \def
\lambda A:Type. (Tnil A).

(* from listtype.ma!!!!!!!! *)
let rec Tapp (A:Type) (l,m: Tlist A) on l \def
  match l with
  [ Tnil \Rightarrow m
  | (Tcons a l1) \Rightarrow (Tcons  A a (Tapp A l1 m))].

definition appA : \forall A: CSetoid. ? \def
\lambda A:CSetoid.
   (Tapp A).

let rec eq_fm (A:CSetoid) (m:Astar A) (k:Astar A) on m : Prop \def
match m with
[ Tnil ⇒ match k with
        [ Tnil ⇒ True
        | (Tcons  a l) ⇒ False]
| (Tcons  b n) ⇒ match k with
        [Tnil ⇒ False
        |(Tcons  a l) ⇒ b=a ∧ (eq_fm A n l)]
].                                 

let rec CSap_fm (A:CSetoid)(m:Astar A)(k:Astar A) on m: Prop \def
match m with
[Tnil ⇒ match k with
        [Tnil ⇒ False
        |(Tcons a l) ⇒ True]
|(Tcons b n) ⇒ match k with
        [Tnil ⇒ True  
        |(Tcons a l) ⇒ b ≠ a ∨ (CSap_fm A n l)]
].

lemma ap_fm_irreflexive: \forall A:CSetoid. (irreflexive (Astar A) (CSap_fm A) ).
unfold irreflexive.
intros 2 (A x).
elim x[
simplify.
unfold.
intro Hy.
exact Hy|
simplify.
unfold.
intro H1.
apply H.
elim H1[
clear H1.
generalize in match (ap_irreflexive A).
unfold irreflexive.
unfold Not.
intro.
unfold in H.
apply False_ind.
apply H1.apply a.
exact H2|exact H2]
]
qed.

lemma ap_fm_symmetric: \forall A:CSetoid. (symmetric  (Astar A) (CSap_fm A)).
intro A.
unfold symmetric.
intro x.
elim x 0 [
intro y.
  elim y 0[
  simplify.
  intro.
  exact H|
  simplify.
  intros.
  exact H1]|
  intros 4 (t t1 H y).
  elim y 0[
    simplify.
    intro.
    exact H1|
  simplify.
  intros.
  elim H2 0 [
  generalize in match (ap_symmetric A).
  unfold symmetric.
  intros.
  left.
  apply ap_symmetric.exact H4|
  intro.
  right.
  apply H.
  exact H3]
  ]
 ]
qed.

lemma ap_fm_cotransitive : \forall A:CSetoid. (cotransitive (Astar A) (CSap_fm A)).
intro A.
unfold cotransitive.
intro x.
elim x 0 [
intro y.
elim y 0 [
intro.simplify in H.intro.elim z.simplify.left. exact H|intros (c l H1 H z).
elim z 0[ 
simplify.
right. apply I|intros (a at).simplify. left. apply I]]
simplify.
left.
autobatch |intros 2 (c l).
intros 2 (Hy).
elim y 0[
intros 2 (H z).
elim z 0 [simplify. left.apply I|
intros  2 ( a at).
intro H1.
simplify.
right. apply I]|
intros (a at bo H z).
elim z 0[
simplify.left.
apply I|
intros 2 (c0 l0).
elim H 0 [
clear H.
intro.intro Hn.simplify.
generalize in match (ap_cotransitive A c a H c0).
intros.elim H1 0[intros.left. left.exact H2|
intro.right.left.exact H2]|intros.
simplify.
generalize in match (Hy at H1 l0).
intros.
elim H3[
left.right.exact H4|
right.right.exact H4]]]]]
qed.

lemma ap_fm_tight : \forall A:CSetoid.  (tight_apart (Astar A) (eq_fm A) (CSap_fm A)).
intro A.
unfold tight_apart.
intro x.
unfold Not.
elim x 0[
  intro y.
  elim y 0[
    split[simplify.intro.autobatch|simplify.intros.exact H1]|
intros (a at).
simplify.
split[intro.autobatch|intros. exact H1]
]
|
intros (a at IHx).
elim y 0[simplify.
  split[intro.autobatch|intros.exact H]
  |
intros 2 (c l).
generalize in match (IHx l).
intro H0.
elim H0. 
split.
intro H3.
split.
generalize in match (ap_tight A a c).
intros.
elim H4.
clear H4.apply H5.
unfold.intro.simplify in H3.
apply H3.left.exact H4.
intros.elim H2.
apply H.intro.apply H3.simplify. right. exact H6.
intro H3.
elim H3 0.
clear H3.
intros.
elim H5.
generalize in match (ap_tight A a c).
intro.
elim H7.clear H7.
unfold Not in H9.simplify in H5.
apply H9.
exact H3.exact H6.
apply H1.
exact H4.exact H6.]]
qed.

definition free_csetoid_is_CSetoid: \forall A:CSetoid.
  (is_CSetoid (Astar A) (eq_fm A) (CSap_fm A)) \def
  \lambda A:CSetoid.
  (mk_is_CSetoid (Astar A) (eq_fm A) (CSap_fm A) (ap_fm_irreflexive A) (ap_fm_symmetric A) 
  (ap_fm_cotransitive A) (ap_fm_tight A )).

definition free_csetoid_as_csetoid: \forall A:CSetoid. CSetoid \def
\lambda A:CSetoid.
(mk_CSetoid (Astar A) (eq_fm A) (CSap_fm A) (free_csetoid_is_CSetoid A)).

lemma app_strext: \forall A:CSetoid.
 (bin_fun_strext  (free_csetoid_as_csetoid A) (free_csetoid_as_csetoid A) 
   (free_csetoid_as_csetoid A) (appA A)).
intro A.
unfold bin_fun_strext.
intro x1.
elim x1 0[simplify.intro x2.
  elim x2 0[simplify.intros.right.exact H|simplify.intros.left.left]
  |intros 6 (a at IHx1 x2 y1 y2).
  simplify.
    elim x2 0 [
      elim y2 0 [simplify.intros.left.exact H|intros.left.left]
      |elim y2 0[simplify.simplify in IHx1.
        intros (c l H).
        elim H1 0 [intros.left.left.exact H2| clear H1.
          generalize in match (IHx1 l y1 (Tnil A)).
          simplify.intros.elim H1 0 [intros.left.right.exact H3|
            intros.right.exact H3|exact H2]
          ]
        |simplify.
        intros (c l H c0 l0).
      elim H2 0 [intros.left.left.exact H3|
      generalize in match (IHx1 l0 y1 (Tcons A c l)).intros.
        elim H3 0 [intros.left.right.exact H5|intros.right.exact H5|exact H4]
      ]
    ]
  ]
]
qed.

definition app_as_csb_fun: \forall A:CSetoid. 
(CSetoid_bin_fun (free_csetoid_as_csetoid A) (free_csetoid_as_csetoid A)
  (free_csetoid_as_csetoid A)) \def 
  \lambda A:CSetoid.
  (mk_CSetoid_bin_fun (free_csetoid_as_csetoid A) (free_csetoid_as_csetoid A) 
   (free_csetoid_as_csetoid A) (appA A) (app_strext A)).

(* TODO : Can't qed 
lemma eq_fm_reflexive: \forall A:CSetoid. \forall (x:Astar A). (eq_fm A x x).
intros (A x).
elim x.
simplify.left.
simplify. left. apply eq_reflexive_unfolded.assumption.
qed.
*)
(* End p66E2b4. *)

(* Partial Functions

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

(* Section SubSets_of_G. *)

(* Subsets of Setoids

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

(* Variable S : CSetoid.

Section Conjunction.

Variables P Q : S -> CProp.
*)

(* From CLogic.v *)
inductive CAnd (A,B : Type): Type \def 
|CAnd_intro : A \to B \to CAnd A B.

definition conjP : \forall S:CSetoid. \forall P,Q: S \to Type. \forall x : S. Type 
\def
\lambda S:CSetoid. \lambda P,Q: S \to Type. \lambda x : S.
 CAnd (P x)  (Q x).

lemma prj1 : \forall S:CSetoid. \forall P,Q : S \to Type. \forall x : S.
 (conjP S P Q x) \to (P x).
intros;elim c.assumption.
qed.

lemma prj2 : \forall S:CSetoid. \forall P,Q : S \to Type. \forall x : S.
   conjP S P Q x \to Q x.
intros. elim c. assumption.
qed.

lemma conj_wd : \forall S:CSetoid. \forall P,Q : S \to Type. 
  pred_wd ? P \to pred_wd ? Q \to pred_wd ? (conjP S P Q).
  intros 3.
  unfold pred_wd.
  unfold conjP.
  intros.elim c.
  split [ apply (f x ? a).assumption|apply (f1 x ? b). assumption]
qed.

(* End Conjunction. *)

(* Section Disjunction. *)
(* Variables P Q : S -> CProp.*)

(*
Although at this stage we never use it, for completeness's sake we also treat disjunction (corresponding to union of subsets).
*)

definition disj : \forall S:CSetoid. \forall P,Q : S \to Prop. \forall x : S.
  Prop \def 
  \lambda S:CSetoid. \lambda P,Q : S \to Prop. \lambda x : S.
  P x \lor Q x.
  
lemma inj1 : \forall S:CSetoid. \forall P,Q : S \to Prop. \forall x : S. 
  P x \to (disj S P Q x).
intros.
left. 
assumption.
qed.

lemma inj2 : \forall S:CSetoid. \forall P,Q : S \to Prop. \forall x : S.
  Q x \to disj S P Q x.
intros. 
right.
assumption.
qed.

lemma disj_wd : \forall S:CSetoid. \forall P,Q : S \to Prop. 
  pred_wd ? P \to pred_wd ? Q \to pred_wd ? (disj S P Q).
intros 3.
unfold pred_wd.
unfold disj.
intros.
elim H2 [left; apply (H x ); assumption|
  right; apply (H1 x). assumption. exact H3]
qed.
(* End Disjunction. *)

(* Section Extension. *)

(*
The next definition is a bit tricky, and is useful for choosing among the elements that satisfy a predicate [P] those that also satisfy [R] in the case where [R] is only defined for elements satisfying [P]---consider [R] to be a condition on the image of an object via a function with domain [P].  We chose to call this operation [extension].
*)

(*
Variable P : S -> CProp.
Variable R : forall x : S, P x -> CProp.
*)

definition extend : \forall S:CSetoid. \forall P: S \to Type. 
  \forall R : (\forall x:S. P x \to Type). \forall x : S. ? 
  \def
     \lambda S:CSetoid. \lambda P: S \to Type. 
      \lambda R : (\forall x:S. P x \to Type). \lambda x : S.
     CAnd (P x)  (\forall H : P x. (R  x  H) ).
 
lemma ext1 : \forall S:CSetoid. \forall P: S \to Prop. 
  \forall R : (\forall x:S. P x \to Prop). \forall x : S. 
   extend S P R x \to P x.
intros.
elim e. 
assumption.
qed.

inductive sigT (A:Type) (P:A -> Type) : Type \def
    |existT : \forall x:A. P x \to sigT A P.

lemma ext2_a : \forall S:CSetoid. \forall P: S \to Prop. 
  \forall R : (\forall x:S. P x \to Prop). \forall x : S.
  extend S P R x \to (sigT ? (λH : P x. R x H)).
intros.
elim e.
apply (existT).assumption.
apply (b a).
qed.

(*
lemma ext2_a : \forall S:CSetoid. \forall P: S \to Prop. 
  \forall R : (\forall x:S. P x \to Prop). \forall x : S.
  extend S P R x \to (ex ? (λH : P x. R x H)).
intros.
elim H.
apply (ex_intro).
exact H1.apply H2.
qed.
*)
definition proj1_sigT: \forall A : Type. \forall P : A \to Type.
 \forall e : sigT A P. ? \def
  \lambda A : Type. \lambda P : A \to Type.
  \lambda e : sigT A P.
  match e with
   [existT a b \Rightarrow a].
   
(* original def in CLogic.v 
Definition proj1_sigT (A : Type) (P : A -> CProp) (e : sigT P) :=
  match e with
  | existT a b => a
  end.
*)
(* _ *)
definition proj2_sigTm : \forall A : Type. \forall P : A \to Type.
 \forall e : sigT A P. ? \def
 \lambda A : Type. \lambda P : A \to Type.
  \lambda e : sigT A P.
  match e return \lambda s:sigT A P. P (proj1_sigT A P s) with
  [ existT a b \Rightarrow b].
  
definition projT1: \forall A: Type. \forall P: A \to Type.\forall H: sigT A P. A \def
   \lambda A: Type. \lambda P: A \to Type.\lambda H: sigT A P.
   match H with
   [existT x b \Rightarrow x].
    
definition projT2m :  \forall A: Type. \forall P: A \to Type. \forall x:sigT A P.
    P (projT1 A P x) \def
    \lambda A: Type. \lambda P: A \to Type. 
   (\lambda H:sigT A P.match H return \lambda s:sigT A P. P (projT1 A P s) with
 [existT (x:A) (h:(P x))\Rightarrow h]).

lemma ext2 : \forall S:CSetoid. \forall P: S \to Prop. 
\forall R : (\forall x:S. P x \to Prop).
\forall x: S.
 \forall Hx:extend S P R x. 
    R x (proj1_sigT ? ? (ext2_a S P R x Hx)).
    intros.
    elim ext2_a.
    apply (projT2m (P x) (\lambda Hbeta:P x.R x a)).
    apply (existT (P x) ).assumption.assumption.
qed.

(*    
Lemma ext2 : forall (x : S) (Hx : extend x), R x (ProjT1 (ext2_a x Hx)).
intros; apply projT2.

Qed.
*)

lemma extension_wd :\forall S:CSetoid. \forall P: S \to Prop. 
  \forall R : (\forall x:S. P x \to Prop).  
  pred_wd ? P \to
 (\forall (x,y : S).\forall Hx : (P x). 
 \forall Hy : (P y). x = y \to R x Hx \to R y Hy) \to 
  pred_wd ? (extend S P R) .
intros (S P R H H0).
unfold.
intros (x y H1 H2).
elim H1;split[apply (H x).assumption. exact H2|
  intro H5.apply (H0 x ? a)[apply H2|apply b]
  ]
qed.

(*End Extension. *)

(*End SubSets_of_G.*)

(* Notation Conj := (conjP _).
Implicit Arguments disj [S].

Implicit Arguments extend [S].
Implicit Arguments ext1 [S P R x].
Implicit Arguments ext2 [S P R x].
*)
(**Operations

We are now ready to define the concept of partial function between arbitrary setoids.
*)
lemma block : \forall y:nat. \forall x:nat. y = x \to x = y.
intros.
symmetry.exact H.
qed.

record BinPartFunct (S1, S2 : CSetoid) : Type \def 
  {bpfdom  :  S1 \to Type;
   bdom_wd :  pred_wd S1 bpfdom;
   bpfpfun :> \forall x : S1. (bpfdom x) \to S2;
   bpfstrx :  \forall x,y,Hx,Hy.
    bpfpfun x Hx ≠ bpfpfun y Hy \to (x \neq y)}.

(* Notation BDom := (bpfdom _ _).
Implicit Arguments bpfpfun [S1 S2]. *)

(*
The next lemma states that every partial function is well defined.
*)

lemma bpfwdef: \forall S1,S2 : CSetoid. \forall F : (BinPartFunct S1 S2). 
  \forall x,y,Hx,Hy.
 x = y \to (bpfpfun S1 S2 F x Hx ) = (bpfpfun S1 S2 F y Hy).
intros.
apply not_ap_imp_eq;unfold. intro H0.
generalize in match (bpfstrx ? ? ? ? ? ? ? H0).
exact (eq_imp_not_ap ? ? ? H).
qed.

(* Similar for autobatchmorphisms. *)

record PartFunct (S : CSetoid) : Type \def 
  {pfdom  :  S -> Type;
   dom_wd :  pred_wd S pfdom;
   pfpfun :> \forall x : S. pfdom x \to S;
   pfstrx :  \forall x, y, Hx, Hy. pfpfun x Hx \neq pfpfun y Hy \to x \neq y}.


(* Notation Dom := (pfdom _).
Notation Part := (pfpfun _).
Implicit Arguments pfpfun [S]. *)

(*
The next lemma states that every partial function is well defined.
*)

lemma pfwdef : \forall S:CSetoid. \forall F : PartFunct S. \forall x, y, Hx, Hy.
   x = y \to (pfpfun S F x Hx ) = (pfpfun S F y Hy).
intros.
apply not_ap_imp_eq;unfold. intro H0.
generalize in match (pfstrx ? ? ? ? ? ? H0).
exact (eq_imp_not_ap ? ? ? H).
qed. 

(*
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

(* Hint Resolve CI: core. *)

(* Section CSetoid_Ops.*)

(*Variable S : CSetoid.*)

(*
To begin with, we want to be able to ``see'' each total function as a partial function.
*)

definition total_eq_part :\forall S:CSetoid. CSetoid_un_op S \to PartFunct S.
intros (S f).
apply (mk_PartFunct ? 
          (\lambda x : S. True) 
          ?
              (\lambda (x : S). \lambda (H : True).(csf_fun ? ? f x))).
unfold. intros;left.
intros (x y Hx Hy H).
exact (csf_strext_unfolded ? ? f ? ? H).
qed.
(*Section Part_Function_Const.*)

(*
In any setoid we can also define constant functions (one for each element of the setoid) and an identity function:

%\begin{convention}% Let [c:S].
%\end{convention}%
*)

(*Variable c : S.*)

definition Fconst: \forall S:CSetoid. \forall c: S. ? \def
  \lambda S:CSetoid. \lambda c: S.
 total_eq_part ? (Const_CSetoid_fun ? ? c).

(* End Part_Function_Const. *)

(* Section Part_Function_Id. *)

definition Fid : \forall S:CSetoid. ? \def 
  \lambda S:CSetoid.total_eq_part ? (id_un_op S).
  
(* End Part_Function_Id. *)

(*
(These happen to be always total functions, but that is more or less obvious, 
as we have no information on the setoid; however, we will be able to define 
partial functions just applying other operators to these ones.)

If we have two setoid functions [F] and [G] we can always compose them.  
The domain of our new function will be the set of points [s] in the domain of [F] 
for which [F(s)] is in the domain of [G]#. 

#%\footnote{%Notice that the use of extension here is essential.%}.%  
The inversion in the order of the variables is done to maintain uniformity 
with the usual mathematical notation.

%\begin{convention}% 
Let [G,F:(PartFunct S)] and denote by [Q] and [P], respectively, the predicates characterizing 
their domains.
%\end{convention}%
*)

(* Section Part_Function_Composition. *)

(* Variables G F : PartFunct S. *)

(* begin hide *)

definition UP : \forall S:CSetoid. \forall F: PartFunct S. ? \def
   \lambda S:CSetoid. \lambda F: PartFunct S. 
   pfdom ? F.
(* Let P := Dom F. *)
definition UQ : \forall S:CSetoid. \forall G : PartFunct S. ? \def
   \lambda S:CSetoid. \lambda G: PartFunct S. 
   pfdom ? G.
(* Let Q := Dom G. *)
definition UR : \forall S:CSetoid.  \forall F,G: PartFunct S. \forall x: S. ? \def 
  \lambda S:CSetoid. \lambda F,G: PartFunct S. \lambda x: S.  
  (sigT ? (\lambda Hx : UP S F x. UQ S G (pfpfun S F x Hx))).
(*Let R x := {Hx : P x | Q (F x Hx)}.*)

(* end hide *)

(* TODO ProjT1 *)
lemma part_function_comp_strext : \forall S:CSetoid.  \forall F,G: PartFunct S. 
\forall x,y:S. \forall Hx : UR S F G x. \forall Hy : (UR S F G y).
 (pfpfun ? G (pfpfun ? F x (proj1_sigT ? ? Hx)) (proj2_sigTm ? ? Hx)) 
  \neq (pfpfun ? G (pfpfun ? F y (proj1_sigT ? ? Hy)) (proj2_sigTm ? ? Hy)) \to x \neq y.
intros (S F G x y Hx Hy H).
exact (pfstrx ? ? ? ? ? ? (pfstrx ? ? ? ? ? ? H)).
qed.
(*
definition TempR : \forall S:CSetoid.  \forall F,G: PartFunct S. \forall x: S. ? \def 
  \lambda S:CSetoid. \lambda F,G: PartFunct S. \lambda x: S.  
  (ex  ? (\lambda Hx : UP S F x. UQ S G (pfpfun S F x Hx))). *)
  
lemma part_function_comp_dom_wd :\forall S:CSetoid. \forall F,G: PartFunct S. 
 pred_wd S (UR S F G).
  intros.unfold.
  intros (x y H H0).
  unfold UR.
  elim H.
  unfold in a.
  unfold UP.unfold UQ.
  apply (existT).
  apply (dom_wd S F x y a H0).
apply (dom_wd S G (pfpfun S F x a)).
assumption.
apply pfwdef; assumption.
qed.

definition Fcomp : \forall S:CSetoid. \forall F,G : PartFunct S. ? \def 
\lambda S:CSetoid. \lambda F,G : PartFunct S. 
mk_PartFunct ? (UR S F G) (part_function_comp_dom_wd S F G)  
(\lambda x. \lambda Hx : UR S F G x. (pfpfun S G (pfpfun S F x (proj1_sigT ? ? Hx)) (proj2_sigTm ? ?  Hx)))
(part_function_comp_strext S F G).

(*End Part_Function_Composition.*)

(*End CSetoid_Ops.*)

(*
%\begin{convention}% Let [F:(BinPartFunct S1 S2)] and [G:(PartFunct S2 S3)], and denote by [Q] and [P], respectively, the predicates characterizing their domains.
%\end{convention}%
*)

(* Section BinPart_Function_Composition.*)

(*Variables S1 S2 S3 : CSetoid.

Variable G : BinPartFunct S2 S3.
Variable F : BinPartFunct S1 S2.
*)
(* begin hide *)
(* Let P := BDom F.
Let Q := BDom G.*)
(* end hide *)
(*Let R x := {Hx : P x | Q (F x Hx)}.*)

definition BP : \forall S1,S2:CSetoid. \forall F: BinPartFunct S1 S2. ? \def
   \lambda S1,S2:CSetoid. \lambda F: BinPartFunct S1 S2. 
   bpfdom ? ? F.
(* Let P := Dom F. *)
definition BQ : \forall S2,S3:CSetoid. \forall G: BinPartFunct S2 S3. ? \def
   \lambda S2,S3:CSetoid. \lambda G: BinPartFunct S2 S3. 
   bpfdom ? ? G.
(* Let Q := BDom G.*)
definition BR : \forall S1,S2,S3:CSetoid.  \forall F: BinPartFunct S1 S2.
\forall G: BinPartFunct S2 S3.
  \forall x: ?. ? \def 
  \lambda S1,S2,S3:CSetoid. \lambda F: BinPartFunct S1 S2.  
  \lambda G: BinPartFunct S2 S3.  \lambda x: ?.  
  (sigT  ? (\lambda Hx : BP S1 S2 F x. BQ S2 S3  G (bpfpfun S1 S2 F x Hx))).
(*Let R x := {Hx : P x | Q (F x Hx)}.*)

lemma bin_part_function_comp_strext : \forall S1,S2,S3:CSetoid. \forall F: BinPartFunct S1 S2.
\forall G: BinPartFunct S2 S3. \forall x,y. \forall Hx : BR S1 S2 S3 F G x. 
\forall Hy : (BR S1 S2 S3 F G y). 
(bpfpfun ? ? G (bpfpfun ? ? F x (proj1_sigT ? ? Hx)) (proj2_sigTm ? ? Hx)) \neq 
(bpfpfun ? ? G (bpfpfun ? ? F y (proj1_sigT ? ? Hy)) (proj2_sigTm ? ? Hy)) \to x \neq y.
intros (S1 S2 S3 x y Hx Hy H).
exact (bpfstrx ? ? ? ? ? ? ? (bpfstrx ? ? ? ? ? ? ? H1)).
qed.  

lemma bin_part_function_comp_dom_wd : \forall S1,S2,S3:CSetoid. 
  \forall F: BinPartFunct S1 S2. \forall G: BinPartFunct S2 S3.
 pred_wd ? (BR S1 S2 S3 F G).
intros.
unfold.intros (x y H H0).
unfold BR; elim H 0.intros (x0).
apply (existT ? ? (bdom_wd ? ? F x y x0 H0)).
apply (bdom_wd ? ? G (bpfpfun ? ? F x x0)).
assumption.
apply bpfwdef; assumption.
qed.

definition BinFcomp : \forall S1,S2,S3:CSetoid. \forall F: BinPartFunct S1 S2. 
  \forall G: BinPartFunct S2 S3. ?
\def 
\lambda S1,S2,S3:CSetoid. \lambda F: BinPartFunct S1 S2. \lambda G: BinPartFunct S2 S3.
mk_BinPartFunct ? ? (BR S1 S2 S3 F G) (bin_part_function_comp_dom_wd S1 S2 S3 F G)
  (\lambda x. \lambda Hx : BR S1 S2 S3 F G x.(bpfpfun ? ? G (bpfpfun ? ? F x (proj1_sigT ? ? Hx)) (proj2_sigTm ? ? Hx)))
  (bin_part_function_comp_strext S1 S2 S3 F G).
(*End BinPart_Function_Composition.*)
(* Different tokens for compatibility with coqdoc *)

(*
Implicit Arguments Fconst [S].
Notation "[-C-] x" := (Fconst x) (at level 2, right associativity).

Notation FId := (Fid _).

Implicit Arguments Fcomp [S].
Infix "[o]" := Fcomp (at level 65, no associativity).

Hint Resolve pfwdef bpfwdef: algebra.
*)
(*Section bijections.*)
(*Bijections *)


definition injective : \forall  A, B :CSetoid. \forall f : CSetoid_fun A B.
 ? \def 
  \lambda  A, B :CSetoid. \lambda f : CSetoid_fun A B.
  (\forall a0: A.\forall a1 : A. a0 \neq a1 \to 
                    (csf_fun A B f a0) \neq (csf_fun A B f a1)).
  
definition injective_weak: \forall  A, B :CSetoid. \forall f : CSetoid_fun A B.
 ? \def 
 \lambda  A, B :CSetoid. \lambda f : CSetoid_fun A B.
 (\forall a0, a1 : A.
 (csf_fun ? ? f a0) = (csf_fun ? ? f a1) -> a0 = a1).

definition surjective : \forall  A, B :CSetoid. \forall f : CSetoid_fun A B.
  ? \def 
  \lambda  A, B :CSetoid. \lambda f : CSetoid_fun A B.
  (\forall b : B. (\exists a : A. (csf_fun ? ? f a) = b)).

(* Implicit Arguments injective [A B].
   Implicit Arguments injective_weak [A B].
   Implicit Arguments surjective [A B]. *)

lemma injective_imp_injective_weak: \forall A, B :CSetoid. \forall f : CSetoid_fun A B.
 injective A B f \to injective_weak A B f.
intros 3 (A B f).
unfold injective.
intro H.
unfold injective_weak.
intros 3 (a0 a1 H0).
apply not_ap_imp_eq.
unfold.
intro H1.
letin H2 \def (H a0 a1 H1).
letin H3 \def (ap_imp_neq B (csf_fun ? ? f a0) (csf_fun ? ? f a1) H2).
letin H4 \def (eq_imp_not_neq B (csf_fun ? ? f a0) (csf_fun ? ? f a1) H0).
apply H4.
exact H3.
qed.

definition bijective : \forall A, B :CSetoid. \forall f : CSetoid_fun A B. 
? \def \lambda A, B :CSetoid. \lambda f : CSetoid_fun A B.
injective A B f \and surjective A B f.


(* Implicit Arguments bijective [A B]. *)

lemma id_is_bij : \forall A:CSetoid. bijective ? ? (id_un_op A).
intro A.
split [unfold. simplify; intros. exact H|
unfold.intro. apply (ex_intro  ).exact b. apply eq_reflexive]
qed.

lemma comp_resp_bij :\forall A,B,C,f,g.
 bijective ? ? f \to bijective ? ? g \to bijective ? ? (compose_CSetoid_fun A B C f g).
intros 5 (A B C f g).
intros 2 (H0 H1).
elim H0 0; clear H0;intros 2 (H00 H01).
elim H1 0; clear H1; intros 2 (H10 H11).
split[unfold. intros 2 (a0 a1); simplify; intro.
unfold compose_CSetoid_fun.simplify.
 apply H10; apply H00;exact H|unfold.
 intro c; unfold compose_CSetoid_fun.simplify.
elim (H11 c) 0;intros (b H20).
elim (H01 b) 0.intros (a H30).
apply ex_intro.apply a.
apply (eq_transitive_unfolded ? ? (csf_fun B C g b)).
apply csf_wd_unfolded.assumption.assumption]
qed.

(* Implicit Arguments invfun [A B]. *)

record CSetoid_bijective_fun (A,B:CSetoid): Type \def
{ direct :2> CSetoid_fun A B;
  inverse: CSetoid_fun B A;
  inv1: \forall x:A.(csf_fun ? ? inverse (csf_fun ? ? direct x)) = x;
  inv2: \forall x:B.(csf_fun ? ? direct (csf_fun ? ? inverse x)) = x
  }. 
   
lemma invfun : \forall A,B:CSetoid. \forall f:CSetoid_bijective_fun A B. 
  B \to A.
 intros (A B f ).
 elim (inverse A B f).apply f1.apply c.
qed.

lemma inv_strext : \forall A,B. \forall f : CSetoid_bijective_fun A B.
 fun_strext B A (invfun A B f).
intros.unfold invfun.
elim (inverse A B f).simplify.intros.
unfold in H.apply H.assumption.
qed.



definition Inv: \forall  A, B:CSetoid. 
\forall f:CSetoid_bijective_fun A B. \forall H : (bijective ? ? (direct ? ? f)). ? \def 
\lambda  A, B:CSetoid. \lambda f:CSetoid_bijective_fun A B. \lambda H : (bijective ? ? (direct ? ? f)).
  mk_CSetoid_fun B A (invfun ? ? f) (inv_strext ? ?  f).

lemma eq_to_ap_to_ap: \forall A:CSetoid.\forall a,b,c:A.
a = b \to b \neq c \to a \neq c.
intros.
generalize in match (ap_cotransitive_unfolded ? ? ? H1 a).
intro.elim H2.apply False_ind.apply (eq_imp_not_ap ? ? ? H).
apply ap_symmetric_unfolded. assumption.
assumption.
qed.

lemma Dir_bij : \forall A, B:CSetoid. 
 \forall f : CSetoid_bijective_fun A B.
  bijective ? ? (direct ? ? f).
  intros.unfold bijective.split
  [unfold injective.intros.
  apply (csf_strext_unfolded ? ? (inverse ? ? f)).
  elim f.
  apply (eq_to_ap_to_ap ? ? ? ? (H1 ?)).
  apply ap_symmetric_unfolded.
  apply (eq_to_ap_to_ap ? ? ? ? (H1 ?)).
  apply ap_symmetric_unfolded.assumption
  |unfold surjective.intros.
   elim f.autobatch.
  ]
qed.
   
lemma Inv_bij : \forall A, B:CSetoid. 
 \forall f : CSetoid_bijective_fun A B.
  bijective ? ?  (inverse A B f).
 intros;
 elim f 2;
 elim c 0;
 elim c1 0;
 simplify;
 intros;
 split;
  [ intros;
    apply H1;
    apply (eq_to_ap_to_ap ? ? ? ? (H3 ?)).
  apply ap_symmetric_unfolded.
  apply (eq_to_ap_to_ap ? ? ? ? (H3 ?)).
  apply ap_symmetric_unfolded.assumption|
  intros.autobatch]
qed.

(* End bijections.*)

(* Implicit Arguments bijective [A B].
Implicit Arguments injective [A B].
Implicit Arguments injective_weak [A B].
Implicit Arguments surjective [A B].
Implicit Arguments inv [A B].
Implicit Arguments invfun [A B].
Implicit Arguments Inv [A B].

Implicit Arguments conj_wd [S P Q].
*)

(* Notation Prj1 := (prj1 _ _ _ _).
   Notation Prj2 := (prj2 _ _ _ _). *)

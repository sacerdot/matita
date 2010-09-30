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

(* $Id: CSemiGroups.v,v 1.10 2004/09/24 15:30:34 loeb Exp $ *)
(* printing [+] %\ensuremath+% #+# *)
(* printing {+} %\ensuremath+% #+# *)

(* Require Export CSetoidInc. *)

(* Begin_SpecReals *)

set "baseuri" "cic:/matita/algebra/CoRN/CSemiGroups".
include "algebra/CoRN/SetoidInc.ma".

(*------------------------------------------------------------------*)
(* Semigroups - Definition of the notion of Constructive Semigroup  *)
(*------------------------------------------------------------------*)

definition is_CSemiGroup : \forall A : CSetoid. \forall op: CSetoid_bin_op A. Prop \def 
\lambda A : CSetoid. \lambda op: CSetoid_bin_op A. CSassociative A (csbf_fun A A A op).

record CSemiGroup : Type \def 
  {csg_crr   :> CSetoid;
   csg_op    :  CSetoid_bin_op csg_crr;
   csg_proof :  is_CSemiGroup csg_crr csg_op}.

(*
Implicit Arguments csg_op [c].
Infix "[+]" := csg_op (at level 50, left associativity).
End_SpecReals *)



(*--------------------------------------------------------------*) 
(*  Semigroup axioms - The axiomatic properties of a semi group *)
(*--------------------------------------------------------------*)
(* Variable G : CSemiGroup. *)

lemma CSemiGroup_is_CSemiGroup : \forall G : CSemiGroup. is_CSemiGroup (csg_crr G) (csg_op G).
intro.
elim G. simplify. exact H.
qed.
(* CoRN 
Lemma CSemiGroup_is_CSemiGroup : is_CSemiGroup G csg_op.*)

lemma plus_assoc : \forall G : CSemiGroup. 
CSassociative G (csbf_fun G G G (csg_op G)).
exact CSemiGroup_is_CSemiGroup.
qed.

(*--------------------------------------------------------------*) 
(*                          Semigroup basics                    *)
(*--------------------------------------------------------------*)

lemma plus_assoc_unfolded : \forall G : CSemiGroup. \forall x,y,z : ?.
 (csbf_fun G G G (csg_op G) x (csbf_fun G G G (csg_op G) y z)) = 
    (csbf_fun G G G (csg_op G) (csbf_fun G G G  (csg_op G) x y) z).
  intros.
  apply plus_assoc.
qed.

(* Section p71R1. *)

(* Morphism
%\begin{convention}%
Let [S1 S2:CSemiGroup].
%\end{convention}%
*)

(* Variable S1:CSemiGroup.
Variable S2:CSemiGroup. *)

definition morphism_of_CSemiGroups: \forall S1,S2: CSemiGroup. \forall f: CSetoid_fun S1 S2. 
  Prop \def
  \lambda S1,S2: CSemiGroup. \lambda f: CSetoid_fun S1 S2. 
  (\forall a,b:S1. (csf_fun S1 S2 f (csbf_fun ? ? ? (csg_op ?) a b)) =
    (csbf_fun ? ? ? (csg_op ?) (csf_fun S1 S2 f a) (csf_fun S1 S2  f b))).

(* End p71R1. *)

(* About the unit *)

(* Zero ?????  *)

definition is_rht_unit: \forall S: CSemiGroup. \forall op : CSetoid_bin_op S. \forall  Zero: ?. Prop  
  \def 
  \lambda S: CSemiGroup. \lambda op : CSetoid_bin_op S. \lambda  Zero: ?.
  \forall x:?. (csbf_fun ? ? ? op x Zero) = x.

(* Definition is_rht_unit S (op : CSetoid_bin_op S) Zero : Prop := forall x, op x Zero [=] x. *)

(* End_SpecReals *)

definition is_lft_unit: \forall S: CSemiGroup. \forall op : CSetoid_bin_op S. \forall  Zero: ?. Prop 
  \def 
  \lambda S: CSemiGroup. \lambda op : CSetoid_bin_op S. \lambda  Zero: ?.
   \forall x:?. (csbf_fun ? ? ? op Zero x) = x.


(* Implicit Arguments is_lft_unit [S]. *)

(* Begin_SpecReals *)

(* Implicit Arguments is_rht_unit [S]. *)

(* An alternative definition:
*)

definition is_unit: \forall S:CSemiGroup.  S \to Prop \def
\lambda S:CSemiGroup.
\lambda e. (\forall (a:S). (csbf_fun ? ? ? (csg_op ?) e a) = a \and (csbf_fun ? ? ? (csg_op ?) a e) 
 = a).

lemma cs_unique_unit : \forall S:CSemiGroup. \forall e,f:S. 
(is_unit S e) \and (is_unit S f) \to e = f.
intros 3 (S e f).
unfold is_unit.
intro H.
elim H 0.
clear H.
intros (H0 H1).
elim (H0 f) 0.
clear H0.
intros (H2 H3).
elim (H1 e) 0.
clear H1.
intros (H4 H5).
autobatch.
qed.
(*
astepr (e[+]f). 
astepl (e[+]f).
apply eq_reflexive.
Qed.
*)

(* End_SpecReals *)

(* Hint Resolve plus_assoc_unfolded: algebra. *)

(* Functional operations
We can also define a similar addition operator, which will be denoted by [{+}], on partial functions.

%\begin{convention}% Whenever possible, we will denote the functional construction corresponding to an algebraic operation by the same symbol enclosed in curly braces.
%\end{convention}%

At this stage, we will always consider autobatchmorphisms; we %{\em %could%}% treat this in a more general setting, but we feel that it wouldn't really be a useful effort.

%\begin{convention}% Let [G:CSemiGroup] and [F,F':(PartFunct G)] and denote by [P] and [Q], respectively, the predicates characterizing their domains.
%\end{convention}%
*)

(* Section Part_Function_Plus. *)

(* Variable G : CSemiGroup.
Variables F F' : PartFunct G. *)

(* begin hide *)
(*Let P := Dom F.
Let Q := Dom F'.*)
(* end hide *)
definition NP : \forall G:CSemiGroup. \forall F,F': PartFunct G. ? \def
   \lambda G:CSemiGroup. \lambda F,F': PartFunct G.
   pfdom ? F.
definition NQ : \forall G:CSemiGroup. \forall F,F': PartFunct G. ? \def
   \lambda G:CSemiGroup. \lambda F,F': PartFunct G.
   pfdom ? F'.
   
lemma part_function_plus_strext :  \forall G:CSemiGroup. \forall F,F': PartFunct G. 
\forall x, y:G. \forall Hx : conjP G (pfdom G F) (pfdom G F') x. 
\forall Hy : conjP G (pfdom G F) (pfdom G F') y.
(csbf_fun ? ? ? (csg_op G) (pfpfun ? F x (prj1 G (pfdom G F) (pfdom G F') x Hx)) 
  (pfpfun ? F' x (prj2 G (pfdom G F) (pfdom G F') x Hx))) 
  \neq (csbf_fun ? ? ? (csg_op G) (pfpfun ? F y (prj1 G (pfdom G F) (pfdom G F') y Hy)) 
    (pfpfun ? F' y (prj2 G (pfdom G F) (pfdom G F') y Hy))) 
  \to x \neq y.
intros (G F F' x y Hx Hy H).
elim (bin_op_strext_unfolded ? ? ? ? ? ? H)[
apply pfstrx[apply F|elim Hx.apply a|elim Hy.apply a|exact H1]|
apply pfstrx[apply F'|elim Hx.apply b|elim Hy.apply b|exact H1]]
qed.

definition Fplus : \forall G:CSemiGroup. \forall F,F': PartFunct G. ? \def 
  \lambda G:CSemiGroup. \lambda F,F': PartFunct G.
mk_PartFunct G ? (conj_wd ? ? ? (dom_wd ? F) (dom_wd ? F'))
  (\lambda x,Hx. (csbf_fun ? ? ? (csg_op ?) 
            (pfpfun ? F x (prj1 ? ? ? ? Hx))  (pfpfun ? F' x (prj2 ? ? ? ? Hx)))) 
  (part_function_plus_strext G F F').

(*
%\begin{convention}% Let [R:G->CProp].
%\end{convention}%
*)

(* Variable R : G -> CProp. *)

lemma included_FPlus :  \forall G:CSemiGroup.  \forall R : G \to Type. \forall F,F': PartFunct G. 
included ? R (NP G F F' ) -> included ? R (NQ G F F') \to included ? R (pfdom ? (Fplus G F F')).
intros; unfold Fplus;simplify. apply included_conj; assumption.
qed.

lemma included_FPlus' : \forall G:CSemiGroup.  \forall R : G \to Type. \forall F,F': PartFunct G. 
  included ? R (pfdom ? (Fplus G F F')) \to included ? R (NP G F F').
intros. unfold Fplus in i. simplify in i; unfold NP.
  apply (included_conj_lft ? ? ? ? i); apply H.
qed.

lemma included_FPlus'' : \forall G:CSemiGroup.  \forall R : G \to Type. \forall F,F': PartFunct G.
   included ? R (pfdom ? (Fplus G F F')) -> included ? R (NQ G F F').
intros (G R F F'H); unfold Fplus in H. simplify in H;
unfold NQ. apply (included_conj_rht ? (pfdom G F)); apply H.
qed.

(* End Part_Function_Plus. *)

(* Implicit Arguments Fplus [G].
Infix "{+}" := Fplus (at level 50, left associativity).

Hint Resolve included_FPlus : included.

Hint Immediate included_FPlus' included_FPlus'' : included.
*) 

(* Subsemigroups
%\begin{convention}%
Let [csg] a semi-group and [P] a non-empty
predicate on the semi-group which is preserved by [[+]].
%\end{convention}%
*)

(* Section SubCSemiGroups. *)

(* Variable csg : CSemiGroup.
   Variable P : csg -> CProp.
   Variable op_pres_P : bin_op_pres_pred _ P csg_op. *) 

definition subcrr : \forall csg: CSemiGroup. \forall P : csg -> Prop. CSetoid \def 
  \lambda csg: CSemiGroup. \lambda P : csg -> Prop.
  mk_SubCSetoid ? P.
definition mk_SubCSemiGroup :\forall csg: CSemiGroup. \forall P : csg -> Prop.
    \forall op_pres_P : bin_op_pres_pred csg P (csg_op csg). CSemiGroup \def
  \lambda csg: CSemiGroup. \lambda P : csg -> Prop. 
    \lambda op_pres_P : bin_op_pres_pred csg P (csg_op csg).
   mk_CSemiGroup (subcrr csg P) (mk_SubCSetoid_bin_op ? ? ? op_pres_P )
 (restr_f_assoc csg P ? op_pres_P  (plus_assoc csg)).
(* Section D9S. *)

(* Direct Product
%\begin{convention}%
Let [M1 M2:CSemiGroup]
%\end{convention}%
*)

(* Variable M1 M2: CSemiGroup. *)

definition dprod: \forall M1,M2:CSemiGroup. \forall x:ProdCSetoid (csg_crr M1) (csg_crr M2).
  \forall y:ProdCSetoid (csg_crr M1) (csg_crr M2). (ProdCSetoid (csg_crr M1) (csg_crr M2)) \def
  \lambda M1,M2:CSemiGroup. \lambda x:ProdCSetoid (csg_crr M1) (csg_crr M2).
  \lambda y:ProdCSetoid (csg_crr M1) (csg_crr M2).
  match x with 
    [pair (x1: (cs_crr (csg_crr M1))) (x2: (cs_crr (csg_crr M2))) \Rightarrow 
     match y with 
       [pair (y1: (cs_crr (csg_crr M1))) (y2: (cs_crr (csg_crr M2))) \Rightarrow 
          pair (cs_crr (csg_crr M1)) (cs_crr (csg_crr M2))
(csbf_fun ? ? ? (csg_op M1) x1 y1) (csbf_fun ? ? ? (csg_op M2) x2 y2)]].

lemma dprod_strext: \forall M1,M2:CSemiGroup.
(bin_fun_strext (ProdCSetoid M1 M2)(ProdCSetoid M1 M2)
  (ProdCSetoid M1 M2) (dprod M1 M2)).
unfold bin_fun_strext.
intros 6 (M1 M2 x1 x2 y1 y2).
unfold dprod.
elim x1 0.
intros 2 (a1 a2).
elim x2 0.
intros 2 (b1 b2).
elim y1 0.
intros 2 (c1 c2).
elim y2 0.
intros 2 (d1 d2).
simplify.
intro H.
elim H 0[simplify.
clear H.
intro H.
cut (a1 \neq b1 \lor c1 \neq d1).
elim Hcut[left.left.assumption|right.left.assumption]
|intros.simplify in H1.
clear H.
cut (a2 \neq b2 \lor c2 \neq d2).
elim Hcut [left.right.assumption|right.right.assumption]
][
letin H0 \def (csg_op M1).
unfold csg_op in H0.
unfold CSetoid_bin_op in H0.
letin H1 \def (csbf_strext M1 M1 M1 H0).
unfold csbf_strext in H1.
unfold bin_fun_strext in H1.
apply H1.
exact H|
letin H0 \def (csg_op M2).
unfold csg_op in H0.
unfold CSetoid_bin_op in H0.
letin H2 \def (csbf_strext M2 M2 M2 H0).
unfold csbf_strext in H2.
unfold bin_fun_strext in H2.
apply H2.
exact H1]
qed.

definition dprod_as_csb_fun: \forall M1,M2:CSemiGroup. 
  CSetoid_bin_fun (ProdCSetoid M1 M2) (ProdCSetoid M1 M2)(ProdCSetoid M1 M2)\def
  \lambda M1,M2:CSemiGroup.
  mk_CSetoid_bin_fun (ProdCSetoid M1 M2)(ProdCSetoid M1 M2)
  (ProdCSetoid M1 M2) (dprod M1 M2) (dprod_strext M1 M2).

lemma direct_product_is_CSemiGroup: \forall M1,M2:CSemiGroup. 
  (is_CSemiGroup (ProdCSetoid M1 M2) (dprod_as_csb_fun M1 M2)).
  intros.
unfold is_CSemiGroup.
unfold CSassociative.
intros (x y z).
elim x 0.
intros (x1 x2).
elim y 0.
intros (y1 y2).
elim z 0.
intros (z1 z2).
split[unfold dprod_as_csb_fun. simplify.apply CSemiGroup_is_CSemiGroup|
      unfold dprod_as_csb_fun. simplify.apply CSemiGroup_is_CSemiGroup].
qed.

definition direct_product_as_CSemiGroup : \forall M1,M2:CSemiGroup. ? \def
  \lambda M1,M2: CSemiGroup.
  mk_CSemiGroup (ProdCSetoid M1 M2) (dprod_as_csb_fun M1 M2) 
  (direct_product_is_CSemiGroup M1 M2).

(* End D9S. *)

(* The SemiGroup of Setoid functions *)

lemma FS_is_CSemiGroup:\forall X:CSetoid.
  is_CSemiGroup (FS_as_CSetoid X X) (comp_as_bin_op  X ).
  intro.
unfold is_CSemiGroup.
apply assoc_comp.
qed.

definition FS_as_CSemiGroup : \forall A : CSetoid. ? \def \lambda A:CSetoid.
  mk_CSemiGroup (FS_as_CSetoid A A) (comp_as_bin_op A) (assoc_comp A).

(* Section p66E2b4. *)

(* The Free SemiGroup
%\begin{convention}% Let [A:CSetoid].
%\end{convention}%
*)

(* Variable A:CSetoid. *)

lemma Astar_is_CSemiGroup: \forall A:CSetoid. 
  (is_CSemiGroup (free_csetoid_as_csetoid A) (app_as_csb_fun A)).
  intro.
unfold is_CSemiGroup.
unfold CSassociative.
intro x.
unfold app_as_csb_fun.
simplify.
elim x 0.
simplify.
intros (x y).
elim x.
simplify.
apply eq_reflexive_unfolded.
simplify. left. apply eq_reflexive_unfolded.assumption.

simplify.
intros.unfold appA in H.
generalize in match (H y z).intros.unfold appA in H1.left. 
apply eq_reflexive_unfolded.
assumption.
qed.

definition Astar_as_CSemiGroup: \forall A:CSetoid. ? \def
  \lambda A:CSetoid. 
  mk_CSemiGroup (free_csetoid_as_csetoid A) (app_as_csb_fun A) 
   (Astar_is_CSemiGroup A).

(* End p66E2b4. *)

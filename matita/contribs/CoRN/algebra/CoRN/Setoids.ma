(**************************************************************************)
(*       ___	                                                            *)
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

set "baseuri" "cic:/matita/algebra/CoRN/Setoid".


include "higher_order_defs/relations.ma".
include "Z/plus.ma".

include "datatypes/constructors.ma".
include "nat/nat.ma".
include "logic/equality.ma".
(*include "Z/Zminus.ma".*)

(* Setoids
Definition of a constructive setoid with apartness,
i.e. a set with an equivalence relation and an apartness relation compatible with it.
*)

(* Definition of Setoid
Apartness, being the main relation, needs to be [CProp]-valued.  Equality,
as it is characterized by a negative statement, lives in [Prop]. 

N.B. for the moment we use Prop for both (Matita group)
*)

record is_CSetoid (A : Type) (eq : relation A) (ap : relation A) : Prop \def
  {ax_ap_irreflexive  : irreflexive A ap;
   ax_ap_symmetric    : symmetric A ap;
   ax_ap_cotransitive : cotransitive A ap;
   ax_ap_tight        : tight_apart A eq ap}.

record CSetoid : Type \def
  {cs_crr   :> Type;
   cs_eq    :  relation cs_crr;
   cs_ap    :  relation cs_crr;
   cs_proof :  is_CSetoid cs_crr cs_eq cs_ap}.   

interpretation "setoid equality" 'eq x y = (cs_eq ? x y).

interpretation "setoid apart" 'neq x y = (cs_ap ? x y).

(* visto che sia "ap" che "eq" vanno in Prop e data la "tight-apartness", 
"cs_neq" e "ap" non sono la stessa cosa? *)
definition cs_neq : \forall S : CSetoid. relation S \def
 \lambda S : CSetoid. \lambda x,y : S. \not x = y.

lemma CSetoid_is_CSetoid : 
 \forall S : CSetoid. is_CSetoid S (cs_eq S) (cs_ap S).
intro. apply (cs_proof S).
qed.

lemma ap_irreflexive: \forall S : CSetoid. irreflexive S (cs_ap S).
intro. elim (CSetoid_is_CSetoid S). assumption.
qed.

lemma ap_symmetric : \forall S : CSetoid. symmetric S(cs_ap S).
intro. elim (CSetoid_is_CSetoid S). assumption. 
qed.

lemma ap_cotransitive : \forall S : CSetoid. cotransitive S (cs_ap S).
intro. elim (CSetoid_is_CSetoid S). assumption.
qed.

lemma ap_tight : \forall S : CSetoid. tight_apart S (cs_eq S) (cs_ap S).
intro. elim (CSetoid_is_CSetoid S). assumption.
qed.

definition ex_unq : \forall S : CSetoid. (S \to Prop) \to Prop \def
 \lambda S : CSetoid. \lambda P : S \to Prop. 
  ex2 S (\lambda x. \forall y : S. P y \to x = y) P.


lemma eq_reflexive : \forall S : CSetoid. reflexive S (cs_eq S).
intro. unfold. intro.
generalize in match (ap_tight S x x).
intro.
generalize in match (ap_irreflexive S x); 
elim H. apply H1. assumption.
qed.

axiom eq_symmetric : \forall S : CSetoid. symmetric S (cs_eq S).
(*
lemma eq_symmetric : \forall S : CSetoid. symmetric S (cs_eq S).
intro. unfold. intros.
generalize in match (ap_tight S x y). intro.
generalize in match (ap_tight S y x). intro.
generalize in match (ap_symmetric S y x). intro.
elim H1. clear H1.
elim H2. clear H2.
apply H1. unfold. intro. autobatch.
qed.
*)
lemma eq_transitive : \forall S : CSetoid. transitive S (cs_eq S).
intro. unfold. intros (x y z H H0).
generalize in match (ap_tight S x y). intro.
generalize in match (ap_tight S y z). intro.
generalize in match (ap_tight S x z). intro.
elim H3.
apply H4. unfold. intro.
generalize in match (ap_cotransitive ? ? ? H6 y). intro H7.
elim H1 (H1' H1''). clear H1.
elim H2 (H2' H2''). clear H2.
elim H3 (H3' H3''). clear H3. 
elim H7 (H1). clear H7. 
generalize in match H1. apply H1''. assumption. (*non ho capito il secondo passo*)
generalize in match H1. apply H2''. assumption.
qed.

lemma eq_reflexive_unfolded : \forall S:CSetoid. \forall x:S. x = x.
apply eq_reflexive.
qed.

lemma eq_symmetric_unfolded : \forall S:CSetoid. \forall x,y:S. x = y \to y = x.
apply eq_symmetric.
qed.

lemma eq_transitive_unfolded : \forall S:CSetoid. \forall x,y,z:S. x = y \to y = z \to x = z.
apply eq_transitive.
qed.


lemma eq_wdl : \forall S:CSetoid. \forall x,y,z:S. x = y \to x = z \to z = y.
intros.
(* perche' autobatch non arriva in fondo ??? *)
apply (eq_transitive_unfolded ? ? x).
apply eq_symmetric_unfolded.
exact H1.
exact H.
qed.


lemma ap_irreflexive_unfolded : \forall S:CSetoid. \forall x:S. \not (x \neq x).
apply ap_irreflexive.
qed.

lemma ap_cotransitive_unfolded : \forall S:CSetoid. \forall a,b:S. a \neq b \to 
 \forall c:S. a \neq c \or c \neq b.
apply ap_cotransitive.
qed.

lemma ap_symmetric_unfolded : \forall S:CSetoid. \forall x,y:S.
 x \neq y \to y \neq x.
apply ap_symmetric.
qed.

lemma eq_imp_not_ap : \forall S:CSetoid. \forall x,y:S. 
 x = y \to \not (x \neq y).
intros.
elim (ap_tight S x y).
apply H2. assumption.
qed.

lemma not_ap_imp_eq : \forall S:CSetoid. \forall x,y:S. 
 \not (x \neq y) \to x = y.
intros.
elim (ap_tight S x y).
apply H1. assumption.
qed.

lemma neq_imp_notnot_ap : \forall S:CSetoid. \forall x,y:S.
 (cs_neq S x y) \to \not \not (x \neq y).
intros. unfold. intro.
apply H.
apply not_ap_imp_eq.
assumption.
qed.

lemma notnot_ap_imp_neq: \forall S:CSetoid. \forall x,y:S. 
 (\not \not (x \neq y)) \to (cs_neq S x y).
intros. unfold. unfold. intro.
apply H.
apply eq_imp_not_ap.
assumption.
qed.

lemma ap_imp_neq : \forall S:CSetoid. \forall x,y:S. 
 x \neq y \to (cs_neq S x y).
intros. unfold. unfold. intro.
apply (eq_imp_not_ap S ? ? H1).
assumption.
qed.

lemma not_neq_imp_eq : \forall S:CSetoid. \forall x,y:S. 
 \not (cs_neq S x y) \to x = y.
intros.
apply not_ap_imp_eq.
unfold. intro.
apply H.
apply ap_imp_neq.
assumption.
qed.

lemma eq_imp_not_neq : \forall S:CSetoid. \forall x,y:S. 
 x = y \to \not (cs_neq S x y).
intros. unfold. intro.
apply H1.
assumption.
qed.



(* -----------------The product of setoids----------------------- *)

definition prod_ap: \forall A,B : CSetoid.\forall c,d: Prod A B. Prop \def
\lambda A,B : CSetoid.\lambda c,d: Prod A B.
  ((cs_ap A (fst A B c) (fst A B d)) \or 
   (cs_ap B (snd A B c) (snd A B d))).

definition prod_eq: \forall A,B : CSetoid.\forall c,d: Prod A B. Prop \def
\lambda A,B : CSetoid.\lambda c,d: Prod A B.
  ((cs_eq A (fst A B c) (fst A B d)) \and 
   (cs_eq B (snd A B c) (snd A B d))).
      

lemma prodcsetoid_is_CSetoid: \forall A,B: CSetoid.
 is_CSetoid (Prod A B) (prod_eq A B) (prod_ap A B).
intros.
apply (mk_is_CSetoid ? (prod_eq A B) (prod_ap A B))
  [unfold.
   intros.
   elim x.
   unfold.
   unfold prod_ap. simplify.
   intros.
   elim H
   [apply (ap_irreflexive A a H1)
   |apply (ap_irreflexive B b H1)
   ]
 |unfold.
  intros 2.
  elim x 2.
  elim y 2.
  unfold prod_ap. simplify.
  intro.
  elim H
  [left. apply ap_symmetric. assumption.
  |right. apply ap_symmetric. assumption
  ]
 |unfold.
  intros 2.
  elim x 2.
  elim y 4.
  elim z.
  unfold prod_ap in H. simplify in H.
  unfold prod_ap. simplify.
  elim H
  [cut ((a \neq a2) \or (a2 \neq a1))
   [elim Hcut
    [left. left. assumption
    |right. left. assumption
    ]
   |apply (ap_cotransitive A). assumption
   ]
  |cut ((b \neq b2) \or (b2 \neq b1))
   [elim Hcut
    [left. right. assumption
    |right. right. assumption
    ]
  |apply (ap_cotransitive B). assumption.
  ]
 ]
|unfold.
 intros 2.
 elim x 2.
 elim y 2.
 unfold prod_ap. simplify.
 split
 [intro.
  left
  [apply not_ap_imp_eq.
   unfold. intro. apply H.
   left. assumption
  |apply not_ap_imp_eq.
   unfold. intro. apply H.
   right. assumption
  ]
 |intro. unfold. intro.
 elim H.
 elim H1
  [apply (eq_imp_not_ap A a a1 H2). assumption
  |apply (eq_imp_not_ap B b b1 H3). assumption
  ]
 ]
]
qed.


definition ProdCSetoid : \forall A,B: CSetoid. CSetoid \def
 \lambda A,B: CSetoid.
  mk_CSetoid (Prod A B) (prod_eq A B) (prod_ap A B) (prodcsetoid_is_CSetoid A B).



(* Relations and predicates
Here we define the notions of well-definedness and strong extensionality
on predicates and relations.
*)



(*-----------------------------------------------------------------------*)
(*-------------------------- Predicates on Setoids ----------------------*)
(*-----------------------------------------------------------------------*)

(* throughout this section consider (S : CSetoid) and (P : S -> Prop) *)

(* Definition pred_strong_ext : CProp := forall x y : S, P x -> P y or x [#] y. *)
definition pred_strong_ext : \forall S: CSetoid. (S \to Prop) \to Prop \def
 \lambda S: CSetoid. \lambda P: S \to Prop. \forall x,y: S. 
  P x \to (P y \or (x \neq y)).

(* Definition pred_wd : CProp := forall x y : S, P x -> x [=] y -> P y. *)
definition pred_wd : \forall S: CSetoid. \forall P :S \to Type. Type \def
 \lambda S: CSetoid. \lambda P: S \to Type. \forall x,y : S. 
  P x \to x = y \to P y.

record wd_pred (S: CSetoid) : Type \def
  {wdp_pred     :> S \to Prop;
   wdp_well_def :  pred_wd S wdp_pred}.
   
record CSetoid_predicate (S: CSetoid) : Type \def 
 {csp_pred   :> S \to Prop;
  csp_strext :  pred_strong_ext S csp_pred}.

lemma csp_wd : \forall S: CSetoid. \forall P: CSetoid_predicate S. 
   pred_wd S (csp_pred S P).
intros.
elim P.
simplify.unfold pred_wd.
intros.
elim (H x y H1)
 [assumption|apply False_ind.apply (eq_imp_not_ap S x y H2 H3)]
qed.


(* Same result with CProp instead of Prop: but we just work with Prop (Matita group) *)
(*
Definition pred_strong_ext' : CProp := forall x y : S, P x -> P y or x [#] y.
Definition pred_wd' : Prop := forall x y : S, P x -> x [=] y -> P y.

Record CSetoid_predicate' : Type := 
 {csp'_pred   :> S -> Prop;
  csp'_strext :  pred_strong_ext' csp'_pred}.

Lemma csp'_wd : forall P : CSetoid_predicate', pred_wd' P.
intro P.
intro x; intros y H H0.
elim (csp'_strext P x y H).

autobatch.

intro H1.
elimtype False.
generalize H1.
exact (eq_imp_not_ap _ _ _ H0).
Qed.
*)



(*------------------------------------------------------------------------*)
(* --------------------------- Relations on Setoids --------------------- *)
(*------------------------------------------------------------------------*)
(* throughout this section consider (S : CSetoid) and (R : S -> S -> Prop) *)


(* Definition rel_wdr : Prop := forall x y z : S, R x y -> y [=] z -> R x z. *)
(* 
 primo tentativo ma R non e' ben tipato: si puo' fare il cast giusto (carrier di S) 
 in modo da sfruttare "relation"?
 e' concettualmente sbagliato lavorare ad un livello piu' alto (Type) ? *)
(* 
definition rel_wdr : \forall S: CSetoid. \forall x,y,z: S. \lambda R: relation S. Prop \def
 \lambda S: CSetoid. \lambda x,y,z: S. \lambda R: relation S. 
  R S x y \to y = z \to R S x z.
 
definition rel_wdr : \forall S: CSetoid. \forall x,y,z: (cs_crr S). \lambda R: relation (cs_crr S). Prop \def
 \lambda S: CSetoid. \lambda x,y,z: (cs_crr S). \lambda R: relation (cs_crr S). 
 R (cs_crr S) x y \to y = z \to R (cs_crr S) x z.
*)
definition rel_wdr : \forall S: CSetoid. (S \to S \to Prop) \to Prop \def
 \lambda S: CSetoid. \lambda R: (S \to S \to Prop). \forall x,y,z: S. 
  R x y \to y = z \to R x z.

(*Definition rel_wdl : Prop := forall x y z : S, R x y -> x [=] z -> R z y.*)
definition rel_wdl : \forall S: CSetoid. (S \to S \to Prop) \to Prop \def
 \lambda S: CSetoid. \lambda R: (S \to S \to Prop). \forall x,y,z: S. 
  R x y \to x = z \to R z y.
 
(* Definition rel_strext : CProp := forall x1 x2 y1 y2 : S, R x1 y1 -> (x1 [#] x2 or y1 [#] y2) or R x2 y2. *)
definition rel_strext : \forall S: CSetoid. (S \to S \to Prop) \to Prop \def
 \lambda S: CSetoid. \lambda R: (S \to S \to Prop). \forall x1,x2,y1,y2: S.
  R x1 y1 \to (x1 \neq x2 \or y1 \neq y2) \or R x2 y2.


(* Definition rel_strext_lft : CProp := forall x1 x2 y : S, R x1 y -> x1 [#] x2 or R x2 y. *)
definition rel_strext_lft : \forall S: CSetoid. (S \to S \to Prop) \to Prop \def
 \lambda S: CSetoid. \lambda R: (S \to S \to Prop). \forall x1,x2,y: S.
   R x1 y \to (x1 \neq x2 \or R x2 y).

(* Definition rel_strext_rht : CProp := forall x y1 y2 : S, R x y1 -> y1 [#] y2 or R x y2. *)
definition rel_strext_rht : \forall S: CSetoid. (S \to S \to Prop) \to Prop \def
 \lambda S: CSetoid. \lambda R: (S \to S \to Prop). \forall x,y1,y2: S.
   R x y1 \to (y1 \neq y2 \or R x y2).
   

lemma rel_strext_imp_lftarg : \forall S: CSetoid. \forall R: S \to S \to Prop.
  rel_strext S R \to rel_strext_lft S R.
unfold rel_strext. 
unfold rel_strext_lft. 
intros.
elim (H  x1 x2 y y H1)
[elim H2 
 [left. assumption
 |absurd (y \neq y) [assumption | apply (ap_irreflexive S y)]
 ]
|right. assumption
]
qed.


lemma rel_strext_imp_rhtarg : \forall S: CSetoid. \forall R: S \to S \to Prop.
  rel_strext S R \to rel_strext_rht S R.
unfold rel_strext.
unfold rel_strext_rht. 
intros.
elim (H x x y1 y2 H1)
[elim H2 
 [absurd (x \neq x) [assumption | apply (ap_irreflexive S x)]
 |left. assumption
 ]
|right. assumption
]
qed.


lemma rel_strextarg_imp_strext : \forall S: CSetoid. \forall R: S \to S \to Prop.
 (rel_strext_rht S R) \to (rel_strext_lft S R) \to (rel_strext S R).
unfold rel_strext_rht.
unfold rel_strext_lft. 
unfold rel_strext. 
intros.
elim ((H x1 y1 y2) H2)
[left. right. assumption
|elim ((H1 x1 x2 y1) H2)
 [left. left. assumption
 |elim ((H x2 y1 y2) H4)
  [left. right. assumption
  |right. assumption.
  ]
 ]
]
qed.

(* ---------- Definition of a setoid relation ----------------- *)
(* The type of relations over a setoid.  *)

(* TODO 
record CSetoid_relation1 (S: CSetoid) : Type \def 
  {csr_rel    : S \to S \to Prop;
   csr_wdr    :  rel_wdr S csr_rel;
   csr_wdl    :  rel_wdl S csr_rel;
   csr_strext :  rel_strext S csr_rel}.   
*)
(* CORN  
Record CSetoid_relation : Type := 
  {csr_rel    :> S -> S -> Prop;
   csr_wdr    :  rel_wdr csr_rel;
   csr_wdl    :  rel_wdl csr_rel;
   csr_strext :  rel_strext csr_rel}.
*)


(* ---------- gli stessi risultati di prima ma in CProp ---------*)
(*
Variable R : S -> S -> CProp.
Definition Crel_wdr : CProp := forall x y z : S, R x y -> y [=] z -> R x z.
Definition Crel_wdl : CProp := forall x y z : S, R x y -> x [=] z -> R z y.
Definition Crel_strext : CProp := forall x1 x2 y1 y2 : S,
 R x1 y1 -> R x2 y2 or x1 [#] x2 or y1 [#] y2.

Definition Crel_strext_lft : CProp := forall x1 x2 y : S, R x1 y -> R x2 y or x1 [#] x2.
Definition Crel_strext_rht : CProp := forall x y1 y2 : S, R x y1 -> R x y2 or y1 [#] y2.

Lemma Crel_strext_imp_lftarg : Crel_strext -> Crel_strext_lft.
Proof.
unfold Crel_strext, Crel_strext_lft in |- *; intros H x1 x2 y H0.
generalize (H x1 x2 y y).
intro H1.
elim (H1 H0).

autobatch.

intro H3.
elim H3; intro H4.

autobatch.
elim (ap_irreflexive _ _ H4).
Qed.

Lemma Crel_strext_imp_rhtarg : Crel_strext -> Crel_strext_rht.
unfold Crel_strext, Crel_strext_rht in |- *; intros H x y1 y2 H0.
generalize (H x x y1 y2 H0); intro H1.
elim H1; intro H2.

autobatch.

elim H2; intro H3.

elim (ap_irreflexive _ _ H3).

autobatch.
Qed.

Lemma Crel_strextarg_imp_strext :
 Crel_strext_rht -> Crel_strext_lft -> Crel_strext.
unfold Crel_strext, Crel_strext_lft, Crel_strext_rht in |- *;
 intros H H0 x1 x2 y1 y2 H1.
elim (H x1 y1 y2 H1); autobatch.
intro H2.
elim (H0 x1 x2 y2 H2); autobatch.
Qed.
*)




(* ---- e questo ??????? -----*)

(*Definition of a [CProp] setoid relation
The type of relations over a setoid.  *)
(*
Record CCSetoid_relation : Type := 
 {Ccsr_rel    :> S -> S -> CProp;
  Ccsr_strext :  Crel_strext Ccsr_rel}.

Lemma Ccsr_wdr : forall R : CCSetoid_relation, Crel_wdr R.
intro R.
red in |- *; intros x y z H H0.
elim (Ccsr_strext R x x y z H).

autobatch.

intro H1; elimtype False.
elim H1; intro H2.

exact (ap_irreflexive_unfolded _ _ H2).

generalize H2.
exact (eq_imp_not_ap _ _ _ H0).
Qed.

Lemma Ccsr_wdl : forall R : CCSetoid_relation, Crel_wdl R.
intro R.
red in |- *; intros x y z H H0.
elim (Ccsr_strext R x z y y H).

autobatch.

intro H1; elimtype False.
elim H1; intro H2.

generalize H2.
exact (eq_imp_not_ap _ _ _ H0).

exact (ap_irreflexive_unfolded _ _ H2).
Qed.

Lemma ap_wdr : Crel_wdr (cs_ap (c:=S)).
red in |- *; intros x y z H H0.
generalize (eq_imp_not_ap _ _ _ H0); intro H1.
elim (ap_cotransitive_unfolded _ _ _ H z); intro H2.

assumption.

elim H1.
apply ap_symmetric_unfolded.
assumption.
Qed.

Lemma ap_wdl : Crel_wdl (cs_ap (c:=S)).
red in |- *; intros x y z H H0.
generalize (ap_wdr y x z); intro H1.
apply ap_symmetric_unfolded.
apply H1.

apply ap_symmetric_unfolded.
assumption.

assumption.
Qed.

Lemma ap_wdr_unfolded : forall x y z : S, x [#] y -> y [=] z -> x [#] z.
Proof ap_wdr.

Lemma ap_wdl_unfolded : forall x y z : S, x [#] y -> x [=] z -> z [#] y.
Proof ap_wdl.

Lemma ap_strext : Crel_strext (cs_ap (c:=S)).
red in |- *; intros x1 x2 y1 y2 H.
case (ap_cotransitive_unfolded _ _ _ H x2); intro H0.

autobatch.

case (ap_cotransitive_unfolded _ _ _ H0 y2); intro H1.

autobatch.

right; right.
apply ap_symmetric_unfolded.
assumption.
Qed.

Definition predS_well_def (P : S -> CProp) : CProp := forall x y : S,
 P x -> x [=] y -> P y.

End CSetoid_relations_and_predicates.

Declare Left Step ap_wdl_unfolded.
Declare Right Step ap_wdr_unfolded.
*)









(*------------------------------------------------------------------------*)
(* ------------------------- Functions between setoids ------------------ *)
(*------------------------------------------------------------------------*)

(* Such functions must preserve the setoid equality
and be strongly extensional w.r.t. the apartness, i.e.
if f(x,y) # f(x1,y1), then  x # x1 or y # y1.
For every arity this has to be defined separately. *)

(* throughout this section consider (S1,S2,S3 : CSetoid) and (f : S1 \to S2) *)

(* First we consider unary functions.  *)

(*
In the following two definitions,
f is a function from (the carrier of) S1 to (the carrier of) S2  *)

(* Nota: senza le parentesi di (S1 \to S2) non funziona, perche'? *)
definition fun_wd : \forall S1,S2 : CSetoid. (S1 \to S2) \to Prop \def
 \lambda S1,S2 : CSetoid.\lambda f : S1 \to S2. \forall x,y : S1. 
  x = y \to f x = f y.

definition fun_strext : \forall S1,S2 : CSetoid. (S1 \to S2) \to Prop \def
 \lambda S1,S2 : CSetoid.\lambda f : S1 \to S2. \forall x,y : S1. 
  (f x \neq f y) \to (x \neq y).

lemma fun_strext_imp_wd : \forall S1,S2 : CSetoid. \forall f : S1 \to S2.
 fun_strext S1 S2 f \to fun_wd S1 S2 f.
unfold fun_strext.
unfold fun_wd. 
intros.
apply not_ap_imp_eq.
unfold.intro.
apply (eq_imp_not_ap ? ? ? H1).
apply H.assumption.
qed.

(* funzioni tra setoidi *)
record CSetoid_fun (S1,S2 : CSetoid) : Type \def 
  {csf_fun    : S1 \to S2;
   csf_strext :  (fun_strext S1 S2 csf_fun)}.

lemma csf_wd : \forall S1,S2 : CSetoid. \forall f : CSetoid_fun S1 S2. fun_wd S1 S2 (csf_fun S1 S2 f).
intros.
apply fun_strext_imp_wd.
apply csf_strext.
qed.

definition Const_CSetoid_fun : \forall S1,S2: CSetoid. S2 \to CSetoid_fun S1 S2.
intros. apply (mk_CSetoid_fun S1 S2 (\lambda x:S1.c)).
unfold.intros.
elim (ap_irreflexive ? ? H).
qed.


(* ---- Binary functions ------*)
(* throughout this section consider (S1,S2,S3 : CSetoid) and (f : S1 \to S2 \to S3) *)

definition bin_fun_wd : \forall S1,S2,S3 : CSetoid. (S1 \to S2 \to S3) \to Prop \def 
 \lambda S1,S2,S3 : CSetoid. \lambda f : S1 \to S2 \to S3. \forall x1,x2: S1. \forall y1,y2: S2.
  x1 = x2 \to y1 = y2 \to f x1 y1 = f x2 y2.

(*
Definition bin_fun_strext : CProp := forall x1 x2 y1 y2,
 f x1 y1 [#] f x2 y2 -> x1 [#] x2 or y1 [#] y2.
*)

definition bin_fun_strext: \forall S1,S2,S3 : CSetoid. (S1 \to S2 \to S3) \to Prop \def 
 \lambda S1,S2,S3 : CSetoid. \lambda f : S1 \to S2 \to S3. \forall x1,x2: S1. \forall y1,y2: S2.
  f x1 y1 \neq f x2 y2 \to x1 \neq x2 \lor y1 \neq y2.

lemma bin_fun_strext_imp_wd : \forall S1,S2,S3: CSetoid.\forall f:S1 \to S2 \to S3.
bin_fun_strext ? ? ? f \to bin_fun_wd ? ? ? f.
intros.unfold in H.
unfold.intros.
apply not_ap_imp_eq.unfold.intro.
elim (H x1 x2 y1 y2 H3).
apply (eq_imp_not_ap ? ? ? H1 H4).
apply (eq_imp_not_ap ? ? ? H2 H4).
qed.



record CSetoid_bin_fun (S1,S2,S3: CSetoid) : Type \def 
 {csbf_fun    :2> S1 \to S2 \to S3;
  csbf_strext :  (bin_fun_strext S1 S2 S3 csbf_fun)}.

lemma csbf_wd : \forall S1,S2,S3: CSetoid. \forall f : CSetoid_bin_fun S1 S2 S3. 
 bin_fun_wd S1 S2 S3 (csbf_fun S1 S2 S3 f).
intros.
apply bin_fun_strext_imp_wd.
apply csbf_strext.
qed.

lemma csf_wd_unfolded : \forall S1,S2: CSetoid. \forall f : CSetoid_fun S1 S2. \forall x,x' : S1. 
 x = x' \to (csf_fun S1 S2 f) x = (csf_fun S1 S2 f) x'.
intros.
apply (csf_wd S1 S2 f x x').
assumption.
qed.

lemma csf_strext_unfolded : \forall S1,S2: CSetoid. \forall f : CSetoid_fun S1 S2. \forall x,y : S1.
(csf_fun S1 S2 f) x \neq (csf_fun S1 S2 f) y \to x \neq y.
intros.
apply (csf_strext S1 S2 f x y).
assumption.
qed.

lemma csbf_wd_unfolded : \forall S1,S2,S3 : CSetoid. \forall f : CSetoid_bin_fun S1 S2 S3. \forall x,x':S1. 
\forall y,y' : S2. x = x' \to y = y' \to (csbf_fun S1 S2 S3 f) x y = (csbf_fun S1 S2 S3 f) x' y'.
intros.
apply (csbf_wd S1 S2 S3 f x x' y y'); assumption.
qed.

(* Hint Resolve csf_wd_unfolded csbf_wd_unfolded: algebra_c.*)

(* The unary and binary (inner) operations on a csetoid
An operation is a function with domain(s) and co-domain equal. *)

(* Properties of binary operations *)

definition commutes : \forall S: CSetoid. (S \to S \to S)  \to Prop \def 
 \lambda S: CSetoid. \lambda f : S \to S \to S. 
 \forall x,y : S. f x y = f y x.
 
definition CSassociative : \forall S: CSetoid. \forall f: S \to S \to S.  Prop \def 
\lambda S: CSetoid. \lambda f : S \to S \to S. 
\forall x,y,z : S.
 f x (f y z) = f (f x y) z.

definition un_op_wd : \forall S:CSetoid. (S \to S) \to Prop \def 
\lambda S: CSetoid. \lambda f: (S \to S).  fun_wd S S f.


definition un_op_strext: \forall S:CSetoid. (S \to S) \to Prop \def 
\lambda S:CSetoid. \lambda f: (S \to S).  fun_strext S S f.


definition CSetoid_un_op : CSetoid \to Type \def 
\lambda S:CSetoid. CSetoid_fun S S.

definition mk_CSetoid_un_op : \forall S:CSetoid. \forall f: S \to S. fun_strext S S f \to CSetoid_fun S S
 \def 
\lambda S:CSetoid. \lambda f: S \to S. mk_CSetoid_fun S S f.

lemma id_strext : \forall S:CSetoid. un_op_strext S (\lambda x:S. x).
unfold un_op_strext.
unfold fun_strext.
intros.
simplify in H.
exact H.
qed.

lemma id_pres_eq : \forall S:CSetoid. un_op_wd S (\lambda x : S.x).
unfold un_op_wd.
unfold fun_wd.
intros.
simplify.
exact H.
qed.

definition id_un_op : \forall S:CSetoid. CSetoid_un_op S 
 \def \lambda S: CSetoid. mk_CSetoid_un_op S (\lambda x : cs_crr S.x) (id_strext S).

definition un_op_fun: \forall S:CSetoid. CSetoid_un_op S \to CSetoid_fun S S
\def \lambda S.\lambda f.f.

coercion cic:/matita/algebra/CoRN/Setoids/un_op_fun.con.

definition cs_un_op_strext : \forall S:CSetoid. \forall f: CSetoid_fun S S. fun_strext S S (csf_fun S S f) \def 
\lambda S:CSetoid. \lambda f : CSetoid_fun S S. csf_strext S S f.

lemma un_op_wd_unfolded : \forall S:CSetoid. \forall op : CSetoid_un_op S. 
\forall x, y : S.
x = y \to (csf_fun S S op) x =  (csf_fun S S op) y.
intros.
apply (csf_wd S S ?).assumption.
qed.

lemma un_op_strext_unfolded : \forall S:CSetoid. \forall op : CSetoid_un_op S. 
\forall x, y : S.
 (csf_fun S S op) x \neq (csf_fun S S op) y \to x \neq y.
exact cs_un_op_strext.
qed.


(* Well-defined binary operations on a setoid.  *)

definition bin_op_wd : \forall S:CSetoid. (S \to S \to S) \to Prop \def 
\lambda S:CSetoid. bin_fun_wd S S S.

definition bin_op_strext : \forall S:CSetoid. (S \to S \to S) \to Prop \def 
\lambda S:CSetoid. bin_fun_strext S S S.

definition CSetoid_bin_op : CSetoid \to Type \def 
\lambda S:CSetoid. CSetoid_bin_fun S S S.


definition mk_CSetoid_bin_op : \forall S:CSetoid. \forall f: S \to S \to S.  
bin_fun_strext S S S f \to CSetoid_bin_fun S S S \def
 \lambda S:CSetoid. \lambda f: S \to S \to S. 
 mk_CSetoid_bin_fun S S S f.
 
(* da controllare che sia ben tipata 
definition cs_bin_op_wd : \forall S:CSetoid. ? \def 
\lambda S:CSetoid.  csbf_wd S S S.
*)
definition cs_bin_op_wd : \forall S:CSetoid. \forall f: CSetoid_bin_fun S S S. bin_fun_wd S S S (csbf_fun S S S f) \def 
\lambda S:CSetoid. csbf_wd S S S.

definition cs_bin_op_strext : \forall S:CSetoid. \forall f: CSetoid_bin_fun S S S. bin_fun_strext S S S (csbf_fun S S S f) \def 
\lambda S:CSetoid. csbf_strext S S S.



(* Identity Coercion bin_op_bin_fun : CSetoid_bin_op >-> CSetoid_bin_fun. *)

definition bin_op_bin_fun: \forall S:CSetoid. CSetoid_bin_op S \to CSetoid_bin_fun S S S
\def \lambda S.\lambda f.f.

coercion cic:/matita/algebra/CoRN/Setoids/bin_op_bin_fun.con.




lemma bin_op_wd_unfolded :\forall S:CSetoid.  \forall op : CSetoid_bin_op S. \forall x1, x2, y1, y2 : S.
 x1 = x2 \to y1 = y2 \to (csbf_fun S S S op) x1 y1 = (csbf_fun S S S op) x2 y2.
exact cs_bin_op_wd.
qed.

lemma bin_op_strext_unfolded : \forall S:CSetoid.  \forall op : CSetoid_bin_op S. \forall x1, x2, y1, y2 : S.
 (csbf_fun S S S op) x1 y1 \neq (csbf_fun S S S op) x2 y2 \to x1 \neq x2 \lor y1 \neq y2.
exact cs_bin_op_strext.
qed.

lemma bin_op_is_wd_un_op_lft : \forall S:CSetoid. \forall op : CSetoid_bin_op S. \forall c : cs_crr S.
 un_op_wd S (\lambda x : cs_crr S. ((csbf_fun S S S op) x c)).
intros. unfold. unfold.
intros. apply bin_op_wd_unfolded [ assumption | apply eq_reflexive_unfolded ]
qed.

lemma bin_op_is_wd_un_op_rht : \forall S:CSetoid. \forall op : CSetoid_bin_op S. \forall c : cs_crr S.
 un_op_wd S (\lambda x : cs_crr S. ((csbf_fun S S S op) c x)).
intros. unfold. unfold.
intros. apply bin_op_wd_unfolded [ apply eq_reflexive_unfolded | assumption ]
qed.


lemma bin_op_is_strext_un_op_lft : \forall S:CSetoid. \forall op : CSetoid_bin_op S. \forall c : cs_crr S.
 un_op_strext S (\lambda x : cs_crr S. ((csbf_fun S S S op) x c)).
intros. unfold un_op_strext. unfold fun_strext.
intros.
cut (x \neq y \lor c \neq c) 
[ elim Hcut 
  [ assumption 
  | generalize in match (ap_irreflexive_unfolded ? ? H1). intro. elim H2
  ]
| apply (bin_op_strext_unfolded S op x y c c). assumption.
]
qed.

lemma bin_op_is_strext_un_op_rht : \forall S:CSetoid. \forall op : CSetoid_bin_op S. \forall c : cs_crr S.
 un_op_strext S (\lambda x : cs_crr S. ((csbf_fun S S S op) c x)).
intros. unfold un_op_strext. unfold fun_strext.
intros.
cut (c \neq c \lor x \neq y) 
[ elim Hcut 
  [ generalize in match (ap_irreflexive_unfolded ? ? H1). intro. elim H2
  | assumption
  ]
| apply (bin_op_strext_unfolded S op c c x y). assumption.
]
qed.

definition bin_op2un_op_rht : \forall S:CSetoid. \forall op : CSetoid_bin_op S.
\forall  c : cs_crr S. CSetoid_un_op S \def
 \lambda S:CSetoid. \lambda op: CSetoid_bin_op S. \lambda  c : cs_crr S.
  mk_CSetoid_un_op S (\lambda x:cs_crr S. ((csbf_fun S S S op) c x))
   (bin_op_is_strext_un_op_rht S op c).

definition bin_op2un_op_lft : \forall S:CSetoid. \forall op : CSetoid_bin_op S.
\forall  c : cs_crr S. CSetoid_un_op S \def
 \lambda S:CSetoid. \lambda op: CSetoid_bin_op S. \lambda  c : cs_crr S.
  mk_CSetoid_un_op S (\lambda x:cs_crr S. ((csbf_fun S S S op) x c))
   (bin_op_is_strext_un_op_lft S op c).

(*
Definition bin_op2un_op_rht (op : CSetoid_bin_op) (c : S) : CSetoid_un_op :=
  Build_CSetoid_un_op (fun x : S => op c x) (bin_op_is_strext_un_op_rht op c).


Definition bin_op2un_op_lft (op : CSetoid_bin_op) (c : S) : CSetoid_un_op :=
  Build_CSetoid_un_op (fun x : S => op x c) (bin_op_is_strext_un_op_lft op c).
*)


(*
Implicit Arguments commutes [S].
Implicit Arguments associative [S].
Hint Resolve bin_op_wd_unfolded un_op_wd_unfolded: algebra_c.
*)

(*The binary outer operations on a csetoid*)


(*
Well-defined outer operations on a setoid.
*)
definition outer_op_well_def : \forall S1,S2:CSetoid. (S1 \to S2 \to S2) \to Prop \def 
\lambda S1,S2:CSetoid. bin_fun_wd S1 S2 S2.

definition outer_op_strext : \forall S1,S2:CSetoid. (S1 \to S2 \to S2) \to Prop \def 
\lambda S1,S2:CSetoid. bin_fun_strext S1 S2 S2.

definition CSetoid_outer_op : \forall S1,S2:CSetoid.Type \def
\lambda S1,S2:CSetoid.
 CSetoid_bin_fun S1 S2 S2.
 
definition mk_CSetoid_outer_op : \forall S1,S2:CSetoid. 
\forall f : S1 \to S2 \to S2. 
bin_fun_strext S1 S2 S2 f \to CSetoid_bin_fun S1 S2 S2 \def 
\lambda S1,S2:CSetoid.
mk_CSetoid_bin_fun S1 S2 S2.

definition csoo_wd : \forall S1,S2:CSetoid. \forall f : CSetoid_bin_fun S1 S2 S2. 
bin_fun_wd S1 S2 S2 (csbf_fun S1 S2 S2 f)  \def 
\lambda S1,S2:CSetoid.
csbf_wd S1 S2 S2.

definition csoo_strext : \forall S1,S2:CSetoid. 
\forall f : CSetoid_bin_fun S1 S2 S2. 
bin_fun_strext S1 S2 S2 (csbf_fun S1 S2 S2 f) \def 
\lambda S1,S2:CSetoid.
csbf_strext S1 S2 S2.


definition outer_op_bin_fun: \forall S:CSetoid. 
CSetoid_outer_op S S \to CSetoid_bin_fun S S S
\def \lambda S.\lambda f.f.

coercion cic:/matita/algebra/CoRN/Setoids/outer_op_bin_fun.con.
(* begin hide 
Identity Coercion outer_op_bin_fun : CSetoid_outer_op >-> CSetoid_bin_fun.
end hide *)

lemma csoo_wd_unfolded :\forall S:CSetoid. \forall op : CSetoid_outer_op S S. 
\forall x1, x2, y1, y2 : S.
 x1 = x2 -> y1 = y2 -> (csbf_fun S S S op) x1 y1 = (csbf_fun S S S op) x2 y2.
intros.
apply csoo_wd[assumption|assumption]
qed.

(*
Hint Resolve csoo_wd_unfolded: algebra_c.
*)



(*---------------------------------------------------------------*)
(*--------------------------- Subsetoids ------------------------*)
(*---------------------------------------------------------------*)

(* Let S be a setoid, and P a predicate on the carrier of S *)
(* Variable P : S -> CProp *)

record subcsetoid_crr (S: CSetoid) (P: S \to Prop) : Type \def 
 {scs_elem :> S;
  scs_prf  :  P scs_elem}.

definition restrict_relation : \forall S:CSetoid. \forall R : S \to S \to Prop.
 \forall P: S \to Prop. relation (subcsetoid_crr S P) \def
  \lambda S:CSetoid. \lambda R : S \to S \to Prop.
  \lambda P: S \to Prop. \lambda a,b: subcsetoid_crr S P.
  match a with
  [ (mk_subcsetoid_crr x H) \Rightarrow
    match b with
    [ (mk_subcsetoid_crr y H) \Rightarrow R x y ]
  ].
(* CPROP
definition Crestrict_relation (R : Crelation S) : Crelation subcsetoid_crr :=
  fun a b : subcsetoid_crr =>
  match a, b with
  | Build_subcsetoid_crr x _, Build_subcsetoid_crr y _ => R x y
  end.
*)

definition subcsetoid_eq : \forall S:CSetoid. \forall P: S \to Prop.
 relation (subcsetoid_crr S P)\def
  \lambda S:CSetoid.
  restrict_relation S (cs_eq S).

definition subcsetoid_ap : \forall S:CSetoid. \forall P: S \to Prop.
 relation (subcsetoid_crr S P)\def
  \lambda S:CSetoid.
  restrict_relation S (cs_ap S).
  
(* N.B. da spostare in relations.ma... *)
definition equiv : \forall A: Type. \forall R: relation A. Prop \def
 \lambda A: Type. \lambda R: relation A.
 (reflexive A R) \land (transitive A R) \land (symmetric A R).

remark subcsetoid_equiv : \forall S:CSetoid. \forall P: S \to Prop.
equiv ? (subcsetoid_eq S P).
intros. unfold equiv. split
[split
 [unfold. intro. elim x. simplify. apply (eq_reflexive S)
 |unfold. intros 3. elim y 2.
  elim x 2. elim z 2. simplify.
  exact (eq_transitive ? c1 c c2)
 ]
| unfold. intros 2. elim x 2. elim y 2. simplify. exact (eq_symmetric ? c c1).
]
qed.

(*
axiom subcsetoid_is_CSetoid : \forall S:CSetoid. \forall P: S \to Prop. 
is_CSetoid ? (subcsetoid_eq S P) (subcsetoid_ap S P).
*)

lemma subcsetoid_is_CSetoid : \forall S:CSetoid. \forall P: S \to Prop. 
is_CSetoid ? (subcsetoid_eq S P) (subcsetoid_ap S P).
intros.
apply (mk_is_CSetoid ? (subcsetoid_eq S P) (subcsetoid_ap S P))
[ unfold. intros.unfold. elim x. exact (ap_irreflexive_unfolded S ? ?) 
 [ assumption | simplify in H1. exact H1 ]
 (* irreflexive *)
|unfold. intros 2. elim x. generalize in match H1. elim y.simplify in H3. simplify.
exact (ap_symmetric ? ? ? H3)
(* cotransitive *)
|unfold.intros 2. elim x.generalize in match H1. elim y. elim z.simplify. simplify in H3.
apply (ap_cotransitive ? ? ? H3)
(* tight *)
|unfold.intros.elim x. elim y.simplify.
apply (ap_tight S ? ?)]
qed.


definition mk_SubCSetoid : \forall S:CSetoid. \forall P: S \to Prop. CSetoid \def 
\lambda S:CSetoid. \lambda P:S \to Prop.
mk_CSetoid (subcsetoid_crr S P) (subcsetoid_eq S P) (subcsetoid_ap S P) (subcsetoid_is_CSetoid S P).

(* Subsetoid unary operations
%\begin{convention}%
Let [f] be a unary setoid operation on [S].
%\end{convention}%
*)

(* Section SubCSetoid_unary_operations.
Variable f : CSetoid_un_op S.
*)

definition un_op_pres_pred : \forall S:CSetoid. \forall P: S \to Prop.
 CSetoid_un_op S \to Prop \def
 \lambda S:CSetoid. \lambda P: S \to Prop. \lambda f: CSetoid_un_op S.
 \forall x : cs_crr S. P x \to P ((csf_fun S S f) x).
 
definition restr_un_op : \forall S:CSetoid. \forall P: S \to Prop.
  \forall f: CSetoid_un_op S. \forall pr: un_op_pres_pred S P f. 
  subcsetoid_crr S P \to subcsetoid_crr S P \def
  \lambda S:CSetoid.  \lambda P: S \to Prop. \lambda f: CSetoid_un_op S. 
  \lambda pr : un_op_pres_pred S P f.\lambda a: subcsetoid_crr S P.
  match a with
  [ (mk_subcsetoid_crr x p) \Rightarrow 
    (mk_subcsetoid_crr ? ? ((csf_fun S S f) x) (pr x p))].

(* TODO *) 
lemma restr_un_op_wd  : \forall S:CSetoid. \forall P: S \to Prop. 
\forall f: CSetoid_un_op S. \forall pr: un_op_pres_pred S P f.  
un_op_wd (mk_SubCSetoid S P) (restr_un_op S P f pr).
intros.
unfold.unfold.intros 2.elim x 2.elim y 2.
simplify.
intro.
normalize in H2.
apply (un_op_wd_unfolded ? f ? ? H2).
qed.

lemma restr_un_op_strext : \forall S:CSetoid. \forall P: S \to Prop. 
\forall f: CSetoid_un_op S. \forall pr: un_op_pres_pred S P f.  
un_op_strext (mk_SubCSetoid S P) (restr_un_op S P f pr).
intros.unfold.unfold. intros 2.elim y 2. elim x 2.
intros.normalize in H2.
apply (cs_un_op_strext ? f ? ? H2).
qed.

definition mk_SubCSetoid_un_op : \forall S:CSetoid. \forall P: S \to Prop. \forall f: CSetoid_un_op S.
 \forall pr:un_op_pres_pred S P f. CSetoid_un_op (mk_SubCSetoid S P).
 intros (S P f pr).
 apply (mk_CSetoid_un_op (mk_SubCSetoid S P) (restr_un_op S P f pr) (restr_un_op_strext S P f pr)).
 qed.

(* BUG Universe Inconsistency detected 
 definition mk_SubCSetoid_un_op : \forall S:CSetoid. \forall P: S \to Prop. \forall f: CSetoid_un_op S.
 \forall pr:un_op_pres_pred S P f. CSetoid_un_op (mk_SubCSetoid S P) \def
 \lambda S:CSetoid. \lambda P: S \to Prop. \lambda f: CSetoid_un_op S.
  \lambda pr:un_op_pres_pred S P f.
  mk_CSetoid_un_op (mk_SubCSetoid S P) (restr_un_op S P f pr) (restr_un_op_strext S P f pr).
*)

(* Subsetoid binary operations
Let [f] be a binary setoid operation on [S].
*)

(* Section SubCSetoid_binary_operations. 
Variable f : CSetoid_bin_op S.
*)

definition bin_op_pres_pred : \forall S:CSetoid. \forall P: S \to Prop. 
(CSetoid_bin_op S) \to Prop \def
 \lambda S:CSetoid. \lambda P: S \to Prop. \lambda f: CSetoid_bin_op S.
 \forall x,y : S. P x \to P y \to P ( (csbf_fun S S S f) x y).

(*
Assume [bin_op_pres_pred].
*)

(* Variable pr : bin_op_pres_pred. *)

definition restr_bin_op : \forall S:CSetoid. \forall P:S \to Prop. 
 \forall f: CSetoid_bin_op S.\forall op : (bin_op_pres_pred S P f).
 \forall a, b : subcsetoid_crr S P. subcsetoid_crr S P \def
 \lambda S:CSetoid. \lambda P:S \to Prop.
 \lambda f: CSetoid_bin_op S. \lambda pr : (bin_op_pres_pred S P f).
 \lambda a, b : subcsetoid_crr S P.
  match a with
  [ (mk_subcsetoid_crr x p) \Rightarrow 
    match b with
    [ (mk_subcsetoid_crr y q) \Rightarrow 
        (mk_subcsetoid_crr ? ? ((csbf_fun S S S f) x y) (pr x y p q))]
  ].


(* TODO *)
lemma restr_bin_op_well_def  : \forall S:CSetoid. \forall P: S \to Prop. 
\forall f: CSetoid_bin_op S. \forall pr: bin_op_pres_pred S P f.  
bin_op_wd (mk_SubCSetoid S P) (restr_bin_op S P f pr).
intros.
unfold.unfold.intros 2.elim x1 2. elim x2 2.intros 2. elim y1 2. elim y2 2.
simplify.
intros.
normalize in H4.
normalize in H5.
apply (cs_bin_op_wd ? f ? ? ? ? H4 H5).
qed.

lemma restr_bin_op_strext : \forall S:CSetoid. \forall P: S \to Prop. 
\forall f: CSetoid_bin_op S. \forall pr: bin_op_pres_pred S P f.  
bin_op_strext (mk_SubCSetoid S P) (restr_bin_op S P f pr).
intros.unfold.unfold. intros 2.elim x1 2. elim x2 2.intros 2. elim y1 2. elim y2 2.
simplify.intros.
normalize in H4.
apply (cs_bin_op_strext ? f ? ? ? ? H4).
qed.

definition mk_SubCSetoid_bin_op : \forall S:CSetoid. \forall P: S \to Prop. 
  \forall f: CSetoid_bin_op S. \forall pr: bin_op_pres_pred S P f. 
  CSetoid_bin_op (mk_SubCSetoid S P).
  intros (S P f pr).
  apply (mk_CSetoid_bin_op (mk_SubCSetoid S P) (restr_bin_op S P f pr)(restr_bin_op_strext S P f pr)).
  qed.

(* BUG Universe Inconsistency detected 
definition mk_SubCSetoid_bin_op : \forall S:CSetoid. \forall P: S \to Prop. 
  \forall f: CSetoid_bin_op S. \forall pr: bin_op_pres_pred S P f. 
  CSetoid_bin_op (mk_SubCSetoid S P) \def
  \lambda S:CSetoid. \lambda P: S \to Prop. 
  \lambda f: CSetoid_bin_op S. \lambda pr: bin_op_pres_pred S P f.
    mk_CSetoid_bin_op (mk_SubCSetoid S P) (restr_bin_op S P f pr)(restr_bin_op_strext S P f pr).
*)

lemma restr_f_assoc : \forall S:CSetoid. \forall P: S \to Prop. 
  \forall f: CSetoid_bin_op S. \forall pr: bin_op_pres_pred S P f.
    CSassociative S (csbf_fun S S S f) 
    \to CSassociative (mk_SubCSetoid S P) (csbf_fun (mk_SubCSetoid S P) (mk_SubCSetoid S P) (mk_SubCSetoid S P) (mk_SubCSetoid_bin_op S P f pr)).
intros 4.
intro.
unfold.
intros 3.
elim z 2.elim y 2. elim x 2.
whd.
apply H.
qed.

definition caseZ_diff: \forall A:Type.Z \to (nat \to nat \to A) \to A \def
\lambda A:Type.\lambda z:Z.\lambda f:nat \to nat \to A.
  match z with
  [OZ \Rightarrow f O O 
  |(pos n) \Rightarrow f (S n) O
  |(neg n) \Rightarrow f O (S n)].
  
(* Zminus.ma *)  
theorem Zminus_S_S : \forall n,m:nat.
Z_of_nat (S n) - S m = Z_of_nat n - m.
intros.
elim n.elim m.simplify. reflexivity.reflexivity.
elim m.simplify.reflexivity.reflexivity.
qed.



lemma proper_caseZ_diff_CS : \forall CS : CSetoid. \forall f : nat \to nat \to CS.
 (\forall m,n,p,q : nat. eq nat (plus m q) (plus n p) \to (f m n) = (f p q)) \to
 \forall m,n : nat. caseZ_diff CS (Zminus (Z_of_nat m) (Z_of_nat n)) f = (f m n).
intros.
(* perche' apply nat_elim2 non funziona?? *)
apply (nat_elim2 (\lambda m,n.caseZ_diff CS (Zminus (Z_of_nat m) (Z_of_nat n)) f = f m n)).
intro.simplify.
apply (nat_case n1).simplify.
apply eq_reflexive.
intro.simplify.apply eq_reflexive.
intro.simplify.apply eq_reflexive.
intros 2.
rewrite > (Zminus_S_S n1 m1).
intros.
cut (f n1 m1 = f (S n1) (S m1)).
apply eq_symmetric_unfolded.
apply eq_transitive.
apply f. apply n1. apply m1.
apply eq_symmetric_unfolded.assumption.
apply eq_symmetric_unfolded.assumption.
apply H.
autobatch.
qed.

(*
Finally, we characterize functions defined on the natural numbers also as setoid functions, similarly to what we already did for predicates.
*)


definition nat_less_n_fun :  \forall S:CSetoid. \forall n:nat. ? \def
 \lambda S:CSetoid. \lambda n:nat. \lambda f: \forall i:nat. i < n \to S.
  \forall i,j : nat. eq nat i j \to (\forall H : i < n.
   \forall H' : j < n . (f i H) =  (f j H')).

definition nat_less_n_fun' : \forall S:CSetoid. \forall n:nat. ? \def
  \lambda S:CSetoid. \lambda n:nat. \lambda f: \forall i: nat. i <= n \to S.
   \forall i,j : nat. eq nat i j \to \forall H : i <= n. 
  \forall H' : j <= n. f i H = f j H'.

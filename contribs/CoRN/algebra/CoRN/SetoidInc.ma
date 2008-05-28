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

set "baseuri" "cic:/matita/algebra/CoRN/SetoidInc".
include "algebra/CoRN/SetoidFun.ma".

(* $Id: CSetoidInc.v,v 1.3 2004/04/22 14:49:43 lcf Exp $ *)

(* printing included %\ensuremath{\subseteq}% #&sube;# *)

(* Section inclusion. *)

(* Inclusion

Let [S] be a setoid, and [P], [Q], [R] be predicates on [S]. *)

(* Variable S : CSetoid. *)

definition included : \forall S : CSetoid. \forall P,Q : S \to Type. Type \def
   \lambda S : CSetoid. \lambda P,Q : S \to Type.
   \forall x : S. P x \to Q x.

(* Section Basics. *)

(* Variables P Q R : S -> CProp. *)
lemma included_refl : \forall S : CSetoid. \forall P : S \to Type. 
  included S P P.
intros.
unfold.
intros.
assumption.
qed.

lemma included_trans : \forall S : CSetoid. \forall P,Q,R : S \to Type.
  included S P Q \to included S Q R \to included S P R.
intros.
unfold.
intros.
apply i1.
apply i.
assumption.
qed.

lemma included_conj : \forall S : CSetoid. \forall P,Q,R : S \to Type.
 included S P Q \to included S P R \to included S P (conjP S Q R).
intros 4.
unfold included.
intros;
unfold.
split [apply f.assumption|apply f1.assumption]
qed.

lemma included_conj' : \forall S : CSetoid. \forall P,Q,R : S \to Type.
  included S (conjP S P Q) P.
  intros.
exact (prj1 S P Q).
qed.

lemma included_conj'' : \forall S : CSetoid. \forall P,Q,R : S \to Type.
 included S (conjP S P Q) Q.
 intros.
exact (prj2 S P Q).
qed.

lemma included_conj_lft : \forall S : CSetoid. \forall P,Q,R : S \to Type.
  included S R (conjP S P Q) -> included S R P.
intros 4.
unfold included.
unfold conjP.intros (f1 x H2).
elim (f1 x ); assumption.
qed.

lemma included_conj_rht : \forall S : CSetoid. \forall P,Q,R : S \to Type. 
  included S R (conjP S P Q) \to included S R Q.
  intros 4.
  unfold included.
  unfold conjP.
intros (H1 x H2).
elim (H1 x); assumption.
qed.
lemma included_extend : \forall S : CSetoid. \forall P,Q,R : S \to Type.  
  \forall H : \forall x. P x \to Type.
 included S R (extend S P H) \to included S R P.
intros 4.
intros (H0 H1).
unfold.
unfold extend in H1.
intros.
elim (H1 x);assumption.
qed.


(* End Basics. *)

(*
%\begin{convention}% Let [I,R:S->CProp] and [F G:(PartFunct S)], and denote
by [P] and [Q], respectively, the domains of [F] and [G].
%\end{convention}%
*)

(* Variables F G : (PartFunct S). *)

(* begin hide *)
(* Let P := Dom F. *)
(* Let Q := Dom G. *)
(* end hide *)

(* Variable R : S -> CProp. *)
lemma included_FComp : \forall S : CSetoid. \forall F,G: PartFunct S. 
\forall R : S \to Type.
  included S R (UP ? F) \to (\forall x: S. \forall Hx. (R x) \to UQ ? G (pfpfun ? F x Hx)) \to 
  included S R (pfdom ? (Fcomp ? F G)).
intros (S F G R HP HQ).
unfold Fcomp.
simplify.
unfold included. intros (x Hx).
apply (existT ? ? (HP x Hx)).
apply HQ.
assumption.
qed.

lemma included_FComp': \forall S : CSetoid. \forall F,G: PartFunct S. 
\forall R : S \to Type.
included S R (pfdom ? (Fcomp ? F G)) \to included S R (UP ? F).
intros (S F G R H).
unfold Fcomp in H.
simplify in H.
unfold. intros (x Hx).
elim (H x Hx);
assumption.
qed.

(* End inclusion. *) 

(* Implicit Arguments included [S].

Hint Resolve included_refl included_FComp : included.

Hint Immediate included_trans included_FComp' : included. *)

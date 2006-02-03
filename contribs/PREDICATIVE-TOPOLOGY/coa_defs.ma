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

set "baseuri" "cic:/matita/PREDICATIVE-TOPOLOGY/coa_defs".

include "iff.ma".
include "domain_data.ma".

(* COMPLETE OVERLAP ALGEBRAS 
*)

record COA: Type \def {
   coa:> Class;                                  (* carrier *)
	 le: coa \to coa \to Prop;                     (* inclusion *)
	 ov: coa \to coa \to Prop;                     (* overlap *)
	 sup: \forall (D:Domain). (D \to coa) \to coa; (* supremum *)
	 inf: \forall (D:Domain). (D \to coa) \to coa; (* infimum *)
	 le_refl: \forall p. le p p;
	 le_trans: \forall p,r. le p r \to \forall q. le r q \to le p q; 
	 le_antysym: \forall q,p. le q p \to le p q \to ceq ? p q;
	 ov_sym: \forall q,p. ov q p \to ov p q;
	 sup_le: \forall D,ps,q. le (sup D ps) q \liff \iforall d. le (ps d) q;
	 inf_le: \forall D,p,qs. le p (inf D qs) \liff \iforall d. le p (qs d);
	 sup_ov: \forall D,ps,q. ov (sup D ps) q \liff \iexists d. ov (ps d) q;
	 density: \forall p,q. (\forall r. ov p r \to ov q r) \to le p q
}.

definition zero: \forall (P:COA). P \def
   \lambda (P:COA). inf P ? (dvoid_ixfam P).

definition one: \forall (P:COA). P \def
   \lambda (P:COA). sup P ? (dvoid_ixfam P).

definition binf: \forall (P:COA). P \to P \to P \def
   \lambda (P:COA). \lambda p0,p1.
   inf P ? (dbool_ixfam P p0 p1).

definition bsup: \forall (P:COA). P \to P \to P \def
   \lambda (P:COA). \lambda p0,p1.
   sup P ? (dbool_ixfam P p0 p1).

(*                          
   inf_ov: forall p q, ov p q -> ov p (inf QDBool (bool_family _ p q))
	 properness: ov zero zero -> False;
	 distributivity: forall I p q, id _ (inf QDBool (bool_family _ (sup I p) q)) (sup I (fun i => (inf QDBool (bool_family _ (p i) q))));
*)

inductive pippo : Prop \def
   | Pippo: let x \def zero in zero = x \to pippo.
   
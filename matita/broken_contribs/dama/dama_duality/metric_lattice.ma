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

include "metric_space.ma".
include "lattice.ma".

record mlattice_ (R : todgroup) : Type ≝ {
  ml_mspace_: metric_space R;
  ml_lattice:> lattice;
  ml_with: ms_carr ? ml_mspace_ = Type_OF_lattice ml_lattice 
}.

lemma ml_mspace: ∀R.mlattice_ R → metric_space R.
intros  (R ml); apply (mk_metric_space R (Type_OF_mlattice_ ? ml));
unfold Type_OF_mlattice_; cases (ml_with ? ml); simplify;
[apply (metric ? (ml_mspace_ ? ml));|apply (mpositive ? (ml_mspace_ ? ml));
|apply (mreflexive ? (ml_mspace_ ? ml));|apply (msymmetric ? (ml_mspace_ ? ml));
|apply (mtineq ? (ml_mspace_ ? ml))]
qed.

coercion cic:/matita/metric_lattice/ml_mspace.con.

alias symbol "plus" = "Abelian group plus".
alias symbol "leq" = "Excess less or equal than".
record mlattice (R : todgroup) : Type ≝ {
  ml_carr :> mlattice_ R;
  ml_prop1: ∀a,b:ml_carr. 0 < δ a b → a # b;
  ml_prop2: ∀a,b,c:ml_carr. δ (a∨b) (a∨c) + δ (a∧b) (a∧c) ≤ (δ b c)
}.

interpretation "Metric lattice leq" 'leq a b = 
  (le (excess_OF_mlattice1 _ _) a b). 
interpretation "Metric lattice geq" 'geq a b = 
  (le (excess_OF_mlattice _ _) a b). 

lemma eq_to_ndlt0: ∀R.∀ml:mlattice R.∀a,b:ml. a ≈ b → ¬ 0 < δ a b.
intros (R ml a b E); intro H; apply E; apply ml_prop1;
assumption;
qed.

lemma eq_to_dzero: ∀R.∀ml:mlattice R.∀x,y:ml.x ≈ y → δ x y ≈ 0.
intros (R ml x y H); intro H1; apply H; clear H; 
apply ml_prop1; split [apply mpositive] apply ap_symmetric;
assumption;
qed.

lemma meq_l: ∀R.∀ml:mlattice R.∀x,y,z:ml. x≈z → δx y ≈ δz y.
intros (R ml x y z); apply le_le_eq;
[ apply (le_transitive ???? (mtineq ???y z)); 
  apply (le_rewl ??? (0+δz y) (eq_to_dzero ???? H));
  apply (le_rewl ??? (δz y) (zero_neutral ??)); apply le_reflexive;
| apply (le_transitive ???? (mtineq ???y x));
  apply (le_rewl ??? (0+δx y) (eq_to_dzero ??z x H));
  apply (le_rewl ??? (δx y) (zero_neutral ??)); apply le_reflexive;]
qed.

(* 3.3 *)
lemma meq_r: ∀R.∀ml:mlattice R.∀x,y,z:ml. x≈z → δy x ≈ δy z.
intros; apply (eq_trans ???? (msymmetric ??y x));
apply (eq_trans ????? (msymmetric ??z y)); apply meq_l; assumption;
qed.

lemma dap_to_lt: ∀R.∀ml:mlattice R.∀x,y:ml. δ x y # 0 → 0 < δ x y.
intros; split [apply mpositive] apply ap_symmetric; assumption;
qed.

lemma dap_to_ap: ∀R.∀ml:mlattice R.∀x,y:ml. δ x y # 0 → x # y.
intros (R ml x y H); apply ml_prop1; split; [apply mpositive;]
apply ap_symmetric; assumption;
qed.

(* 3.11 *)
lemma le_mtri: 
  ∀R.∀ml:mlattice R.∀x,y,z:ml. x ≤ y → y ≤ z → δ x z ≈ δ x y + δ y z.
intros (R ml x y z Lxy Lyz); apply le_le_eq; [apply mtineq]
apply (le_transitive ????? (ml_prop2 ?? (y) ??)); 
cut ( δx y+ δy z ≈ δ(y∨x) (y∨z)+ δ(y∧x) (y∧z)); [
  apply (le_rewr ??? (δx y+ δy z)); [assumption] apply le_reflexive]
lapply (le_to_eqm y x Lxy) as Dxm; lapply (le_to_eqm z y Lyz) as Dym;
lapply (le_to_eqj x y Lxy) as Dxj; lapply (le_to_eqj y z Lyz) as Dyj; clear Lxy Lyz;
 STOP 
apply (Eq≈ (δ(x∧y) y + δy z) (meq_l ????? Dxm));
apply (Eq≈ (δ(x∧y) (y∧z) + δy z) (meq_r ????? Dym));
apply (Eq≈ (δ(x∧y) (y∧z) + δ(y∨x) z));[
  apply feq_plusl; apply meq_l; clear Dyj Dxm Dym; assumption]
apply (Eq≈ (δ(x∧y) (y∧z) + δ(y∨x) (z∨y))); [
  apply (feq_plusl ? (δ(x∧y) (y∧z)) ?? (meq_r ??? (y∨x) ? Dyj));]
apply (Eq≈ ? (plus_comm ???));
apply (Eq≈ (δ(y∨x) (y∨z)+ δ(x∧y) (y∧z)));[
  apply feq_plusr; apply meq_r; apply (join_comm ??);]
apply feq_plusl;
apply (Eq≈ (δ(y∧x) (y∧z)) (meq_l ????? (meet_comm ??)));
apply eq_reflexive;   
qed.  


(* 3.17 conclusione: δ x y ≈ 0 *)
(* 3.20 conclusione: δ x y ≈ 0 *)
(* 3.21 sup forte
   strong_sup x ≝ ∀n. s n ≤ x ∧ ∀y x ≰ y → ∃n. s n ≰ y
   strong_sup_zoli x ≝  ∀n. s n ≤ x ∧ ∄y. y#x ∧ y ≤ x
*)
(* 3.22 sup debole (più piccolo dei maggioranti) *)
(* 3.23 conclusion: δ x sup(...) ≈ 0 *)
(* 3.25 vero nel reticolo e basta (niente δ) *)
(* 3.36 conclusion: δ x y ≈ 0 *)

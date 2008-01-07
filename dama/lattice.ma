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



include "excess.ma".

record lattice : Type ≝ {
  l_carr:> apartness;
  join: l_carr → l_carr → l_carr;
  meet: l_carr → l_carr → l_carr;
  join_refl: ∀x.join x x ≈ x;
  meet_refl: ∀x.meet x x ≈ x;  
  join_comm: ∀x,y:l_carr. join x y ≈ join y x;
  meet_comm: ∀x,y:l_carr. meet x y ≈ meet y x;
  join_assoc: ∀x,y,z:l_carr. join x (join y z) ≈ join (join x y) z;
  meet_assoc: ∀x,y,z:l_carr. meet x (meet y z) ≈ meet (meet x y) z;
  absorbjm: ∀f,g:l_carr. join f (meet f g) ≈ f;
  absorbmj: ∀f,g:l_carr. meet f (join f g) ≈ f;
  strong_extj: ∀x.strong_ext ? (join x);
  strong_extm: ∀x.strong_ext ? (meet x)
}.

interpretation "Lattice meet" 'and a b =
 (cic:/matita/lattice/meet.con _ a b).

interpretation "Lattice join" 'or a b =
 (cic:/matita/lattice/join.con _ a b).

definition excl ≝ λl:lattice.λa,b:l.a # (a ∧ b).

lemma excess_of_lattice: lattice → excess.
intro l; apply (mk_excess l (excl l));
[ intro x; unfold; intro H; unfold in H; apply (ap_coreflexive l x);
  apply (ap_rewr ??? (x∧x) (meet_refl l x)); assumption;
| intros 3 (x y z); unfold excl; intro H;
  cases (ap_cotransitive ??? (x∧z∧y) H) (H1 H2); [2:
    left; apply ap_symmetric; apply (strong_extm ? y); 
    apply (ap_rewl ???? (meet_comm ???));
    apply (ap_rewr ???? (meet_comm ???));
    assumption]
  cases (ap_cotransitive ??? (x∧z) H1) (H2 H3); [left; assumption]
  right; apply (strong_extm ? x); apply (ap_rewr ???? (meet_assoc ????));
  assumption]
qed.    

coercion cic:/matita/lattice/excess_of_lattice.con.

lemma feq_ml: ∀ml:lattice.∀a,b,c:ml. a ≈ b → (c ∧ a) ≈ (c ∧ b).
intros (l a b c H); unfold eq in H ⊢ %; unfold Not in H ⊢ %;
intro H1; apply H; clear H; apply (strong_extm ???? H1);
qed.

lemma feq_jl: ∀ml:lattice.∀a,b,c:ml. a ≈ b → (c ∨ a) ≈ (c ∨ b).
intros (l a b c H); unfold eq in H ⊢ %; unfold Not in H ⊢ %;
intro H1; apply H; clear H; apply (strong_extj ???? H1);
qed.

lemma le_to_eqm: ∀ml:lattice.∀a,b:ml. a ≤ b → a ≈ (a ∧ b).
intros (l a b H); 
  unfold le in H; unfold excess_of_lattice in H;
  unfold excl in H; simplify in H; 
unfold eq; assumption;
qed.

lemma le_to_eqj: ∀ml:lattice.∀a,b:ml. a ≤ b → b ≈ (a ∨ b).
intros (l a b H); lapply (le_to_eqm ??? H) as H1;
lapply (feq_jl ??? b H1) as H2;
apply (Eq≈ ?? (join_comm ???));
apply (Eq≈ (b∨a∧b) ? H2); clear H1 H2 H;
apply (Eq≈ (b∨(b∧a)) ? (feq_jl ???? (meet_comm ???)));
apply eq_sym; apply absorbjm;
qed.




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



include "nat/plus.ma".
include "nat/orders.ma".

lemma ltwl: ∀a,b,c:nat. b + a < c → a < c.
intros 3 (x y z); elim y (H z IH H); [apply H]
apply IH; apply lt_S_to_lt; apply H;
qed.

lemma ltwr: ∀a,b,c:nat. a + b < c → a < c.
intros 3 (x y z); rewrite > sym_plus; apply ltwl;
qed. 

include "sequence.ma".
include "metric_lattice.ma".

definition d2s ≝ 
  λR.λml:mlattice R.λs:sequence ml.λk.λn. δ (s n) k.

notation "s ⇝ x" non associative with precedence 50 for @{'tends $s $x}.
  
interpretation "tends to" 'tends s x = 
  (cic:/matita/sequence/tends0.con _ (cic:/matita/sandwich/d2s.con _ _ s x)).
    
alias symbol "and" = "constructive and".
theorem sandwich:
  ∀R.∀ml:mlattice R.∀an,bn,xn:sequence ml.∀x:ml.
    (∀n. (an n ≤ xn n) ∧ (xn n ≤ bn n)) → 
    an ⇝ x → bn ⇝ x → xn ⇝ x.
intros (R ml an bn xn x H Ha Hb); 
unfold tends0 in Ha Hb ⊢ %; unfold d2s in Ha Hb ⊢ %; intros (e He);
alias num (instance 0) = "natural number".
cases (Ha (e/2) (divide_preserves_lt ??? He)) (n1 H1); clear Ha; 
cases (Hb (e/2) (divide_preserves_lt ??? He)) (n2 H2); clear Hb;
apply (ex_introT ?? (n1+n2)); intros (n3 Lt_n1n2_n3);
lapply (ltwr ??? Lt_n1n2_n3) as Lt_n1n3; lapply (ltwl ??? Lt_n1n2_n3) as Lt_n2n3;
cases (H1 ? Lt_n1n3) (c daxe); cases (H2 ? Lt_n2n3) (c dbxe); 
cases (H n3) (H7 H8); clear Lt_n1n3 Lt_n2n3 Lt_n1n2_n3 c H1 H2 H n1 n2;     
(* the main inequality *)
cut (δ (xn n3) x ≤ δ (bn n3) x + δ (an n3) x + δ (an n3) x) as main_ineq; [2:
  apply (le_transitive ???? (mtineq ???? (an n3)));
  cut ( δ(an n3) (bn n3)+- δ(xn n3) (bn n3)≈( δ(an n3) (xn n3))) as H11; [2:
    lapply (le_mtri ????? H7 H8) as H9; clear H7 H8;
    lapply (feq_plusr ? (- δ(xn n3) (bn n3)) ?? H9) as H10; clear H9;
    apply (Eq≈ (0 + δ(an n3) (xn n3)) ? (zero_neutral ??));
    apply (Eq≈ (δ(an n3) (xn n3) + 0) ? (plus_comm ???));
    apply (Eq≈ (δ(an n3) (xn n3) + (-δ(xn n3) (bn n3) +  δ(xn n3) (bn n3))) ? (opp_inverse ??));
    apply (Eq≈ (δ(an n3) (xn n3) + (δ(xn n3) (bn n3) + -δ(xn n3) (bn n3))) ? (plus_comm ?? (δ(xn n3) (bn n3))));
    apply (Eq≈ ?? (eq_sym ??? (plus_assoc ????))); assumption;]
  apply (Le≪ (δ(an n3) (xn n3)+ δ(an n3) x) (msymmetric ??(an n3)(xn n3)));    
  apply (Le≪ (δ(an n3) (bn n3)+- δ(xn n3) (bn n3)+ δ(an n3) x) H11);
  apply (Le≪ (- δ(xn n3) (bn n3)+ δ(an n3) (bn n3)+δ(an n3) x) (plus_comm ??(δ(an n3) (bn n3))));
  apply (Le≪ (- δ(xn n3) (bn n3)+ (δ(an n3) (bn n3)+δ(an n3) x)) (plus_assoc ????));
  apply (Le≪ ((δ(an n3) (bn n3)+δ(an n3) x)+- δ(xn n3) (bn n3)) (plus_comm ???));
  apply lew_opp; [apply mpositive] apply fle_plusr;
  apply (Le≫ ? (plus_comm ???));
  apply (Le≫ ( δ(an n3) x+ δx (bn n3)) (msymmetric ????));
  apply mtineq;]
split; [ (* first the trivial case: -e< δ(xn n3) x *)
  apply (lt_le_transitive ????? (mpositive ????));
  apply lt_zero_x_to_lt_opp_x_zero; assumption;]
(* the main goal: δ(xn n3) x<e *)
apply (le_lt_transitive ???? main_ineq);
apply (Lt≫ (e/2+e/2+e/2)); [apply (divpow ?e 2)]
repeat (apply ltplus; try assumption);
qed.

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

include "tend.ma".
include "metric_lattice.ma".

alias symbol "leq" = "ordered sets less or equal than".
alias symbol "and" = "constructive and".
theorem sandwich:
let ugo ≝ excess_OF_lattice1 in
  ∀R.∀ml:mlattice R.∀an,bn,xn:sequence ml.∀x:ml.
    (∀n. (xn n ≤ an n) ∧ (bn n ≤ xn n)) →  
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
    lapply (le_mtri ?? ??? H8 H7) as H9; clear H7 H8;
    lapply (Eq≈ ? (msymmetric ????) H9) as H10; clear H9;
    lapply (feq_plusr ? (- δ(xn n3) (bn n3)) ?? H10) as H9; clear H10;
    apply (Eq≈ ? H9); clear H9;
    apply (Eq≈ (δ(xn n3) (an n3)+ δ(bn n3) (xn n3)+- δ(xn n3) (bn n3)) (plus_comm ??( δ(xn n3) (an n3))));
    apply (Eq≈ (δ(xn n3) (an n3)+ δ(bn n3) (xn n3)+- δ(bn n3) (xn n3)) (feq_opp ??? (msymmetric ????)));    
    apply (Eq≈ ( δ(xn n3) (an n3)+ (δ(bn n3) (xn n3)+- δ(bn n3) (xn n3))) (plus_assoc ????));
    apply (Eq≈ (δ(xn n3) (an n3) + (- δ(bn n3) (xn n3) + δ(bn n3) (xn n3))) (plus_comm ??(δ(bn n3) (xn n3))));
    apply (Eq≈ (δ(xn n3) (an n3) + 0) (opp_inverse ??));
    apply (Eq≈ ? (plus_comm ???));
    apply (Eq≈ ? (zero_neutral ??));
    apply (Eq≈ ? (msymmetric ????));
    apply eq_reflexive;]
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

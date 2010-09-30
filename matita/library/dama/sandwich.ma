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

include "dama/ordered_uniform.ma".

lemma le_w_plus: ∀n,m,o.n+m≤o → m ≤ o.
intro; elim n; simplify; [assumption]
lapply (le_S ?? H1); apply H; apply le_S_S_to_le; assumption;
qed.

alias symbol "leq" = "Ordered set less or equal than".
alias symbol "and" = "logical and".
theorem sandwich: 
  ∀O:ordered_uniform_space.∀l:O.∀a,b,x:sequence O.
   (∀i:nat.a i ≤ x i ∧ x i ≤ b i) →
    a uniform_converges l → 
     b uniform_converges l → 
      x uniform_converges l.
intros 10; 
cases (us_phi3 ? ? H3) (V GV); cases GV (Gv HV); clear GV;
cases (us_phi3 ? ? Gv) (W GW); cases GW (Gw HW); clear GW;
cases (H1 ? Gw) (ma Hma); cases (H2 ? Gw) (mb Hmb); clear H1 H2;
exists [apply (ma + mb)] intros; apply (HV 〈l,(x i)〉); 
unfold; simplify; exists [apply (a i)] split;
[2: apply (ous_convex_l ?? Gv 〈a i,b i〉); cases (H i) (Lax Lxb); clear H;
    [1: apply HW; exists [apply l]simplify; split; 
        [1: cases (us_phi4 ?? Gw 〈(a i),l〉); apply H2; clear H2 H;
            apply (Hma i); rewrite > sym_plus in H1; apply (le_w_plus mb); assumption;
        |2: apply Hmb; apply (le_w_plus ma); assumption] 
    |2,3: simplify; apply (le_transitive (a i) ?? Lax Lxb);
    |4: apply (le_reflexive);
    |5,6: assumption;]
|1: apply HW; exists[apply l] simplify; split;
    [1: apply (us_phi1 ?? Gw); unfold; apply eq_reflexive;
    |2: apply Hma;  rewrite > sym_plus in H1; apply (le_w_plus mb); assumption;]]
qed. 
 

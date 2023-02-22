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

include "dama/uniform.ma".
include "dama/bishop_set_rewrite.ma".

definition discrete_uniform_space_of_bishop_set:bishop_set → uniform_space.
intro C; apply (mk_uniform_space C);
[1: intro; 
    alias symbol "pi2" = "pair pi2".
    alias symbol "pi1" = "pair pi1".
    alias symbol "and" = "logical and".
    apply (∃d:unit.∀n:C squareB.(\fst n ≈ \snd n → P n) ∧ (P n → \fst n ≈ \snd n)); 
|2: intros 4 (U H x Hx); simplify in Hx;
    cases H (_ H1); cases (H1 x); apply H2; apply Hx;
|3: intros; cases H (_ PU); cases H1 (_ PV); 
    exists[apply (λx.U x ∧ V x)] split;
    [1: exists[apply something] intro; cases (PU n); cases (PV n);
        split; intros; try split;[apply H2;|apply H4] try assumption;
        apply H3; cases H6; assumption;
    |2: simplify; intros; assumption;]
|4: intros; cases H (_ PU); exists [apply U] split;
    [1: exists [apply something] intro n; cases (PU n);
        split; intros; try split;[apply H1;|apply H2] assumption;
    |2: intros 2 (x Hx); cases Hx; cases H1; clear H1;
        cases (PU 〈(\fst x),x1〉); lapply (H4 H2) as H5; simplify in H5;
        cases (PU 〈x1,(\snd x)〉); lapply (H7 H3) as H8; simplify in H8;
        generalize in match H5; generalize in match H8;
        generalize in match (PU x); clear H6 H7 H1 H4 H2 H3 H5 H8; 
        cases x; simplify; intros; cases H1; clear H1; apply H4;
        apply (eq_trans ???? H3 H2);]
|5: intros; cases H (_ H1); split; cases x; 
    [2: cases (H1 〈b,b1〉); intro; apply H2; cases (H1 〈b1,b〉);
        lapply (H6 H4) as H7; apply eq_sym; apply H7; 
    |1: cases (H1 〈b1,b〉); intro; apply H2; cases (H1 〈b,b1〉);
        lapply (H6 H4) as H7; apply eq_sym; apply H7;]] 
qed.        

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

include "dama/sandwich.ma".
include "dama/property_exhaustivity.ma".

(* NOT DUALIZED *)
alias symbol "low" = "lower".
alias id "le" = "cic:/matita/dama/ordered_set/le.con".
lemma order_converges_bigger_lowsegment:
  ∀C:ordered_set.
   ∀a:sequence (os_l C).∀s:segment C.∀H:∀i:nat.a i ∈ s. 
     ∀x:C.∀p:order_converge C a x. 
       ∀j. 𝕝_ s ≤ (pi1exT23 ???? p j).
intros; cases p (xi yi Ux Dy Hxy); clear p; simplify; 
cases Ux (Ixi Sxi); clear Ux; cases Dy (Dyi Iyi); clear Dy;
cases (Hxy j) (Ia Sa); clear Hxy; cases Ia (Da SSa); cases Sa (Inca SIa); clear Ia Sa;
intro H2; cases (SSa 𝕝_ s H2) (w Hw); simplify in Hw;
lapply (H (w+j)) as K; cases (cases_in_segment ? s ? K); apply H3; apply Hw;
qed.   
  
alias symbol "upp" = "uppper".
alias symbol "leq" = "Ordered set less or equal than".
lemma order_converges_smaller_upsegment:
  ∀C:ordered_set.
   ∀a:sequence (os_l C).∀s:segment C.∀H:∀i:nat.a i ∈ s. 
     ∀x:C.∀p:order_converge C a x. 
       ∀j. (pi2exT23 ???? p j) ≤ 𝕦_ s.
intros; cases p (xi yi Ux Dy Hxy); clear p; simplify; 
cases Ux (Ixi Sxi); clear Ux; cases Dy (Dyi Iyi); clear Dy;
cases (Hxy j) (Ia Sa); clear Hxy; cases Ia (Da SSa); cases Sa (Inca SIa); clear Ia Sa;
intro H2; cases (SIa 𝕦_ s H2) (w Hw); lapply (H (w+j)) as K; 
cases (cases_in_segment ? s ? K); apply H1; apply Hw;  
qed. 

(* Theorem 3.10 *)
theorem lebesgue_oc:
  ∀C:ordered_uniform_space.
   (∀s:‡C.order_continuity {[s]}) →
    ∀a:sequence C.∀s:‡C.∀H:∀i:nat.a i ∈ s. 
     ∀x:C.a order_converges x → 
      x ∈ s ∧ 
      ∀h:x ∈ s.
       uniform_converge {[s]} (⌊n,≪a n,H n≫⌋) ≪x,h≫.
intros; 
generalize in match (order_converges_bigger_lowsegment ? a s H1 ? H2);
generalize in match (order_converges_smaller_upsegment ? a s H1 ? H2);
cases H2 (xi yi Hx Hy Hxy); clear H2; simplify in ⊢ ((?→???%) → (?→???%) → ?); intros;
cut (∀i.xi i ∈ s) as Hxi; [2:
  intros; apply (prove_in_segment (os_l C)); [apply (H3 i)] cases (Hxy i) (H5 _); cases H5 (H7 _);
  lapply (H7 0) as K; cases (cases_in_segment ? s ? (H1 i)) (Pl Pu);
  simplify in K:(? ? % ?); apply (hle_transitive (os_l C) (xi i) (a i) 𝕦_ s K Pu);] clear H3;
cut (∀i.yi i ∈ s) as Hyi; [2:
  intros; apply (prove_in_segment (os_l C)); [2:apply (H2 i)] cases (Hxy i) (_ H5); cases H5 (H7 _);
  lapply (H7 0) as K; cases (cases_in_segment ? s ? (H1 i)) (Pl Pu); simplify in K;
  apply (le_transitive 𝕝_ s ? ? ? K);apply Pl;] clear H2;
split;
[1: apply (uparrow_to_in_segment s ? Hxi ? Hx);
|2: intros 3 (h);
    letin Xi ≝ (⌊n,≪xi n, Hxi n≫⌋);
    letin Yi ≝ (⌊n,≪yi n, Hyi n≫⌋);
    letin Ai ≝ (⌊n,≪a n, H1 n≫⌋); 
    apply (sandwich {[s]} ≪x, h≫ Xi Yi Ai); [4: assumption;]
    [1: intro j; cases (Hxy j); cases H3; cases H4; split; clear H3 H4; simplify in H5 H7;
        [apply (l2sl_ ? s (Xi j) (Ai j) (H5 0));|apply (l2sl_ ? s (Ai j) (Yi j) (H7 0))]
    |2: cases (H s Xi ≪?,h≫) (Ux Uy); apply Ux; cases Hx; split; [intro i; apply (l2sl_ ? s (Xi i) (Xi (S i)) (H3 i));]
        cases H4; split; [intro i; apply (l2sl_ ? s (Xi i) ≪x,h≫ (H5 i))] 
        intros (y Hy);cases (H6 (\fst y));[2:apply (sx2x_ ? s ? y Hy)]
        exists [apply w] apply (x2sx_ ? s (Xi w) y H7); 
    |3: cases (H s Yi ≪?,h≫) (Ux Uy); apply Uy; cases Hy; split; [intro i; apply (l2sl_ ? s (Yi (S i))  (Yi i) (H3 i));]
        cases H4; split; [intro i; apply (l2sl_ ? s ≪x,h≫ (Yi i) (H5 i))]
        intros (y Hy);cases (H6 (\fst y));[2:apply (sx2x_ ? s y ≪x,h≫ Hy)]
        exists [apply w] apply (x2sx_ ? s y (Yi w) H7);]]
qed.
 

(* Theorem 3.9 *)
theorem lebesgue_se:
  ∀C:ordered_uniform_space.property_sigma C →
   (∀s:‡C.exhaustive {[s]}) →
    ∀a:sequence C.∀s:‡C.∀H:∀i:nat.a i ∈ s. 
     ∀x:C.a order_converges x → 
      x ∈ s ∧ 
      ∀h:x ∈ s.
       uniform_converge {[s]} (⌊n,≪a n,H n≫⌋) ≪x,h≫.
intros (C S);
generalize in match (order_converges_bigger_lowsegment ? a s H1 ? H2);
generalize in match (order_converges_smaller_upsegment ? a s H1 ? H2);
cases H2 (xi yi Hx Hy Hxy); clear H2; simplify in ⊢ ((?→???%) → (?→???%) → ?); intros;
cut (∀i.xi i ∈ s) as Hxi; [2:
  intros; apply (prove_in_segment (os_l C)); [apply (H3 i)] cases (Hxy i) (H5 _); cases H5 (H7 _);
  lapply (H7 0) as K; cases (cases_in_segment ? s ? (H1 i)) (Pl Pu);
  simplify in K:(? ? % ?); apply (hle_transitive (os_l C) (xi i) (a i) 𝕦_ s K Pu);] clear H3;
cut (∀i.yi i ∈ s) as Hyi; [2:
  intros; apply (prove_in_segment (os_l C)); [2:apply (H2 i)] cases (Hxy i) (_ H5); cases H5 (H7 _);
  lapply (H7 0) as K; cases (cases_in_segment ? s ? (H1 i)) (Pl Pu); simplify in K;
  apply (le_transitive 𝕝_ s ? ? ? K);apply Pl;] clear H2;
letin Xi ≝ (⌊n,≪xi n, Hxi n≫⌋);
letin Yi ≝ (⌊n,≪yi n, Hyi n≫⌋);
cases (restrict_uniform_convergence_uparrow ? S ? (H s) Xi x Hx);
cases (restrict_uniform_convergence_downarrow ? S ? (H s) Yi x Hy);
split; [1: assumption]
intros 3;
lapply (uparrow_upperlocated  xi x Hx)as Ux;
lapply (downarrow_lowerlocated  yi x Hy)as Uy;
letin Ai ≝ (⌊n,≪a n, H1 n≫⌋);
apply (sandwich {[s]} ≪x, h≫ Xi Yi Ai); [4: assumption;|2:apply H3;|3:apply H5]
intro j; cases (Hxy j); cases H7; cases H8; split;
[apply (l2sl_ ? s (Xi j) (Ai j) (H9 0));|apply (l2sl_ ? s (Ai j) (Yi j) (H11 0))]
qed. 




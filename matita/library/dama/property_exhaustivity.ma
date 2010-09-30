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
include "dama/property_sigma.ma".

lemma h_segment_upperbound:
  ∀C:half_ordered_set.
   ∀s:segment C.
    ∀a:sequence (half_segment_ordered_set C s).
      upper_bound ? ⌊n,\fst (a n)⌋ (seg_u C s). 
intros 4; simplify; cases (a n); simplify; unfold in H;
cases (wloss_prop C); rewrite < H1 in H; simplify; cases H; 
assumption;
qed.

notation "'segment_upperbound'" non associative with precedence 90 for @{'segment_upperbound}.
notation "'segment_lowerbound'" non associative with precedence 90 for @{'segment_lowerbound}.

interpretation "segment_upperbound" 'segment_upperbound = (h_segment_upperbound (os_l ?)).
interpretation "segment_lowerbound" 'segment_lowerbound = (h_segment_upperbound (os_r ?)).

lemma h_segment_preserves_uparrow:
  ∀C:half_ordered_set.∀s:segment C.∀a:sequence (half_segment_ordered_set C s).
   ∀x,h. uparrow C ⌊n,\fst (a n)⌋ x → uparrow (half_segment_ordered_set C s) a ≪x,h≫.
intros; cases H (Ha Hx); split;
[ intro n; intro H; apply (Ha n); apply rule H;
| cases Hx; split; 
  [ intro n; intro H; apply (H1 n);apply rule H; 
  | intros; cases (H2 (\fst y)); [2: apply rule H3;] 
    exists [apply w] apply (x2sx_ ?? (a w) y H4);]]
qed.

notation "'segment_preserves_uparrow'" non associative with precedence 90 for @{'segment_preserves_uparrow}.
notation "'segment_preserves_downarrow'" non associative with precedence 90 for @{'segment_preserves_downarrow}.

interpretation "segment_preserves_uparrow" 'segment_preserves_uparrow = (h_segment_preserves_uparrow (os_l ?)).
interpretation "segment_preserves_downarrow" 'segment_preserves_downarrow = (h_segment_preserves_uparrow (os_r ?)).
 
(* Fact 2.18 *)
lemma segment_cauchy:
  ∀C:ordered_uniform_space.∀s:‡C.∀a:sequence {[s]}.
    a is_cauchy → ⌊n,\fst (a n)⌋ is_cauchy.
intros 6; 
alias symbol "pi1" (instance 3) = "pair pi1".
alias symbol "pi2" = "pair pi2".
apply (H (λx:{[s]} squareB.U 〈\fst (\fst x),\fst (\snd x)〉));
(unfold segment_ordered_uniform_space; simplify);
exists [apply U] split; [assumption;]
intro; cases b; intros; simplify; split; intros; assumption;
qed.       

(* Definition 3.7 *)
definition exhaustive ≝
  λC:ordered_uniform_space.
   ∀a,b:sequence C.
     (a is_increasing → a is_upper_located → a is_cauchy) ∧
     (b is_decreasing → b is_lower_located → b is_cauchy).

lemma h_uparrow_to_in_segment:
  ∀C:half_ordered_set.
   ∀s:segment C.
     ∀a:sequence C.
      (∀i.a i ∈ s) →
       ∀x:C. uparrow C a x → 
         in_segment C s x.
intros (C H a H1 x H2); unfold in H2; cases H2; clear H2;unfold in H3 H4; cases H4; clear H4; unfold in H2;
cases (wloss_prop C) (W W); apply prove_in_segment; unfold; 
[ apply (hle_transitive ??? x ? (H2 O)); lapply (H1 O) as K; unfold in K; rewrite <W in K;
  cases K; unfold in H4 H6; apply H4;
| intro; cases (H5 ? H4); clear H5 H4;lapply(H1 w) as K; unfold in K; rewrite<W in K;
  cases K; unfold in H5 H4; apply H5; apply H6;    
| apply (hle_transitive ??? x ?  (H2 O)); lapply (H1 0) as K; unfold in K; rewrite <W in K;
  cases K; unfold in H4 H6; apply H6;
| intro; cases (H5 ? H4); clear H5 H4;lapply(H1 w) as K; unfold in K; rewrite<W in K;
  cases K; unfold in H5 H4; apply (H4 H6);]    
qed.

notation "'uparrow_to_in_segment'" non associative with precedence 90 for @{'uparrow_to_in_segment}.
notation "'downarrow_to_in_segment'" non associative with precedence 90 for @{'downarrow_to_in_segment}.

interpretation "uparrow_to_in_segment" 'uparrow_to_in_segment = (h_uparrow_to_in_segment (os_l ?)).
interpretation "downarrow_to_in_segment" 'downarrow_to_in_segment = (h_uparrow_to_in_segment (os_r ?)).
 
alias symbol "dependent_pair" = "dependent pair".
(* Lemma 3.8 NON DUALIZZATO *)
lemma restrict_uniform_convergence_uparrow:
  ∀C:ordered_uniform_space.property_sigma C →
    ∀s:segment (os_l C).exhaustive (segment_ordered_uniform_space C s) →
     ∀a:sequence (segment_ordered_uniform_space C s).
      ∀x:C. ⌊n,\fst (a n)⌋ ↑ x → 
       in_segment (os_l C) s x ∧ ∀h:x ∈ s.a uniform_converges ≪x,h≫.
intros; split;
[1: apply (uparrow_to_in_segment s ⌊n,\fst (a \sub n)⌋ ? x H2); 
    simplify; intros; cases (a i); assumption;
|2: intros;
    lapply (uparrow_upperlocated a ≪x,h≫) as Ha1;
      [2: apply (segment_preserves_uparrow s); assumption;]
    lapply (segment_preserves_supremum s a ≪?,h≫ H2) as Ha2; 
    cases Ha2; clear Ha2;
    cases (H1 a a); lapply (H5 H3 Ha1) as HaC;
    lapply (segment_cauchy C s ? HaC) as Ha;
    lapply (sigma_cauchy ? H  ? x ? Ha); [left; assumption]
    apply (restric_uniform_convergence C s ≪?,h≫ a Hletin)]
qed.

lemma hint_mah1:
  ∀C. Type_OF_ordered_uniform_space__1 C → hos_carr (os_r C).
  intros; assumption; qed.
  
coercion hint_mah1 nocomposites.

lemma hint_mah2:
  ∀C. sequence (hos_carr (os_l C)) → sequence (hos_carr (os_r C)).
  intros; assumption; qed.
  
coercion hint_mah2 nocomposites.

lemma hint_mah3:
  ∀C. Type_OF_ordered_uniform_space C → hos_carr (os_r C).
  intros; assumption; qed.
  
coercion hint_mah3 nocomposites.
    
lemma hint_mah4:
  ∀C. sequence (hos_carr (os_r C)) → sequence (hos_carr (os_l C)).
  intros; assumption; qed.
  
coercion hint_mah4 nocomposites.

lemma hint_mah5:
  ∀C. segment (hos_carr (os_r C)) → segment (hos_carr (os_l C)).
  intros; assumption; qed.
  
coercion hint_mah5 nocomposites.

lemma hint_mah6:
  ∀C. segment (hos_carr (os_l C)) → segment (hos_carr (os_r C)).
  intros; assumption; qed.

coercion hint_mah6 nocomposites.

lemma restrict_uniform_convergence_downarrow:
  ∀C:ordered_uniform_space.property_sigma C →
    ∀s:segment (os_l C).exhaustive (segment_ordered_uniform_space C s) →
     ∀a:sequence (segment_ordered_uniform_space C s).
      ∀x:C. ⌊n,\fst (a n)⌋ ↓ x → 
       in_segment (os_l C) s x ∧ ∀h:x ∈ s.a uniform_converges ≪x,h≫.
intros; split;       
[1: apply (downarrow_to_in_segment s ⌊n,\fst (a n)⌋ ? x); [2: apply H2]; 
    simplify; intros; cases (a i); assumption;
|2: intros;
    lapply (downarrow_lowerlocated a ≪x,h≫) as Ha1;
      [2: apply (segment_preserves_downarrow s a x h H2);] 
    lapply (segment_preserves_infimum s a ≪?,h≫ H2) as Ha2; 
    cases Ha2; clear Ha2;
    cases (H1 a a); lapply (H6 H3 Ha1) as HaC;
    lapply (segment_cauchy C s ? HaC) as Ha;
    lapply (sigma_cauchy ? H  ? x ? Ha); [right; assumption]
    apply (restric_uniform_convergence C s ≪x,h≫ a Hletin)]
qed.

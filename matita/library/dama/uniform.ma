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

include "dama/supremum.ma".

(* Definition 2.13 *)
alias symbol "pair" = "Pair construction".
alias symbol "exists" = "exists".
alias symbol "and" = "logical and".
definition compose_bs_relations ≝
  λC:bishop_set.λU,V:C squareB → Prop.
   λx:C squareB.∃y:C. U 〈\fst x,y〉 ∧ V 〈y,\snd x〉.
   
definition compose_os_relations ≝
  λC:ordered_set.λU,V:C squareB → Prop.
   λx:C squareB.∃y:C. U 〈\fst x,y〉 ∧ V 〈y,\snd x〉.
   
interpretation "bishop set relations composition" 'compose a b = (compose_bs_relations ? a b).
interpretation "ordered set relations composition" 'compose a b = (compose_os_relations ? a b).

definition invert_bs_relation ≝
  λC:bishop_set.λU:C squareB → Prop.
    λx:C squareB. U 〈\snd x,\fst x〉.
      
notation > "\inv" with precedence 65 for @{ 'invert_symbol  }.
interpretation "relation invertion" 'invert a = (invert_bs_relation ? a).
interpretation "relation invertion" 'invert_symbol = (invert_bs_relation ?).
interpretation "relation invertion" 'invert_appl a x = (invert_bs_relation ? a x).

alias symbol "exists" = "CProp exists".
alias symbol "compose" = "bishop set relations composition".
alias symbol "and" (instance 21) = "constructive and".
alias symbol "and" (instance 16) = "constructive and".
alias symbol "and" (instance 9) = "constructive and".
record uniform_space : Type ≝ {
  us_carr:> bishop_set;
  us_unifbase: (us_carr squareB → Prop) → CProp;
  us_phi1: ∀U:us_carr squareB → Prop. us_unifbase U → 
    (λx:us_carr squareB.\fst x ≈ \snd x) ⊆ U;
  us_phi2: ∀U,V:us_carr squareB → Prop. us_unifbase U → us_unifbase V →
    ∃W:us_carr squareB → Prop.us_unifbase W ∧ (W ⊆ (λx.U x ∧ V x));
  us_phi3: ∀U:us_carr squareB → Prop. us_unifbase U → 
    ∃W:us_carr squareB → Prop.us_unifbase W ∧ (W ∘ W) ⊆ U;
  us_phi4: ∀U:us_carr squareB → Prop. us_unifbase U → ∀x.(U x → (\inv U) x) ∧ ((\inv U) x → U x)
}.

(* Definition 2.14 *)  
alias symbol "leq" = "natural 'less or equal to'".
definition cauchy ≝
  λC:uniform_space.λa:sequence C.∀U.us_unifbase C U → 
   ∃n. ∀i,j. n ≤ i → n ≤ j → U 〈a i,a j〉.
   
notation < "a \nbsp 'is_cauchy'" non associative with precedence 45 
  for @{'cauchy $a}.
notation > "a 'is_cauchy'" non associative with precedence 45 
  for @{'cauchy $a}.
interpretation "Cauchy sequence" 'cauchy s = (cauchy ? s).  
   
(* Definition 2.15 *)  
definition uniform_converge ≝
  λC:uniform_space.λa:sequence C.λu:C.
    ∀U.us_unifbase C U →  ∃n. ∀i. n ≤ i → U 〈u,a i〉.
    
notation < "a \nbsp (\u \atop (\horbar\triangleright)) \nbsp x" non associative with precedence 45 
  for @{'uniform_converge $a $x}.
notation > "a 'uniform_converges' x" non associative with precedence 45 
  for @{'uniform_converge $a $x}.
interpretation "Uniform convergence" 'uniform_converge s u =
 (uniform_converge ? s u).
 
(* Lemma 2.16 *)
lemma uniform_converge_is_cauchy : 
  ∀C:uniform_space.∀a:sequence C.∀x:C.
   a uniform_converges x → a is_cauchy. 
intros (C a x Ha); intros 2 (u Hu);
cases (us_phi3 ?? Hu) (v Hv0); cases Hv0 (Hv H); clear Hv0;
cases (Ha ? Hv) (n Hn); exists [apply n]; intros;
apply H; unfold; exists [apply x]; split [2: apply (Hn ? H2)]
cases (us_phi4 ?? Hv 〈a i,x〉) (P1 P2); apply P2;
apply (Hn ? H1);
qed.

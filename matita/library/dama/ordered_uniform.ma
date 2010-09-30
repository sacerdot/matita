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

record ordered_uniform_space_ : Type ≝ {
  ous_os:> ordered_set;
  ous_us_: uniform_space;
  with_ : us_carr ous_us_ = bishop_set_of_ordered_set ous_os
}.

lemma ous_unifspace: ordered_uniform_space_ → uniform_space.
intro X; apply (mk_uniform_space (bishop_set_of_ordered_set X));
unfold bishop_set_OF_ordered_uniform_space_;
[1: rewrite < (with_ X); simplify; apply (us_unifbase (ous_us_ X));
|2: cases (with_ X); simplify; apply (us_phi1 (ous_us_ X));
|3: cases (with_ X); simplify; apply (us_phi2 (ous_us_ X));
|4: cases (with_ X); simplify; apply (us_phi3 (ous_us_ X));
|5: cases (with_ X); simplify; apply (us_phi4 (ous_us_ X))]
qed.

coercion ous_unifspace.

record ordered_uniform_space : Type ≝ {
  ous_stuff :> ordered_uniform_space_;
  ous_convex_l: ∀U.us_unifbase ous_stuff U → convex (os_l ous_stuff) U;
  ous_convex_r: ∀U.us_unifbase ous_stuff U → convex (os_r ous_stuff) U
}.   

definition half_ordered_set_OF_ordered_uniform_space : ordered_uniform_space → half_ordered_set.
intro; compose ordered_set_OF_ordered_uniform_space with os_l. apply (f o);
qed.

definition invert_os_relation ≝
  λC:ordered_set.λU:C squareO → Prop.
    λx:C squareO. U 〈\snd x,\fst x〉.

interpretation "relation invertion" 'invert a = (invert_os_relation ? a).
interpretation "relation invertion" 'invert_symbol = (invert_os_relation ?).
interpretation "relation invertion" 'invert_appl a x = (invert_os_relation ? a x).

lemma hint_segment: ∀O.
 segment (Type_of_ordered_set O) →
 segment (hos_carr (os_l O)).
intros; assumption;
qed.

coercion hint_segment nocomposites.

lemma segment_square_of_ordered_set_square: 
  ∀O:ordered_set.∀s:‡O.∀x:O squareO.
   \fst x ∈ s → \snd x ∈ s → {[s]} squareO.
intros; split; exists; [1: apply (\fst x) |3: apply (\snd x)] assumption;
qed.

coercion segment_square_of_ordered_set_square with 0 2 nocomposites.

alias symbol "pi1" (instance 4) = "exT \fst".
alias symbol "pi1" (instance 2) = "exT \fst".
lemma ordered_set_square_of_segment_square : 
 ∀O:ordered_set.∀s:‡O.{[s]} squareO → O squareO ≝ 
  λO:ordered_set.λs:‡O.λb:{[s]} squareO.〈\fst(\fst b),\fst(\snd b)〉.

coercion ordered_set_square_of_segment_square nocomposites.

lemma restriction_agreement : 
  ∀O:ordered_uniform_space.∀s:‡O.∀P:{[s]} squareO → Prop.∀OP:O squareO → Prop.Prop.
apply(λO:ordered_uniform_space.λs:‡O.
       λP:{[s]} squareO → Prop. λOP:O squareO → Prop.
          ∀b:{[s]} squareO.(P b → OP b) ∧ (OP b → P b));
qed.

lemma unrestrict: ∀O:ordered_uniform_space.∀s:‡O.∀U,u.∀x:{[s]} squareO.
  restriction_agreement ? s U u → U x → u x.
intros 6; cases (H x); assumption;
qed.

lemma restrict: ∀O:ordered_uniform_space.∀s:‡O.∀U,u.∀x:{[s]} squareO.
  restriction_agreement ? s U u → u x → U x.
intros 6; cases (H x); assumption;
qed.

lemma invert_restriction_agreement: 
  ∀O:ordered_uniform_space.∀s:‡O.
   ∀U:{[s]} squareO → Prop.∀u:O squareO → Prop.
    restriction_agreement ? s U u →
    restriction_agreement ? s (\inv U) (\inv u).
intros 6; cases b;
generalize in match (H 〈h1,h〉); cases h; cases h1; simplify; 
intro X; cases X; split; assumption; 
qed. 

lemma bs2_of_bss2: 
 ∀O:ordered_set.∀s:‡O.(bishop_set_of_ordered_set {[s]}) squareB → (bishop_set_of_ordered_set O) squareB ≝ 
  λO:ordered_set.λs:‡O.λb:{[s]} squareO.〈\fst(\fst b),\fst(\snd b)〉.

coercion bs2_of_bss2 nocomposites.


lemma a2sa :
 ∀O:ordered_uniform_space.∀s:‡(ordered_set_OF_ordered_uniform_space O).
 ∀x:
  bs_carr
  (square_bishop_set
   (bishop_set_of_ordered_set
     (segment_ordered_set 
       (ordered_set_OF_ordered_uniform_space O) s))).
 (\fst x) ≈ (\snd x) →
 (\fst (bs2_of_bss2 (ordered_set_OF_ordered_uniform_space O) s x))
 ≈
 (\snd (bs2_of_bss2 (ordered_set_OF_ordered_uniform_space O) s x)).
intros 3; cases x (a b); clear x; simplify in match (\fst ?);
simplify in match (\snd ?); intros 2 (K H); apply K; clear K;
cases H; 
[ left; change in H1:(? ? % ?) with (\fst a); 
        change in H1:(? ? ? %) with (\fst b); 
        change in a with (hos_carr (half_segment_ordered_set ? s));
        change in b with (hos_carr (half_segment_ordered_set ? s));
        apply rule (x2sx_ ? s ?? H1);
| right; change in H1:(? ? % ?) with (\fst b); 
        change in H1:(? ? ? %) with (\fst a); 
        change in a with (hos_carr (half_segment_ordered_set ? s));
        change in b with (hos_carr (half_segment_ordered_set ? s));
        apply rule (x2sx_ ? s ?? H1);]
qed.


lemma segment_ordered_uniform_space: 
  ∀O:ordered_uniform_space.∀s:‡O.ordered_uniform_space.
intros (O s); apply mk_ordered_uniform_space;
[1: apply (mk_ordered_uniform_space_ {[s]});
    [1: alias symbol "and" = "constructive and".
        letin f ≝ (λP:{[s]} squareO → Prop. ∃OP:O squareO → Prop.
                    (us_unifbase O OP) ∧ restriction_agreement ?? P OP);
        apply (mk_uniform_space (bishop_set_of_ordered_set {[s]}) f);
        [1: intros (U H); intro x; simplify; 
            cases H (w Hw); cases Hw (Gw Hwp); clear H Hw; intro Hm;
            lapply (us_phi1 O w Gw x (a2sa ??? Hm)) as IH;
            apply (restrict ? s ??? Hwp IH); 
        |2: intros (U V HU HV); cases HU (u Hu); cases HV (v Hv); clear HU HV;
            cases Hu (Gu HuU); cases Hv (Gv HvV); clear Hu Hv;
            cases (us_phi2 O u v Gu Gv) (w HW); cases HW (Gw Hw); clear HW;
            exists; [apply (λb:{[s]} squareB.w b)] split;
            [1: unfold f; simplify; clearbody f;
                exists; [apply w]; split; [assumption] intro b; simplify;
                unfold segment_square_of_ordered_set_square;
                cases b; intros; split; intros; assumption;
            |2: intros 2 (x Hx); cases (Hw ? Hx); split;
                [apply (restrict O s ??? HuU H)|apply (restrict O s ??? HvV H1);]]
        |3: intros (U Hu); cases Hu (u HU); cases HU (Gu HuU); clear Hu HU;
            cases (us_phi3 O u Gu) (w HW); cases HW (Gw Hwu); clear HW;
            exists; [apply (λx:{[s]} squareB.w x)] split;
            [1: exists;[apply w];split;[assumption] intros; simplify; intro;
                unfold segment_square_of_ordered_set_square;
                cases b; intros; split; intro; assumption;
            |2: intros 2 (x Hx); apply (restrict O s ??? HuU); apply Hwu; 
                cases Hx (m Hm); exists[apply (\fst m)] apply Hm;]
        |4: intros (U HU x); cases HU (u Hu); cases Hu (Gu HuU); clear HU Hu;
            cases (us_phi4 O u Gu x) (Hul Hur);
            split; intros; 
            [1: lapply (invert_restriction_agreement O s ?? HuU) as Ra;
                apply (restrict O s ?? x Ra);
                apply Hul; apply (unrestrict O s ??? HuU H);
            |2: apply (restrict O s ??? HuU); apply Hur; 
                apply (unrestrict O s ??? (invert_restriction_agreement O s ?? HuU) H);]]
    |2: simplify; reflexivity;]
|2: simplify; unfold convex; intros 3; cases s1; intros;
    (* TODO: x2sx is for ≰, we need one for ≤ *) 
    cases H (u HU); cases HU (Gu HuU); clear HU H;
    lapply depth=0 (ous_convex_l ?? Gu 〈\fst h,\fst h1〉 ???????) as K3;
    [2: intro; apply H2; apply (x2sx_ (os_l O) s h h1 H);
    |3: apply 〈\fst (\fst y),\fst (\snd y)〉;
    |4: intro; change in H with (\fst (\fst y) ≰ \fst h1); apply H3;
        apply (x2sx_ (os_l O) s (\fst y) h1 H);
    |5: change with (\fst h ≤ \fst (\fst y)); intro; apply H4;
        apply (x2sx_ (os_l O) s h (\fst y) H);
    |6: change with (\fst (\snd y) ≤ \fst h1); intro; apply H5;
        apply (x2sx_ (os_l O) s (\snd y) h1 H);
    |7: change with (\fst (\fst y) ≤ \fst (\snd y)); intro; apply H6;
        apply (x2sx_ (os_l O) s (\fst y) (\snd y) H);
    |8: apply (restrict O s U u y HuU K3);
    |1: apply (unrestrict O s ?? 〈h,h1〉 HuU H1);]
|3: simplify; unfold convex; intros 3; cases s1; intros;
    cases H (u HU); cases HU (Gu HuU); clear HU H;
    lapply depth=0 (ous_convex_r ?? Gu 〈\fst h,\fst h1〉 ???????) as K3;
    [2: intro; apply H2; apply (x2sx_ (os_r O) s h h1 H);
    |3: apply 〈\fst (\fst y),\fst (\snd y)〉;
    |4: intro; apply H3;
        apply (x2sx_ (os_r O) s (\fst y) h1 H);
    |5: intro; apply H4;
        apply (x2sx_ (os_r O) s h (\fst y) H);
    |6: intro; apply H5;
        apply (x2sx_ (os_r O) s (\snd y) h1 H);
    |7: intro; apply H6;
        apply (x2sx_ (os_r O) s (\fst y) (\snd y) H);
    |8: apply (restrict O s U u y HuU K3);
    |1: apply (unrestrict O s ?? 〈h,h1〉 HuU H1);]
]  
qed.

interpretation "Ordered uniform space segment" 'segset a = 
 (segment_ordered_uniform_space ? a).

(* Lemma 3.2 *)
alias symbol "pi1" = "exT \fst".
lemma restric_uniform_convergence:
 ∀O:ordered_uniform_space.∀s:‡O.
  ∀x:{[s]}.
   ∀a:sequence {[s]}.
    (⌊n, \fst (a n)⌋ : sequence O) uniform_converges (\fst x) → 
      a uniform_converges x.
intros 7; cases H1; cases H2; clear H2 H1;
cases (H ? H3) (m Hm); exists [apply m]; intros; 
apply (restrict ? s ??? H4); apply (Hm ? H1);
qed.

definition order_continuity ≝
  λC:ordered_uniform_space.∀a:sequence C.∀x:C.
    (a ↑ x → a uniform_converges x) ∧ (a ↓ x → a uniform_converges x).

lemma hint_boh1: ∀O. Type_OF_ordered_uniform_space O → hos_carr (os_l O).
intros; assumption;
qed.

coercion hint_boh1 nocomposites. 

lemma hint_boh2: ∀O:ordered_uniform_space. hos_carr (os_l O) → Type_OF_ordered_uniform_space O.
intros; assumption;
qed.

coercion hint_boh2 nocomposites. 


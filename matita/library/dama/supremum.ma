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


include "datatypes/constructors.ma".
include "nat/plus.ma".
include "dama/nat_ordered_set.ma".
include "dama/sequence.ma".

(* Definition 2.4 *)
definition upper_bound ≝ 
  λO:half_ordered_set.λa:sequence O.λu:O.∀n:nat.a n ≤≤ u.

definition supremum ≝
  λO:half_ordered_set.λs:sequence O.λx.
    upper_bound ? s x ∧ (∀y:O.x ≰≰ y → ∃n.s n ≰≰ y).

definition increasing ≝ 
  λO:half_ordered_set.λa:sequence O.∀n:nat.a n ≤≤ a (S n).

notation < "x \nbsp 'is_upper_bound' \nbsp s" non associative with precedence 45 
  for @{'upper_bound $s $x}.
notation < "x \nbsp 'is_lower_bound' \nbsp s" non associative with precedence 45 
  for @{'lower_bound $s $x}.
notation < "s \nbsp 'is_increasing'" non associative with precedence 45 
  for @{'increasing $s}.
notation < "s \nbsp 'is_decreasing'" non associative with precedence 45 
  for @{'decreasing $s}.
notation < "x \nbsp 'is_supremum' \nbsp s" non associative with precedence 45 
  for @{'supremum $s $x}.
notation < "x \nbsp 'is_infimum' \nbsp s" non associative with precedence 45 
  for @{'infimum $s $x}.
notation > "x 'is_upper_bound' s" non associative with precedence 45 
  for @{'upper_bound $s $x}.
notation > "x 'is_lower_bound' s" non associative with precedence 45 
  for @{'lower_bound $s $x}.
notation > "s 'is_increasing'"    non associative with precedence 45 
  for @{'increasing $s}.
notation > "s 'is_decreasing'"    non associative with precedence 45 
  for @{'decreasing $s}.
notation > "x 'is_supremum' s"  non associative with precedence 45 
  for @{'supremum $s $x}.
notation > "x 'is_infimum' s"  non associative with precedence 45 
  for @{'infimum $s $x}.

interpretation "Ordered set upper bound" 'upper_bound s x = (upper_bound (os_l ?) s x).
interpretation "Ordered set lower bound" 'lower_bound s x = (upper_bound (os_r ?) s x).

interpretation "Ordered set increasing"  'increasing s = (increasing (os_l ?) s).
interpretation "Ordered set decreasing"  'decreasing s = (increasing (os_r ?) s).

interpretation "Ordered set strong sup"  'supremum s x = (supremum (os_l ?) s x).
interpretation "Ordered set strong inf"  'infimum s x = (supremum (os_r ?) s x).
  
(* Fact 2.5 *)
lemma h_supremum_is_upper_bound: 
  ∀C:half_ordered_set.∀a:sequence C.∀u:C.
   supremum ? a u → ∀v.upper_bound ? a v → u ≤≤ v.
intros 7 (C s u Hu v Hv H); cases Hu (_ H1); clear Hu;
cases (H1 ? H) (w Hw); apply Hv; [apply w] assumption;
qed.

notation "'supremum_is_upper_bound'" non associative with precedence 90 for @{'supremum_is_upper_bound}.
notation "'infimum_is_lower_bound'" non associative with precedence 90 for @{'infimum_is_lower_bound}.

interpretation "supremum_is_upper_bound" 'supremum_is_upper_bound = (h_supremum_is_upper_bound (os_l ?)).
interpretation "infimum_is_lower_bound" 'infimum_is_lower_bound = (h_supremum_is_upper_bound (os_r ?)).

(* Lemma 2.6 *)
definition strictly_increasing ≝ 
  λC:half_ordered_set.λa:sequence C.∀n:nat.a (S n) ≰≰ a n.

notation < "s \nbsp 'is_strictly_increasing'" non associative with precedence 45 
  for @{'strictly_increasing $s}.
notation > "s 'is_strictly_increasing'" non associative with precedence 45 
  for @{'strictly_increasing $s}.
interpretation "Ordered set strict increasing"  'strictly_increasing s    = 
  (strictly_increasing (os_l ?) s).
  
notation < "s \nbsp 'is_strictly_decreasing'" non associative with precedence 45 
  for @{'strictly_decreasing $s}.
notation > "s 'is_strictly_decreasing'" non associative with precedence 45 
  for @{'strictly_decreasing $s}.
interpretation "Ordered set strict decreasing"  'strictly_decreasing s    = 
  (strictly_increasing (os_r ?) s).

definition uparrow ≝
  λC:half_ordered_set.λs:sequence C.λu:C.
   increasing ? s ∧ supremum ? s u.

interpretation "Ordered set uparrow" 'funion s u = (uparrow (os_l ?) s u).
interpretation "Ordered set downarrow" 'fintersects s u = (uparrow (os_r ?) s u).

lemma h_trans_increasing: 
  ∀C:half_ordered_set.∀a:sequence C.increasing ? a → 
   ∀n,m:nat_ordered_set. n ≤ m → a n ≤≤ a m.
intros 5 (C a Hs n m); elim m; [
  rewrite > (le_n_O_to_eq n (not_lt_to_le O n H));
  intro X; cases (hos_coreflexive ? (a n) X);]
cases (le_to_or_lt_eq ?? (not_lt_to_le (S n1) n H1)); clear H1;
[2: rewrite > H2; intro; cases (hos_coreflexive ? (a (S n1)) H1);
|1: apply (hle_transitive ???? (H ?) (Hs ?));
    intro; whd in H1; apply (not_le_Sn_n n); apply (transitive_le ??? H2 H1);]
qed.

notation "'trans_increasing'" non associative with precedence 90 for @{'trans_increasing}.
notation "'trans_decreasing'" non associative with precedence 90 for @{'trans_decreasing}.

interpretation "trans_increasing" 'trans_increasing = (h_trans_increasing (os_l ?)).
interpretation "trans_decreasing" 'trans_decreasing = (h_trans_increasing (os_r ?)).

lemma hint_nat :
 Type_OF_ordered_set nat_ordered_set →
   hos_carr (os_l (nat_ordered_set)).
intros; assumption;
qed.

coercion hint_nat nocomposites.

lemma h_trans_increasing_exc: 
  ∀C:half_ordered_set.∀a:sequence C.increasing ? a → 
   ∀n,m:nat_ordered_set. m ≰≰ n → a n ≤≤ a m.
intros 5 (C a Hs n m); elim m; [cases (not_le_Sn_O n H);]
intro; apply H; 
[1: change in n1 with (hos_carr (os_l nat_ordered_set)); 
    change with (n<n1);
    cases (le_to_or_lt_eq ?? H1); [apply le_S_S_to_le;assumption]
    cases (Hs n); rewrite < H3 in H2; assumption;    
|2: cases (hos_cotransitive ? (a n) (a (S n1)) (a n1) H2); [assumption]
    cases (Hs n1); assumption;]
qed.

notation "'trans_increasing_exc'" non associative with precedence 90 for @{'trans_increasing_exc}.
notation "'trans_decreasing_exc'" non associative with precedence 90 for @{'trans_decreasing_exc}.

interpretation "trans_increasing_exc" 'trans_increasing_exc = (h_trans_increasing_exc (os_l ?)).
interpretation "trans_decreasing_exc" 'trans_decreasing_exc = (h_trans_increasing_exc (os_r ?)).

alias symbol "exists" = "CProp exists".
lemma nat_strictly_increasing_reaches: 
  ∀m:sequence nat_ordered_set.
   m is_strictly_increasing → ∀w.∃t.m t ≰ w.
intros; elim w;
[1: cases (nat_discriminable O (m O)); [2: cases (not_le_Sn_n O (ltn_to_ltO ?? H1))]
    cases H1; [exists [apply O] apply H2;]
    exists [apply (S O)] lapply (H O) as H3; rewrite < H2 in H3; assumption
|2: cases H1 (p Hp); cases (nat_discriminable (S n) (m p)); 
    [1: cases H2; clear H2;
        [1: exists [apply p]; assumption;
        |2: exists [apply (S p)]; rewrite > H3; apply H;]
    |2: cases (?:False); change in Hp with (n<m p);
        apply (not_le_Sn_n (m p));
        apply (transitive_le ??? H2 Hp);]]
qed.
     
lemma h_selection_uparrow: 
  ∀C:half_ordered_set.∀m:sequence nat_ordered_set.
   m is_strictly_increasing →
    ∀a:sequence C.∀u.uparrow ? a u → uparrow ? ⌊x,a (m x)⌋ u.
intros (C m Hm a u Ha); cases Ha (Ia Su); cases Su (Uu Hu); repeat split; 
[1: intro n; simplify; apply (h_trans_increasing_exc ? a Ia); apply (Hm n);
|2: intro n; simplify; apply Uu;
|3: intros (y Hy); simplify; cases (Hu ? Hy);
    cases (nat_strictly_increasing_reaches ? Hm w); 
    exists [apply w1]; cases (hos_cotransitive ? (a w) y (a (m w1)) H); [2:assumption]  
    cases (h_trans_increasing_exc ?? Ia w (m w1) H1); assumption;]
qed.     

notation "'selection_uparrow'" non associative with precedence 90 for @{'selection_uparrow}.
notation "'selection_downarrow'" non associative with precedence 90 for @{'selection_downarrow}.

interpretation "selection_uparrow" 'selection_uparrow = (h_selection_uparrow (os_l ?)).
interpretation "selection_downarrow" 'selection_downarrow = (h_selection_uparrow (os_r ?)).

(* Definition 2.7 *)
definition order_converge ≝
  λO:ordered_set.λa:sequence O.λx:O.
   exT23 (sequence O) (λl.l ↑ x) (λu.u ↓ x)
     (λl,u:sequence O.∀i:nat. (l i) is_infimum ⌊w,a (w+i)⌋ ∧ 
                   (u i) is_supremum ⌊w,a (w+i)⌋).
    
notation < "a \nbsp (\cir \atop (\horbar\triangleright)) \nbsp x" non associative with precedence 45 
  for @{'order_converge $a $x}.
notation > "a 'order_converges' x" non associative with precedence 45 
  for @{'order_converge $a $x}.
interpretation "Order convergence" 'order_converge s u = (order_converge ? s u).   
    
(* Definition 2.8 *)
record segment (O : Type) : Type ≝ {
   seg_l_ : O;
   seg_u_ : O
}.

notation > "𝕦_ term 90 s" non associative with precedence 90 for @{'upp $s}.
notation "𝕦 \sub term 90 s" non associative with precedence 90 for @{'upp $s}. 
notation > "𝕝_ term 90 s" non associative with precedence 90 for @{'low $s}.
notation "𝕝 \sub term 90 s" non associative with precedence 90 for @{'low $s}. 
 
definition seg_u ≝
 λO:half_ordered_set.λs:segment O.
   wloss O ?? (λl,u.l) (seg_u_ ? s) (seg_l_ ? s).
definition seg_l ≝
 λO:half_ordered_set.λs:segment O.
   wloss O ?? (λl,u.l) (seg_l_ ? s) (seg_u_ ? s). 
 
interpretation "uppper" 'upp s = (seg_u (os_l ?) s).
interpretation "lower" 'low s = (seg_l (os_l ?) s).
interpretation "uppper dual" 'upp s = (seg_l (os_r ?) s).
interpretation "lower dual" 'low s = (seg_u (os_r ?) s).
 
definition in_segment ≝ 
  λO:half_ordered_set.λs:segment O.λx:O.
    wloss O ?? (λp1,p2.p1 ∧ p2) (seg_l ? s ≤≤ x) (x ≤≤ seg_u ? s).

notation "‡O" non associative with precedence 90 for @{'segment $O}.
interpretation "Ordered set sergment" 'segment x = (segment x).

interpretation "Ordered set sergment in" 'mem x s = (in_segment ? s x).

definition segment_ordered_set_carr ≝
  λO:half_ordered_set.λs:‡O.∃x.x ∈ s.
definition segment_ordered_set_exc ≝ 
  λO:half_ordered_set.λs:‡O.
   λx,y:segment_ordered_set_carr O s.hos_excess_ O (\fst x) (\fst y).
lemma segment_ordered_set_corefl:
 ∀O,s. coreflexive ? (wloss O ?? (segment_ordered_set_exc O s)).
intros 3; cases x; cases (wloss_prop O);
generalize in match (hos_coreflexive O w);
rewrite < (H1 ?? (segment_ordered_set_exc O s));
rewrite < (H1 ?? (hos_excess_ O)); intros; assumption;
qed.
lemma segment_ordered_set_cotrans : 
  ∀O,s. cotransitive ? (wloss O ?? (segment_ordered_set_exc O s)).
intros 5 (O s x y z); cases x; cases y ; cases z; clear x y z;
generalize in match (hos_cotransitive O w w1 w2);
cases (wloss_prop O); 
do 3 rewrite < (H3 ?? (segment_ordered_set_exc O s));
do 3 rewrite < (H3 ?? (hos_excess_ O)); intros; apply H4; assumption;
qed.  
  
lemma half_segment_ordered_set: 
  ∀O:half_ordered_set.∀s:segment O.half_ordered_set.
intros (O a); constructor 1;
[ apply (segment_ordered_set_carr O a);
| apply (wloss O);
| apply (wloss_prop O);
| apply (segment_ordered_set_exc O a);
| apply (segment_ordered_set_corefl O a);
| apply (segment_ordered_set_cotrans ??);
]
qed.

lemma segment_ordered_set: 
  ∀O:ordered_set.∀s:‡O.ordered_set.
intros (O s); 
apply half2full; apply (half_segment_ordered_set (os_l O) s); 
qed.

notation "{[ term 19 s ]}" non associative with precedence 90 for @{'segset $s}.
interpretation "Ordered set segment" 'segset s = (segment_ordered_set ? s). 

(* test :
 ∀O:ordered_set.∀s: segment (os_l O).∀x:O.
   in_segment (os_l O) s x
   =
   in_segment (os_r O) s x.
intros; try reflexivity;
*)

lemma prove_in_segment: 
 ∀O:half_ordered_set.∀s:segment O.∀x:O.
   (seg_l O s) ≤≤ x → x ≤≤ (seg_u O s) → x ∈ s.
intros; unfold; cases (wloss_prop O); rewrite < H2;
split; assumption;
qed.

lemma cases_in_segment: 
  ∀C:half_ordered_set.∀s:segment C.∀x. x ∈ s → (seg_l C s) ≤≤ x ∧ x ≤≤ (seg_u C s).
intros; unfold in H; cases (wloss_prop C) (W W); rewrite<W in H; [cases H; split;assumption]
cases H; split; assumption;
qed. 

definition hint_sequence: 
  ∀C:ordered_set.
    sequence (hos_carr (os_l C)) → sequence (Type_of_ordered_set C).
intros;assumption;
qed.

definition hint_sequence1: 
  ∀C:ordered_set.
    sequence (hos_carr (os_r C)) → sequence (Type_of_ordered_set_dual C).
intros;assumption;
qed.

definition hint_sequence2: 
  ∀C:ordered_set.
    sequence (Type_of_ordered_set C) → sequence (hos_carr (os_l C)).
intros;assumption;
qed.

definition hint_sequence3: 
  ∀C:ordered_set.
    sequence (Type_of_ordered_set_dual C) → sequence (hos_carr (os_r C)).
intros;assumption;
qed.

coercion hint_sequence nocomposites.
coercion hint_sequence1 nocomposites.
coercion hint_sequence2 nocomposites.
coercion hint_sequence3 nocomposites.

(* Lemma 2.9 - non easily dualizable *)

lemma x2sx_:
  ∀O:half_ordered_set.
   ∀s:segment O.∀x,y:half_segment_ordered_set ? s.
    \fst x ≰≰ \fst y → x ≰≰ y.
intros 4; cases x; cases y; clear x y; simplify; unfold hos_excess;
whd in ⊢ (?→? (% ? ?)? ? ? ? ?); simplify in ⊢ (?→%);
cases (wloss_prop O) (E E); do 2 rewrite < E; intros; assumption;
qed.

lemma sx2x_:
  ∀O:half_ordered_set.
   ∀s:segment O.∀x,y:half_segment_ordered_set ? s.
    x ≰≰ y → \fst x ≰≰ \fst y.
intros 4; cases x; cases y; clear x y; simplify; unfold hos_excess;
whd in ⊢ (? (% ? ?) ?? ? ? ? → ?); simplify in ⊢ (% → ?);
cases (wloss_prop O) (E E); do 2 rewrite < E; intros; assumption;
qed.

lemma l2sl_:
  ∀C,s.∀x,y:half_segment_ordered_set C s. \fst x ≤≤ \fst y → x ≤≤ y.
intros; intro; apply H; apply sx2x_; apply H1;
qed.


lemma sl2l_:
  ∀C,s.∀x,y:half_segment_ordered_set C s. x ≤≤ y → \fst x ≤≤ \fst y.
intros; intro; apply H; apply x2sx_; apply H1;
qed.

coercion x2sx_ nocomposites.
coercion sx2x_ nocomposites.
coercion l2sl_ nocomposites.
coercion sl2l_ nocomposites.

lemma h_segment_preserves_supremum:
  ∀O:half_ordered_set.∀s:segment O.
   ∀a:sequence (half_segment_ordered_set ? s).
    ∀x:half_segment_ordered_set ? s. 
      increasing ? ⌊n,\fst (a n)⌋ ∧ 
      supremum ? ⌊n,\fst (a n)⌋ (\fst x) → uparrow ? a x.
intros; split; cases H; clear H; 
[1: intro n; lapply (H1 n) as K; clear H1 H2;
    intro; apply K; clear K; apply rule H; 
|2: cases H2; split; clear H2;
    [1: intro n; lapply (H n) as K; intro W; apply K;
        apply rule W;
    |2: clear H1 H; intros (y0 Hy0); cases (H3 (\fst y0));[exists[apply w]]
        [1: change in H with (\fst (a w) ≰≰ \fst y0); apply rule H;
        |2: apply rule Hy0;]]]
qed.

notation "'segment_preserves_supremum'" non associative with precedence 90 for @{'segment_preserves_supremum}.
notation "'segment_preserves_infimum'" non associative with precedence 90 for @{'segment_preserves_infimum}.

interpretation "segment_preserves_supremum" 'segment_preserves_supremum = (h_segment_preserves_supremum (os_l ?)).
interpretation "segment_preserves_infimum" 'segment_preserves_infimum = (h_segment_preserves_supremum (os_r ?)).

(*
test segment_preserves_infimum2:
  ∀O:ordered_set.∀s:‡O.∀a:sequence {[s]}.∀x:{[s]}. 
    ⌊n,\fst (a n)⌋ is_decreasing ∧ 
    (\fst x) is_infimum ⌊n,\fst (a n)⌋ → a ↓ x.
intros; apply (segment_preserves_infimum s a x H);
qed.
*)
       
(* Definition 2.10 *)

alias symbol "pi2" = "pair pi2".
alias symbol "pi1" = "pair pi1".
(*
definition square_segment ≝ 
  λO:half_ordered_set.λs:segment O.λx: square_half_ordered_set O.
    in_segment ? s (\fst x) ∧ in_segment ? s (\snd x).
*) 
definition convex ≝
  λO:half_ordered_set.λU:square_half_ordered_set O → Prop.
    ∀s.U s → le O (\fst s) (\snd s) → 
     ∀y. 
       le O (\fst y) (\snd s) → 
       le O (\fst s) (\fst y) →
       le O (\snd y) (\snd s) →
       le O (\fst y) (\snd y) →
       U y.
  
(* Definition 2.11 *)  
definition upper_located ≝
  λO:half_ordered_set.λa:sequence O.∀x,y:O. y ≰≰ x → 
    (∃i:nat.a i ≰≰ x) ∨ (∃b:O.y ≰≰ b ∧ ∀i:nat.a i ≤≤ b).

notation < "s \nbsp 'is_upper_located'" non associative with precedence 45 
  for @{'upper_located $s}.
notation > "s 'is_upper_located'" non associative with precedence 45 
  for @{'upper_located $s}.
interpretation "Ordered set upper locatedness" 'upper_located s = 
  (upper_located (os_l ?) s).

notation < "s \nbsp 'is_lower_located'" non associative with precedence 45 
  for @{'lower_located $s}.
notation > "s 'is_lower_located'" non associative with precedence 45
  for @{'lower_located $s}.
interpretation "Ordered set lower locatedness" 'lower_located s = 
  (upper_located (os_r ?) s).
      
(* Lemma 2.12 *)    
lemma h_uparrow_upperlocated:
  ∀C:half_ordered_set.∀a:sequence C.∀u:C.uparrow ? a u → upper_located ? a.
intros (C a u H); cases H (H2 H3); clear H; intros 3 (x y Hxy);
cases H3 (H4 H5); clear H3; cases (hos_cotransitive C y x u Hxy) (W W);
[2: cases (H5 x W) (w Hw); left; exists [apply w] assumption;
|1: right; exists [apply u]; split; [apply W|apply H4]]
qed.

notation "'uparrow_upperlocated'" non associative with precedence 90 for @{'uparrow_upperlocated}.
notation "'downarrow_lowerlocated'" non associative with precedence 90 for @{'downarrow_lowerlocated}.

interpretation "uparrow_upperlocated" 'uparrow_upperlocated = (h_uparrow_upperlocated (os_l ?)).
interpretation "downarrow_lowerlocated" 'downarrow_lowerlocated = (h_uparrow_upperlocated (os_r ?)).

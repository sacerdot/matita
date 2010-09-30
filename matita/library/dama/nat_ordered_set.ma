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

include "nat/compare.ma".
include "dama/bishop_set.ma". 

definition nat_excess : nat → nat → CProp ≝ λn,m. m<n.

lemma nat_elim2: 
  ∀R:nat → nat → CProp.
  (∀ n:nat. R O n) → (∀n:nat. R (S n) O) → (∀n,m:nat. R n m → R (S n) (S m)) →
    ∀n,m:nat. R n m.
intros 5;elim n; [apply H]
cases m;[ apply H1| apply H2; apply H3 ]
qed.

alias symbol "lt" = "natural 'less than'".
lemma nat_discriminable: ∀x,y:nat.x < y ∨ x = y ∨ y < x.
intros (x y); apply (nat_elim2 ???? x y); 
[1: intro;left;cases n; [right;reflexivity] left; apply lt_O_S;
|2: intro;right;apply lt_O_S;
|3: intros; cases H; 
    [1: cases H1; [left; left; apply le_S_S; assumption]
        left;right;rewrite > H2; reflexivity;
    |2: right;apply le_S_S; assumption]]
qed.
        
lemma nat_excess_cotransitive: cotransitive ? nat_excess.
intros 3 (x y z); unfold nat_excess; simplify; intros;
cases (nat_discriminable x z); [2: left; assumption] cases H1; clear H1;
[1: right; apply (trans_lt ??? H H2);
|2: right; rewrite < H2; assumption;]
qed.
  
lemma nat_ordered_set : ordered_set.
letin hos ≝ (mk_half_ordered_set nat (λT,R:Type.λf:T→T→R.f) ? nat_excess ? nat_excess_cotransitive);
[ intros; left; intros; reflexivity;
| intro x; intro H; apply (not_le_Sn_n ? H);]
constructor 1;  apply hos;
qed.

interpretation "ordered set N" 'N = nat_ordered_set.

alias id "le" = "cic:/matita/nat/orders/le.ind#xpointer(1/1)".
lemma os_le_to_nat_le:
  ∀a,b:nat_ordered_set.a ≤ b → le a b.
intros; normalize in H; apply (not_lt_to_le b a H);
qed.
 
lemma nat_le_to_os_le:
  ∀a,b:nat_ordered_set.le a b → a ≤ b.
intros 3; apply (le_to_not_lt a b);assumption;
qed.


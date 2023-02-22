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

include "logic/equality.ma".
include "logic/coimplication.ma".
include "logic/cprop_connectives.ma".
include "datatypes/constructors.ma".
include "nat/orders.ma".
include "Z/z.ma". 

axiom choose : ∀A:Type.∀P:A → Prop.(∃x.P x) → exP ? P.
alias symbol "plus" = "Disjoint union".
axiom decide : ∀A,B.A ∨ B → A + B.

axiom R : Type.

axiom R0 : R.
axiom R1 : R.

axiom Rplus : R → R → R.
axiom Rtimes : R → R → R.
axiom Ropp : R → R.
axiom Rinv : R → R.
axiom Rlt : R → R → Prop.
definition Rle : R → R → Prop ≝ λx,y:R.Rlt x y ∨ x = y.

interpretation "real numbers" 'R = R.

interpretation "real numbers plus" 'plus x y = (Rplus x y).
interpretation "real numbers times" 'times x y = (Rtimes x y).
interpretation "real numbers opposite" 'uminus x = (Ropp x).
interpretation "real numbers reciprocal" 'invert x = (Rinv x).
interpretation "real numbers less than" 'lt x y = (Rlt x y).
interpretation "real numbers less eq" 'leq x y = (Rle x y).

axiom not_eq_R0_R1 : ¬ R0 = R1.

(* commutative ring with unity *)

axiom sym_Rplus : ∀x,y:R. x + y = y + x.
axiom assoc_Rplus : ∀x,y,z:R.(x+y)+z = x+(y+z).
axiom Rplus_x_R0 : ∀x.x + R0 = x.
axiom Rplus_Ropp : ∀x.x + (-x) = R0.

axiom sym_Rtimes : ∀x,y:R. x * y = y * x.
axiom assoc_Rtimes : ∀x,y,z:R.(x*y)*z = x*(y*z).
axiom Rtimes_x_R1 : ∀x.x * R1 = x.
axiom distr_Rtimes_Rplus_l : ∀x,y,z:R.x*(y+z) = x*y + x*z.

(*pump 200.*)
pump 40.

lemma distr_Rtimes_Rplus_r : ∀x,y,z:R.(x+y)*z = x*z + y*z.
intros; autobatch; 
qed.

(* commutative field *)

axiom Rinv_Rtimes_l : ∀x. ¬ x = R0 → x * (Rinv x) = R1.

(* ordered commutative field *)

axiom irrefl_Rlt : ∀x:R.¬ x < x.
axiom asym_Rlt : ∀x,y:R. x < y → ¬ y < x.
axiom trans_Rlt : ∀x,y,z:R.x < y → y < z → x < z.
axiom trichotomy_Rlt : ∀x,y.x < y ∨ y < x ∨ x = y.

lemma trans_Rle : ∀x,y,z:R.x ≤ y → y ≤ z → x ≤ z.
intros;cases H
[cases H1; unfold; autobatch;
|autobatch;]
(*
 [left;autobatch
 |rewrite < H3;assumption]
|rewrite > H2;assumption]*)
qed.

axiom Rlt_plus_l : ∀z,x,y:R.x < y → z + x < z + y.
axiom Rlt_times_l : ∀z,x,y:R.x < y → R0 < z → z*x < z*y.

(* FIXME: these should be lemmata *)
axiom Rle_plus_l : ∀z,x,y:R.x ≤ y → z + x ≤ z + y.
axiom Rle_times_l : ∀z,x,y:R.x ≤ y → R0 < z → z*x ≤ z*y.

lemma Rle_plus_r : ∀z,x,y:R.x ≤ y → x + z ≤ y + z.
intros; autobatch.
qed.

lemma Rle_times_r : ∀z,x,y:R.x ≤ y → R0 < z → x*z ≤ y*z.
intros;
(* rewrite > sym_Rtimes;rewrite > sym_Rtimes in ⊢ (??%); *)
autobatch;
qed.

(* Dedekind-completeness *)

definition ub ≝ λS: R → Prop.λx:R.∀y.S y → y ≤ x.
definition lub ≝ λS: R → Prop.λx:R.ub S x ∧ ∀y. ub S y → x ≤ y. 

axiom R_dedekind : ∀S:R → Prop.(∃x.S x) → (∃x.ub S x) → ∃x.lub S x.

(* coercions *)

definition R_of_nat : nat → R ≝
 λn.match n with
 [ O ⇒ R0
 | S p ⇒ let rec aux m ≝
   match m with
   [ O ⇒ R1
   | S q ⇒ (aux q) + R1] in aux p].

definition R_of_Z ≝
λz.match z with
[ pos n ⇒ R_of_nat (S n)
| neg n ⇒ Ropp (R_of_nat (S n))
| OZ ⇒ R0 ].

(* FIXME!!! coercion clash! *)
coercion R_of_Z.

(*coercion R_of_nat.*)

(* archimedean property *)

axiom R_archimedean : ∀x,y:R.R0 < x → ∃n:nat.y < n*x.

(*definition Rminus : R → R → R ≝
 λx,y.x + (-y).*)
 
interpretation "real numbers minus" 'minus x y = (Rplus x (Ropp y)).
interpretation "real numbers divide" 'divide x y = (Rtimes x (Rinv y)).

(* basic properties *)

(* equality *)

(* 
lemma Rplus_eq_l : ∀x,y,z.x = y → z + x= z + y.
intros;autobatch;
qed.

lemma Rplus_eq_r Rtimes_eq_l Rtimes_eq_r analogamente *)

lemma eq_Rplus_l_to_r : ∀a,b,c:R.a+b=c → a = c-b.
intros;lapply (eq_f ? ? (λx:R.x-b) ? ? H);
rewrite > assoc_Rplus in Hletin;rewrite > Rplus_Ropp in Hletin;
rewrite > Rplus_x_R0 in Hletin;assumption;
qed.

lemma eq_Rplus_r_to_l : ∀a,b,c:R.a=b+c → a-c = b.
intros;symmetry;apply eq_Rplus_l_to_r;symmetry;assumption;
qed.

lemma eq_Rminus_l_to_r : ∀a,b,c:R.a-b=c → a = c+b.
intros;lapply (eq_f ? ? (λx:R.x+b) ? ? H);
rewrite > assoc_Rplus in Hletin;rewrite > sym_Rplus in Hletin:(??(??%)?);
rewrite > Rplus_Ropp in Hletin;rewrite > Rplus_x_R0 in Hletin;assumption;
qed.

lemma eq_Rminus_r_to_l : ∀a,b,c:R.a=b-c → a+c = b.
intros;symmetry;apply eq_Rminus_l_to_r;autobatch paramodulation;
qed.

lemma eq_Rtimes_l_to_r : ∀a,b,c:R.b ≠ R0 → a*b=c → a = c/b.
intros;lapply (eq_f ? ? (λx:R.x/b) ? ? H1);
rewrite > assoc_Rtimes in Hletin;rewrite > Rinv_Rtimes_l in Hletin
[rewrite > Rtimes_x_R1 in Hletin;assumption
|assumption]
qed.

lemma eq_Rtimes_r_to_l : ∀a,b,c:R.c ≠ R0 → a=b*c → a/c = b.
intros;symmetry;apply eq_Rtimes_l_to_r
[assumption
|symmetry;assumption]
qed.

lemma eq_Rdiv_l_to_r : ∀a,b,c:R.b ≠ R0 → a/b=c → a = c*b.
intros;lapply (eq_f ? ? (λx:R.x*b) ? ? H1);
rewrite > assoc_Rtimes in Hletin;rewrite > sym_Rtimes in Hletin:(??(??%)?);
rewrite > Rinv_Rtimes_l in Hletin
[rewrite > Rtimes_x_R1 in Hletin;assumption
|assumption]
qed.

lemma eq_Rdiv_r_to_l : ∀a,b,c:R.c ≠ R0 → a=b/c → a*c = b.
intros;symmetry;apply eq_Rdiv_l_to_r
[assumption
|symmetry;assumption]
qed.

(* lemma unique_Ropp : ∀x,y.x + y = R0 → y = -x.
intros;autobatch paramodulation;
qed. *)

lemma Rtimes_x_R0 : ∀x.x * R0 = R0.
(*intro; autobatch paramodulation.*)  
intros;
rewrite < Rplus_x_R0 in ⊢ (? ? % ?);
rewrite < (Rplus_Ropp (x*R0)) in ⊢ (? ? (? ? %) %);
rewrite < assoc_Rplus;
apply eq_f2;autobatch paramodulation;

qed.

lemma eq_Rtimes_Ropp_R1_Ropp : ∀x.x*(-R1) = -x.
intro. (*autobatch paramodulation.*) 

rewrite < Rplus_x_R0 in ⊢ (? ? % ?);
rewrite < Rplus_x_R0 in ⊢ (? ? ? %);
rewrite < (Rplus_Ropp x) in ⊢ (? ? % ?);
rewrite < assoc_Rplus;
rewrite < sym_Rplus in ⊢ (? ? % ?);
rewrite < sym_Rplus in ⊢ (? ? (? ? %) ?);
apply eq_f2 [reflexivity]
rewrite < Rtimes_x_R1 in ⊢ (? ? (? % ?) ?);
rewrite < distr_Rtimes_Rplus_l;autobatch paramodulation;

qed.

lemma Ropp_inv : ∀x.x = Ropp (Ropp x).
intro;autobatch;
qed.

lemma Rinv_inv : ∀x.x ≠ R0 → x = Rinv (Rinv x).
intros;rewrite < Rtimes_x_R1 in ⊢ (???%);rewrite > sym_Rtimes;
apply eq_Rtimes_l_to_r
[intro;lapply (eq_f ? ? (λy:R.x*y) ? ? H1);
 rewrite > Rinv_Rtimes_l in Hletin
 [rewrite > Rtimes_x_R0 in Hletin;apply not_eq_R0_R1;symmetry;assumption
 |assumption]
|apply Rinv_Rtimes_l;assumption] 
qed.

lemma Ropp_R0 : R0 = - R0. demodulate all. (*
rewrite < eq_Rtimes_Ropp_R1_Ropp;autobatch paramodulation; *)
qed.

lemma distr_Ropp_Rplus : ∀x,y:R.-(x + y) = -x -y.
intros; demodulate all; (*rewrite < eq_Rtimes_Ropp_R1_Ropp;
rewrite > sym_Rtimes;rewrite > distr_Rtimes_Rplus_l;
autobatch paramodulation;*)
qed.

lemma Ropp_Rtimes_l : ∀x,y:R.-(x*y) = -x*y.
intros; demodulate all; (*rewrite < eq_Rtimes_Ropp_R1_Ropp;
rewrite > sym_Rtimes;rewrite < assoc_Rtimes;autobatch paramodulation;*)
qed.

lemma Ropp_Rtimes_r : ∀x,y:R.-(x*y) = x*-y.
intros; demodulate all; (*rewrite > sym_Rtimes;rewrite > sym_Rtimes in ⊢ (???%);
autobatch;*)
qed.

(* less than *)

lemma Rlt_to_Rlt_Ropp_Ropp : ∀x,y.x < y → -y < -x.
intros;rewrite < Rplus_x_R0 in ⊢ (??%);
rewrite < (Rplus_Ropp y);rewrite < Rplus_x_R0 in ⊢ (?%?);
rewrite < assoc_Rplus;rewrite < sym_Rplus in ⊢ (??%);
apply Rlt_plus_l;
rewrite < (Rplus_Ropp x);rewrite < sym_Rplus in ⊢ (?%?);autobatch;
qed.

lemma lt_R0_R1 : R0 < R1.
elim (trichotomy_Rlt R0 R1) [|elim (not_eq_R0_R1 H)]
elim H [assumption]
rewrite > Ropp_inv in ⊢ (??%);rewrite < eq_Rtimes_Ropp_R1_Ropp;
rewrite < (Rtimes_x_R0 (-R1));
apply Rlt_times_l;rewrite < (Rtimes_x_R0 (-R1));
rewrite > sym_Rtimes;rewrite > eq_Rtimes_Ropp_R1_Ropp;autobatch;
qed.

lemma pos_z_to_lt_Rtimes_Rtimes_to_lt : ∀x,y,z.R0 < z → z*x < z*y → x < y.
intros;elim (trichotomy_Rlt x y)
[elim H2 [assumption]
 elim (asym_Rlt (z*y) (z*x));autobatch
|rewrite > H2 in H1;elim (irrefl_Rlt ? H1)]
qed.

lemma pos_z_to_le_Rtimes_Rtimes_to_lt : ∀x,y,z.R0 < z → z*x ≤ z*y → x ≤ y.
intros;cases H1
[left;autobatch
|right; rewrite < Rtimes_x_R1;rewrite < Rtimes_x_R1 in ⊢ (???%);
 rewrite < sym_Rtimes;rewrite < sym_Rtimes in ⊢ (???%);
 rewrite < (Rinv_Rtimes_l z)
 [demodulate all; (*rewrite < sym_Rtimes in ⊢ (??(?%?)?);rewrite < sym_Rtimes in ⊢ (???(?%?));
  autobatch paramodulation*)
 |intro;rewrite > H3 in H;apply (irrefl_Rlt R0);assumption]] 
qed.

lemma neg_z_to_lt_Rtimes_Rtimes_to_lt : ∀x,y,z.z < R0 → z*x < z*y → y < x.
intros;rewrite > Ropp_inv in ⊢ (?%?);
rewrite > Ropp_inv in ⊢ (??%);
apply Rlt_to_Rlt_Ropp_Ropp;apply (pos_z_to_lt_Rtimes_Rtimes_to_lt ?? (-z))
[rewrite > Ropp_R0;autobatch
|applyS H1; (*
 rewrite < (eq_Rtimes_Ropp_R1_Ropp) in ⊢ (?(??%)?);
 rewrite < (eq_Rtimes_Ropp_R1_Ropp) in ⊢ (??(??%));
 do 2 rewrite < assoc_Rtimes;
 rewrite > eq_Rtimes_Ropp_R1_Ropp;
 rewrite > eq_Rtimes_Ropp_R1_Ropp in ⊢ (??%);
 rewrite > sym_Rtimes;rewrite > sym_Rtimes in ⊢ (??%);
 rewrite < (eq_Rtimes_Ropp_R1_Ropp) in ⊢ (?%?);
 rewrite < (eq_Rtimes_Ropp_R1_Ropp) in ⊢ (??%);
 do 2 rewrite > assoc_Rtimes;
 rewrite > eq_Rtimes_Ropp_R1_Ropp;
 rewrite < Ropp_inv;
 rewrite > sym_Rtimes;rewrite > sym_Rtimes in ⊢ (??%);
 assumption*)]
qed.

lemma lt_R0_Rinv : ∀x.R0 < x → R0 < Rinv x.
intros;apply (pos_z_to_lt_Rtimes_Rtimes_to_lt ?? x H);rewrite > Rinv_Rtimes_l;
[rewrite > Rtimes_x_R0;autobatch
|intro;apply (irrefl_Rlt x);rewrite < H1 in H;assumption]
qed.

lemma pos_times_pos_pos : ∀x,y.R0 < x → R0 < y → R0 < x*y.
intros;rewrite < (Rtimes_x_R0 x);autobatch;
qed.

lemma pos_plus_pos_pos : ∀x,y.R0 < x → R0 < y → R0 < x+y.
intros;rewrite < (Rplus_Ropp x);apply Rlt_plus_l;
apply (trans_Rlt ???? H1);rewrite > Ropp_R0;
apply Rlt_to_Rlt_Ropp_Ropp;assumption;
qed.

lemma Rlt_to_neq : ∀x,y:R.x < y → x ≠ y.
intros;intro;rewrite > H1 in H;apply (irrefl_Rlt ? H);
qed.

lemma lt_Rinv : ∀x,y.R0 < x → x < y → Rinv y < Rinv x.
intros;
lapply (Rlt_times_l (Rinv x * Rinv y) ? ? H1)
[ lapply (Rinv_Rtimes_l x);[2: intro; destruct H2; autobatch;]
  lapply (Rinv_Rtimes_l y);[2: intro; destruct H2; autobatch;]
  cut ((x \sup -1/y*x<x \sup -1/y*y) = (y^-1 < x ^-1));[2:autobatch
(* end auto($Revision: 9716 $) proof: TIME=2.24 SIZE=100 DEPTH=100 *) ;]
  rewrite < Hcut; assumption;
 (*
 rewrite > sym_Rtimes in Hletin;rewrite < assoc_Rtimes in Hletin;
 rewrite > assoc_Rtimes in Hletin:(??%);
 rewrite > sym_Rtimes in Hletin:(??(??%));
 rewrite > Rinv_Rtimes_l in Hletin
 [rewrite > Rinv_Rtimes_l in Hletin
  [applyS Hletin;(*rewrite > Rtimes_x_R1 in Hletin;rewrite > sym_Rtimes in Hletin;
   rewrite > Rtimes_x_R1 in Hletin;assumption*)
  |intro;rewrite > H2 in H1;apply (asym_Rlt ? ? H H1)]
 |intro;rewrite > H2 in H;apply (irrefl_Rlt ? H)]*)
|apply pos_times_pos_pos;apply lt_R0_Rinv;autobatch]
qed.

lemma Rlt_plus_l_to_r : ∀a,b,c.a + b < c → a < c - b.
intros;
autobatch by H, (Rlt_plus_l (-b) (a+b) c);
(*
rewrite < Rplus_x_R0;rewrite < (Rplus_Ropp b);
rewrite < assoc_Rplus;
rewrite < sym_Rplus;rewrite < sym_Rplus in ⊢ (??%);
apply (Rlt_plus_l (-b) (a+b) c);assumption;
*)
qed.

lemma Rlt_plus_r_to_l : ∀a,b,c.a < b + c → a - c < b.
intros;
rewrite > Ropp_inv;rewrite > Ropp_inv in ⊢ (??%);
apply Rlt_to_Rlt_Ropp_Ropp;rewrite > distr_Ropp_Rplus;
apply Rlt_plus_l_to_r;rewrite < distr_Ropp_Rplus;apply Rlt_to_Rlt_Ropp_Ropp;
assumption;
qed.

lemma Rlt_minus_l_to_r : ∀a,b,c.a - b < c → a < c + b.
intros;rewrite > (Ropp_inv b);apply Rlt_plus_l_to_r;assumption;
qed.

lemma Rlt_minus_r_to_l : ∀a,b,c.a < b - c → a + c < b.
intros;rewrite > (Ropp_inv c);apply Rlt_plus_r_to_l;assumption;
qed.

lemma Rlt_div_r_to_l : ∀a,b,c.R0 < c → a < b/c → a*c < b.
intros;rewrite < sym_Rtimes;
rewrite < Rtimes_x_R1 in ⊢ (??%);rewrite < sym_Rtimes in ⊢ (??%);
rewrite < (Rinv_Rtimes_l c)
[rewrite > assoc_Rtimes;apply Rlt_times_l
 [rewrite > sym_Rtimes;assumption
 |autobatch]
|intro;elim (Rlt_to_neq ?? H);symmetry;assumption]
qed.

lemma Rlt_times_l_to_r : ∀a,b,c.R0 < b → a*b < c → a < c/b.
intros;rewrite < sym_Rtimes;
rewrite < Rtimes_x_R1;rewrite < sym_Rtimes;
rewrite < (Rinv_Rtimes_l b)
[rewrite < sym_Rtimes in ⊢ (? (? % ?) ?);
 rewrite > assoc_Rtimes;apply Rlt_times_l
 [rewrite > sym_Rtimes;assumption
 |autobatch]
|intro;elim (Rlt_to_neq ?? H);symmetry;assumption]
qed.

lemma Rle_plus_l_to_r : ∀a,b,c.a + b ≤ c → a ≤ c - b.
intros;cases H
[left;autobatch
|right;autobatch]
qed.

lemma Rle_plus_r_to_l : ∀a,b,c.a ≤ b + c → a - c ≤ b.
intros;cases H
[left;autobatch
|right;autobatch]
qed.

lemma Rle_minus_l_to_r : ∀a,b,c.a - b ≤ c → a ≤ c + b.
intros;cases H
[left;autobatch
|right;autobatch]
qed.

lemma Rle_minus_r_to_l : ∀a,b,c.a ≤ b - c → a + c ≤ b.
intros;cases H
[left;autobatch
|right;autobatch]
qed.

lemma R_OF_nat_S : ∀n.R_OF_nat (S n) = R_OF_nat n + R1.
intros;elim n;simplify
[autobatch paramodulation
|reflexivity]
qed.

lemma nat_lt_to_R_lt : ∀m,n:nat.m < n → R_OF_nat m < R_OF_nat n.
intros;elim H
[cases m;simplify
 [autobatch
 |rewrite < Rplus_x_R0 in ⊢ (?%?);apply Rlt_plus_l;autobatch]
|apply (trans_Rlt ??? H2);cases n1;simplify
 [autobatch
 |rewrite < Rplus_x_R0 in ⊢ (?%?);apply Rlt_plus_l;autobatch]]
qed.
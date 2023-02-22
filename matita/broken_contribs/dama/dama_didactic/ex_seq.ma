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



include "sequences.ma".

(*
ESERCIZI SULLE SUCCESSIONI

Dimostrare che la successione alpha converge a 0
*)

definition F ≝ λ x:R.Rdiv x (S (S O)).

definition alpha ≝ successione F R1.

axiom cont: continuo F.

lemma l1: monotone_not_increasing alpha.
 we need to prove (monotone_not_increasing alpha)
 or equivalently (∀n:nat. alpha (S n) ≤ alpha n).
  assume n:nat.
  we need to prove (alpha (S n) ≤ alpha n)
  or equivalently (Rdiv (alpha n) (S (S O)) ≤ alpha n).
  done.
qed.
 
lemma l2: inf_bounded alpha.
 we need to prove (inf_bounded alpha)
 or equivalently (∃m. ∀n:nat. m ≤ alpha n).
  (* da trovare il modo giusto *)
  cut (∀n:nat.R0 ≤ alpha n).by (ex_intro ? ? R0 Hcut) done.
  (* fatto *)
  we need to prove (∀n:nat. R0 ≤ alpha n).
  assume n:nat.
  we proceed by induction on n to prove (R0 ≤ alpha n).
  case O.
    (* manca il comando 
    the thesis becomes (R0 ≤ alpha O)
    or equivalently (R0 ≤ R1).
    by _ done. *)
    (* approssimiamo con questo *)
    we need to prove (R0 ≤ alpha O)
    or equivalently (R0 ≤ R1).
    done.
  case S (m:nat).
   by induction hypothesis we know (R0 ≤ alpha m) (H).
   we need to prove (R0 ≤ alpha (S m))
   or equivalently (R0 ≤ Rdiv (alpha m) (S (S O))).
    done.
qed.

axiom xxx':
∀ F: R → R. ∀b:R. continuo F →
 ∀ l. tends_to (successione F b) l →
  punto_fisso F l.

theorem dimostrazione: tends_to alpha O.
 let l:R such that (tends_to alpha l) (H).
(* unfold alpha in H.
 change in match alpha in H with (successione F O).
 check(xxx' F cont l H).*)
(* end auto($Revision: 8612 $) proof: TIME=0.01 SIZE=100 DEPTH=100 *)
 using (lim_punto_fisso F R1 cont l H)  we proved (punto_fisso F l) (H2)
 that is equivalent to (l = (Rdiv l (S (S O)))).
 we proved (tends_to alpha l = tends_to alpha O) (H4).
 rewrite < H4.
 done.
qed.

(******************************************************************************)

(* Dimostrare che la successione alpha2 diverge *)

definition F2 ≝ λ x:R. Rmult x x.

definition alpha2 ≝ successione F2 (S (S O)).
 
lemma uno: ∀n. alpha2 n ≥ R1.
 we need to prove (∀n. alpha2 n ≥ R1).
 assume n:nat.
 we proceed by induction on n to prove (alpha2 n ≥ R1).
 case O.
   alias num (instance 0) = "natural number".
   we need to prove (alpha2 0 ≥ R1)
   or equivalently ((S (S O)) ≥ R1).
   done.
 case S (m:nat).
   by induction hypothesis we know (alpha2 m ≥ R1) (H).
   we need to prove (alpha2 (S m) ≥ R1)
   or equivalently (Rmult (alpha2 m) (alpha2 m) ≥ R1).letin xxx := (n ≤ n);
   we proved (R1 · R1 ≤ alpha2 m · alpha2 m) (H1).
   we proved (R1 · R1 = R1) (H2).
   rewrite < H2.
   done.
qed.

lemma mono1: monotone_not_decreasing alpha2.
 we need to prove (monotone_not_decreasing alpha2)
 or equivalently (∀n:nat. alpha2 n ≤ alpha2 (S n)).
 assume n:nat.
 we need to prove (alpha2 n ≤ alpha2 (S n))
 or equivalently (alpha2 n ≤ Rmult (alpha2 n) (alpha2 n)).
 done.
qed.

(*
lemma due: ∀n. Relev (alpha2 0) n ≥ R0.
 we need to prove (∀n. Relev (alpha2 0) n ≥ R0)
 or equivalently (∀n. Relev (S (S O)) n ≥ R0).
 by _ done.
qed.

lemma tre: ∀n. alpha2 (S n) ≥ Relev (alpha2 0) (S n).
 we need to prove (∀n. alpha2 (S n) ≥ Relev (alpha2 0) (S n)).
 assume n:nat.
 we proceed by induction on n to prove (alpha2 (S n) ≥ Relev (alpha2 0) (S n)).
 case 0.
  we need to prove (alpha2 1 ≥ Relev (alpha2 0) R1)
  or equivalently (Rmult R2 R2 ≥ R2).
  by _ done.
 case S (m:nat).
  by induction hypothesis we know (alpha2 (S m) ≥ Relev (alpha2 0) (S m)) (H).
  we need to prove (alpha2 (S (S m)) ≥ Relev (alpha2 0) (S (S m)))
  or equivalently
  (*..TODO..*)
  
theorem dim2: tends_to_inf alpha2.
(*..TODO..*)
qed.
*)
  
(******************************************************************************)

(* Dimostrare che la successione alpha3 converge a 0 *)
(*
definition alpha3 ≝ successione F2 (Rdiv (S 0) (S (S 0))).

lemma quattro: ∀n. alpha3 n ≤ R1.
 assume n:nat.
 we need to prove (∀n. alpha3 n ≤ R1).
 we proceed by induction on n to prove (alpha3 n ≤ R1).
 case O.
  we need to prove (alpha3 0 ≤ R1).
  by _ done.
 case S (m:nat).
  by induction hypothesis we know (alpha3 m ≤ R1) (H).
  we need to prove (alpha3 (S m) ≤ R1)
  or equivalently (Rmult (alpha3 m) (alpha3 m) ≤ R1).
  by _ done.
 qed.

lemma mono3: monotone_not_increasing alpha3.
 we need to prove (monotone_not_increasing alpha3)
 or equivalently (∀n:nat. alpha (S n) ≤ alpha n).
  assume n:nat.
  we need to prove (alpha (S n) ≤ alpha n)
  or equivalently (Rmult (alpha3 n) (alpha3 n) ≤ alpha3 n).
  by _ done.
qed.

lemma bound3: inf_bounded alpha3.
 we need to prove (inf_bounded alpha3)
 or equivalently (∃m. ∀n:nat. m ≤ alpha3 n).
  (* da trovare il modo giusto *)
  cut (∀n:nat.R0 ≤ alpha3 n).by (ex_intro ? ? R0 Hcut) done.
  (* fatto *)
  we need to prove (∀n:nat. R0 ≤ alpha3 n).
  assume n:nat.
  we proceed by induction on n to prove (R0 ≤ alpha3 n).
  case O.
    (* manca il comando 
    the thesis becomes (R0 ≤ alpha O)
    or equivalently (R0 ≤ R1).
    by _ done. *)
    (* approssimiamo con questo *)
    we need to prove (R0 ≤ alpha3 O)
    or equivalently (R0 ≤ Rdiv (S 0) (S (S 0))).
    by _ done.
  case S (m:nat).
   by induction hypothesis we know (R0 ≤ alpha3 m) (H).
   we need to prove (R0 ≤ alpha3 (S m))
   or equivalently (R0 ≤ Rmult (alpha3 m) (alpha3 m)).
   by _ done.
qed.

theorem dim3: tends_to alpha3 O.
(*..TODO..*)
qed.
*)
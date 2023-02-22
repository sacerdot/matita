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



include "coq.ma".

alias id "nat" = "cic:/Coq/Init/Datatypes/nat.ind#xpointer(1/1)".
alias id "eq" = "cic:/Coq/Init/Logic/eq.ind#xpointer(1/1)".
alias id "eq_ind" = "cic:/Coq/Init/Logic/eq_ind.con".
alias id "eq_ind_r" = "cic:/Coq/Init/Logic/eq_ind_r.con".
alias id "sym_eq" = "cic:/Coq/Init/Logic/sym_eq.con".

definition bool_algebra \def
  \lambda A:Set.
  \lambda one:A.
  \lambda zero:A.
  \lambda add: A \to A \to A.
  \lambda mult: A \to A \to A.
  \lambda inv: A \to A.
  (\forall x:A. (add x (inv x)) = one)\land
  (\forall x:A. (mult x (inv x)) = zero)\land
  (\forall x:A. (mult x one) = x)\land
  (\forall x:A. (add x zero) = x)\land
  (\forall x,y,z:A.(mult x (add y z)) = (add (mult x y) (mult x z)))\land
  (\forall x,y,z:A.(add x (mult y z)) = (mult (add x y) (add x z)))\land
  (\forall x,y:A.(mult x y) = (mult y x))\land
  (\forall x,y:A.(add x y) = (add y x)).
 
(*
theorem SKK:
  \forall A:Set.
  \forall app: A \to A \to A.
  \forall K:A. 
  \forall S:A.
  \forall H1: (\forall x,y:A.(app (app K x) y) = x).
  \forall H2: (\forall x,y,z:A.
    (app (app (app S x) y) z) = (app (app x z) (app y z))).
  \forall x:A.
    (app (app (app S K) K) x) = x.
intros.auto paramodulation.
qed.
*)
(*
theorem bool1:
  \forall A: Set.
  \forall one,zero: A.
  \forall add,mult: A \to A \to A.
  \forall inv: A \to A.
  \forall H: bool_algebra A one zero add mult inv.
  (inv zero) = one.
intros.
unfold bool_algebra in H.
decompose
auto paramodulation.
qed.
*)
(*
theorem bool2:
  \forall A: Set.
  \forall one,zero: A.
  \forall add,mult: A \to A \to A.
  \forall inv: A \to A.
  \forall H: bool_algebra A one zero add mult inv.
  \forall x:A. (mult x zero) = zero.
intros.
unfold bool_algebra in H.
decompose
auto paramodulation.
qed.
*)
(*
theorem bool3:
  \forall A: Set.
  \forall one,zero: A.
  \forall add,mult: A \to A \to A.
  \forall inv: A \to A.
  \forall H: bool_algebra A one zero add mult inv.
  \forall x:A. (inv (inv x)) = x.
intros.
unfold bool_algebra in H.
decompose
auto paramodulation.
qed.
*)
(*
theorem bool266:
  \forall A: Set.
  \forall one,zero: A.
  \forall add,mult: A \to A \to A.
  \forall inv: A \to A.
  \forall H: bool_algebra A one zero add mult inv.
  \forall x,y:A. (mult x (add (inv x) y)) = (mult x y).
intros.
unfold bool_algebra in H.
decompose
auto paramodulation.
qed.
*)
(*
theorem bool507:
  \forall A: Set.
  \forall one,zero: A.
  \forall add,mult: A \to A \to A.
  \forall inv: A \to A.
  \forall H: bool_algebra A one zero add mult inv.
  \forall x,y:A. zero = (mult x (mult (inv x) y)).
intros.
unfold bool_algebra in H.
decompose
auto paramodulation.
qed.
*)
(*
theorem bool515:
  \forall A: Set.
  \forall one,zero: A.
  \forall add,mult: A \to A \to A.
  \forall inv: A \to A.
  \forall H: bool_algebra A one zero add mult inv.
  \forall x,y:A. zero = mult (inv x) (mult x y).
intros.
unfold bool_algebra in H.
decompose
auto paramodulation.
qed.
*)
(*
theorem bool304:
  \forall A: Set.
  \forall one,zero: A.
  \forall add,mult: A \to A \to A.
  \forall inv: A \to A.
  \forall H: bool_algebra A one zero add mult inv.
  \forall x,y:A. x = (mult (add y x) x).
intros.
unfold bool_algebra in H.
decompose
auto paramodulation.
qed.
*)
(*
theorem bool531:
  \forall A: Set.
  \forall one,zero: A.
  \forall add,mult: A \to A \to A.
  \forall inv: A \to A.
  \forall H: bool_algebra A one zero add mult inv.
  \forall x,y:A. zero = (mult (inv (add x y)) y).
intros.
unfold bool_algebra in H.
decompose
auto paramodulation.
qed.
*)
(*
theorem bool253:
  \forall A: Set.
  \forall one,zero: A.
  \forall add,mult: A \to A \to A.
  \forall inv: A \to A.
  \forall H: bool_algebra A one zero add mult inv.
  \forall x,y:A. (add (inv x) (mult y x)) = (add (inv x) y).
intros.
unfold bool_algebra in H.
decompose
auto paramodulation.
qed.
*)
(*
theorem bool557:
  \forall A: Set.
  \forall one,zero: A.
  \forall add,mult: A \to A \to A.
  \forall inv: A \to A.
  \forall H: bool_algebra A one zero add mult inv.
  \forall x,y:A. 
    inv x =  (add (inv x) (inv (add y x))).
intros.
unfold bool_algebra in H.
decompose
auto paramodulation.
qed.
*)
(*
theorem bool609:
  \forall A: Set.
  \forall one,zero: A.
  \forall add,mult: A \to A \to A.
  \forall inv: A \to A.
  \forall H: bool_algebra A one zero add mult inv.
  \forall x,y:A. 
    inv x =  (add (inv (add y x)) (inv x)).
intros.
unfold bool_algebra in H.
decompose
auto paramodulation.
qed.
*)
(*
theorem bool260:
  \forall A: Set.
  \forall one,zero: A.
  \forall add,mult: A \to A \to A.
  \forall inv: A \to A.
  \forall H: bool_algebra A one zero add mult inv.
  \forall x,y,z:A. 
    add x (mult x y) = mult x (add x y).
intros.
unfold bool_algebra in H.
decompose
auto paramodulation.
qed.
*)
(*
theorem bool276:
  \forall A: Set.
  \forall one,zero: A.
  \forall add,mult: A \to A \to A.
  \forall inv: A \to A.
  \forall H: bool_algebra A one zero add mult inv.
  \forall x,y,z,u:A. 
    (mult (add x y) (add z (add x u))) = (add (mult (add x y) z) (add x (mult y u))).
intros.
unfold bool_algebra in H.
decompose
auto paramodulation.
qed. 
*)
(*
theorem bool250:
  \forall A: Set.
  \forall one,zero: A.
  \forall add,mult: A \to A \to A.
  \forall inv: A \to A.
  \forall H: bool_algebra A one zero add mult inv.
  \forall x,y,z:A. 
    add x (mult y z) = mult (add y x) (add x z).
intros.
unfold bool_algebra in H.
decompose
auto paramodulation.
qed. 
*)
(*
theorem bool756minimal:
  \forall A:Set.
  \forall add: A \to A \to A.
  \forall mult: A \to A \to A.
  \forall c1:(\forall x,y:A.(add x y) = (add y x)). 
  \forall hint1: (\forall x,y,z,u:A. 
    add y (add x (mult x u)) = (add (mult (add x y) z) (add x (mult y u)))).
  \forall hint2: (\forall x,y:A. x = (mult (add y x) x)).
  \forall x,y,z:A. 
    add x (add y (mult y z)) = add x (add y (mult x z)).
intros.
auto paramodulation.
qed.
*)
(*
theorem bool756simplified:
  \forall A:Set.
  \forall add: A \to A \to A.
  \forall mult: A \to A \to A.
  \forall c1:(\forall x,y:A.(add x y) = (add y x)). 
  \forall c2:(\forall x,y:A.(mult x y) = (mult y x)). 
  \forall hint1: (\forall x,y,z,u:A. 
    (mult (add x y) (add z (add x u))) = (add (mult (add x y) z) (add x (mult y u)))).
  \forall hint2: (\forall x,y:A. x = (mult (add y x) x)).
  \forall hint3: (\forall x,y,z:A. 
    add x (mult y z) = mult (add y x) (add x z)).
  \forall hint4: (\forall x,y:A. 
    add x (mult x y) = mult x (add x y)).
  \forall x,y,z:A. 
    add x (add y (mult y z)) = add x (add y (mult x z)).
intros.
auto paramodulation.
qed.
*)
(*
theorem bool756:
  \forall A:Set.
  \forall one:A.
  \forall zero:A.
  \forall add: A \to A \to A.
  \forall mult: A \to A \to A.
  \forall inv: A \to A.
  \forall c1:(\forall x,y:A.(add x y) = (add y x)). 
  \forall c2:(\forall x,y:A.(mult x y) = (mult y x)). 
  \forall d1: (\forall x,y,z:A.
              (add x (mult y z)) = (mult (add x y) (add x z))).
  \forall d2: (\forall x,y,z:A.
              (mult x (add y z)) = (add (mult x y) (mult x z))).  
  \forall i1: (\forall x:A. (add x zero) = x).
  \forall i2: (\forall x:A. (mult x one) = x).   
  \forall inv1: (\forall x:A. (add x (inv x)) = one).  
  \forall inv2: (\forall x:A. (mult x (inv x)) = zero). 
  \forall hint1: (\forall x,y,z,u:A. 
    (mult (add x y) (add z (add x u))) = (add (mult (add x y) z) (add x (mult y u)))).
  \forall hint2: (\forall x,y:A. x = (mult (add y x) x)).
  \forall hint3: (\forall x,y,z:A. 
    add x (mult y z) = mult (add y x) (add x z)).
  \forall hint4: (\forall x,y:A. 
    add x (mult x y) = mult x (add x y)).
  \forall x,y,z:A. 
    add x y = add x (add y (mult x z)).
intros;
cut (mult (add y x) (add x (add y z)) = add x (add y (mult x z)));
[auto paramodulation
|auto paramodulation]
qed.
*)
(*
theorem bool756full:
  \forall A: Set.
  \forall one,zero: A.
  \forall add,mult: A \to A \to A.
  \forall inv: A \to A.
  \forall H: bool_algebra A one zero add mult inv.
  \forall x,y,z:A. 
    add x y = add x (add y (mult x z)).
intros.
unfold bool_algebra in H.
decompose
auto paramodulation.
qed.
*)
(*
theorem bool1164:
  \forall A: Set.
  \forall one,zero: A.
  \forall add,mult: A \to A \to A.
  \forall inv: A \to A.
  \forall H: bool_algebra A one zero add mult inv.
  \forall x,y,z:A.
    (add x y) = (add (add x (mult y z)) y).
intros.
unfold bool_algebra in H.
decompose
auto paramodulation.
qed.
*)
(*
theorem bool1230:
  \forall A: Set.
  \forall one,zero: A.
  \forall add,mult: A \to A \to A.
  \forall inv: A \to A.
  \forall H: bool_algebra A one zero add mult inv.
  \forall A:Set.
  \forall one:A.
  \forall zero:A.
  \forall add: A \to A \to A.
  \forall mult: A \to A \to A.
  \forall inv: A \to A.
  \forall c1:(\forall x,y:A.(add x y) = (add y x)). 
  \forall c2:(\forall x,y:A.(mult x y) = (mult y x)). 
  \forall d1: (\forall x,y,z:A.
              (add x (mult y z)) = (mult (add x y) (add x z))).
  \forall d2: (\forall x,y,z:A.
              (mult x (add y z)) = (add (mult x y) (mult x z))).  
  \forall i1: (\forall x:A. (add x zero) = x).
  \forall i2: (\forall x:A. (mult x one) = x).   
  \forall inv1: (\forall x:A. (add x (inv x)) = one).  
  \forall inv2: (\forall x:A. (mult x (inv x)) = zero). 
  \forall x,y,z:A.
  \forall c1z: (\forall x:A.(add x z) = (add z x)). 
    add (add x y) z = add (add x y) (add z y).
intros.
auto paramodulation.
qed.
*)
(*
theorem bool1230:
  \forall A: Set.
  \forall one,zero: A.
  \forall add,mult: A \to A \to A.
  \forall inv: A \to A.
  \forall H: bool_algebra A one zero add mult inv.
  \forall x,y,z:A.
    add (add x y) z = add (add x y) (add z y).
intros.
unfold bool_algebra in H.
decompose
auto paramodulation.
qed.
*)
(*
theorem bool1372:
  \forall A: Set.
  \forall one,zero: A.
  \forall add,mult: A \to A \to A.
  \forall inv: A \to A.
  \forall H: bool_algebra A one zero add mult inv.
  \forall x,y,z:A.
    add x (add y z) = add (add x z) y.
intros.
unfold bool_algebra in H.
decompose
auto paramodulation.
qed.
*)
(*
theorem bool381:
  \forall A: Set.
  \forall one,zero: A.
  \forall add,mult: A \to A \to A.
  \forall inv: A \to A.
  \forall H: bool_algebra A one zero add mult inv.
  \forall x,y:A.
      add (inv x) y = add (mult x y) (inv x).
intros.
unfold bool_algebra in H.
decompose
auto paramodulation.
qed.
*)
(*
theorem bool5hint1:
  \forall A:Set.
  \forall one:A.
  \forall zero:A.
  \forall add: A \to A \to A.
  \forall mult: A \to A \to A.
  \forall inv: A \to A.
  \forall c1:(\forall x,y:A.(add x y) = (add y x)). 
  \forall c2:(\forall x,y:A.(mult x y) = (mult y x)). 
  \forall d1: (\forall x,y,z:A.
              (add x (mult y z)) = (mult (add x y) (add x z))).
  \forall d2: (\forall x,y,z:A.
              (mult x (add y z)) = (add (mult x y) (mult x z))).  
  \forall i1: (\forall x:A. (add x zero) = x).
  \forall i2: (\forall x:A. (mult x one) = x).   
  \forall inv1: (\forall x:A. (add x (inv x)) = one).  
  \forall inv2: (\forall x:A. (mult x (inv x)) = zero). 
  \forall hint1731:(\forall x,y:A. add (inv (add x y)) y = add y (inv x)).
  \forall hint1735:(\forall x,y:A. add (inv (add x y)) x = add x (inv y)).
  \forall hint623:(\forall x,y:A. inv (mult x y) = add (inv x) (inv (mult x y))).
  \forall x,y:A.
    (inv (mult x y)) = (add (inv x) (inv y)).
intros.
auto paramodulation.
qed.
*)
(*
theorem bool5hint2:
  \forall A:Set.
  \forall one:A.
  \forall zero:A.
  \forall add: A \to A \to A.
  \forall mult: A \to A \to A.
  \forall inv: A \to A.
  \forall c1:(\forall x,y:A.(add x y) = (add y x)). 
  \forall c2:(\forall x,y:A.(mult x y) = (mult y x)). 
  \forall d1: (\forall x,y,z:A.
              (add x (mult y z)) = (mult (add x y) (add x z))).
  \forall d2: (\forall x,y,z:A.
              (mult x (add y z)) = (add (mult x y) (mult x z))).  
  \forall i1: (\forall x:A. (add x zero) = x).
  \forall i2: (\forall x:A. (mult x one) = x).   
  \forall inv1: (\forall x:A. (add x (inv x)) = one).  
  \forall inv2: (\forall x:A. (mult x (inv x)) = zero). 
  \forall hint1731:(\forall x,y:A. add (inv (add x y)) y = add y (inv x)).
  \forall hint623:(\forall x,y:A. inv (mult x y) = add (inv x) (inv (mult x y))).
  \forall x,y:A.
    (inv (mult x y)) = (add (inv x) (inv y)).
intros.
auto paramodulation.
qed.
*)
(*
theorem bool5hint3:
  \forall A:Set.
  \forall one:A.
  \forall zero:A.
  \forall add: A \to A \to A.
  \forall mult: A \to A \to A.
  \forall inv: A \to A.
  \forall c1:(\forall x,y:A.(add x y) = (add y x)). 
  \forall c2:(\forall x,y:A.(mult x y) = (mult y x)). 
  \forall d1: (\forall x,y,z:A.
              (add x (mult y z)) = (mult (add x y) (add x z))).
  \forall d2: (\forall x,y,z:A.
              (mult x (add y z)) = (add (mult x y) (mult x z))).  
  \forall i1: (\forall x:A. (add x zero) = x).
  \forall i2: (\forall x:A. (mult x one) = x).   
  \forall inv1: (\forall x:A. (add x (inv x)) = one).  
  \forall inv2: (\forall x:A. (mult x (inv x)) = zero). 
  \forall hint1731:(\forall x,y:A. add (inv (add x y)) y = add y (inv x)).
  \forall hint609:(\forall x,y:A. inv x = add (inv (add y x)) (inv x)).
  \forall x,y:A.
    (inv (mult x y)) = (add (inv x) (inv y)).
intros.
auto paramodulation.
qed.
*)
theorem bool5:
  \forall A: Set.
  \forall one,zero: A.
  \forall add,mult: A \to A \to A.
  \forall inv: A \to A.
  \forall H: bool_algebra A one zero add mult inv.
  \forall x,y:A.
    (inv (mult x y)) = (add (inv x) (inv y)).
intros.
unfold bool_algebra in H.
decompose.
autobatch paramodulation timeout=120.
qed.

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

set "baseuri" "cic:/matita/test/prova".

include "../legacy/coq.ma".

theorem pippo: \forall (A,B:Prop). A \land B \to A.
 intros; decompose; assumption.
qed.  

inline procedural "cic:/matita/test/prova/pippo.con".

alias id "plus" = "cic:/Coq/Init/Peano/plus.con".
alias id "nat" = "cic:/Coq/Init/Datatypes/nat.ind#xpointer(1/1)".
alias id "eq" = "cic:/Coq/Init/Logic/eq.ind#xpointer(1/1)".
theorem plus_comm: \forall n:nat.\forall m:nat.eq nat (plus n m) (plus m n).
 intros; alias id "plus_comm" = "cic:/Coq/Arith/Plus/plus_comm.con".
apply plus_comm.
qed.
(*
include "LAMBDA-TYPES/LambdaDelta-1/preamble.ma".
alias id "ty3" = "cic:/matita/LAMBDA-TYPES/LambdaDelta-1/ty3/defs/ty3.ind#xpointer(1/1)".
alias id "pc3" = "cic:/matita/LAMBDA-TYPES/LambdaDelta-1/pc3/defs/pc3.con".
alias id "THead" = "cic:/matita/LAMBDA-TYPES/LambdaDelta-1/T/defs/T.ind#xpointer(1/1/3)".
alias id "T" = "cic:/matita/LAMBDA-TYPES/LambdaDelta-1/T/defs/T.ind#xpointer(1/1)".
alias id "G" = "cic:/matita/LAMBDA-TYPES/LambdaDelta-1/G/defs/G.ind#xpointer(1/1)".
alias id "Flat" = "cic:/matita/LAMBDA-TYPES/LambdaDelta-1/T/defs/K.ind#xpointer(1/1/2)".
alias id "Cast" = "cic:/matita/LAMBDA-TYPES/LambdaDelta-1/T/defs/F.ind#xpointer(1/1/2)".
alias id "C" = "cic:/matita/LAMBDA-TYPES/LambdaDelta-1/C/defs/C.ind#xpointer(1/1)".
theorem ty3_gen_cast:
 (\forall g:G
 .\forall c:C
  .\forall t1:T
   .\forall t2:T
    .\forall x:T
     .ty3 g c (THead (Flat Cast) t2 t1) x
      \rarr pc3 c t2 x\land ty3 g c t1 t2)
.
(* tactics: 80 *)
intros 6 (g c t1 t2 x H).
apply insert_eq;(* 6 P P P C I I 3 0 *)
[apply T(* dependent *)
|apply (THead (Flat Cast) t2 t1)(* dependent *)
|apply (\lambda t:T.ty3 g c t x)(* dependent *)
|intros 2 (y H0).
alias id "ty3_ind" = "cic:/matita/LAMBDA-TYPES/LambdaDelta-1/ty3/defs/ty3_ind.con".
elim H0 using ty3_ind names 0;(* 13 P C I I I I I I I C C C I 12 3 *)
[intros 11 (c0 t0 t UNUSED UNUSED u t3 UNUSED H4 H5 H6).
letin H7 \def (f_equal T T (\lambda e:T.e) u (THead (Flat Cast) t2 t1) H6).(* 6 C C C C C I *)
rewrite > H7 in H4:(%) as (H8).
cut (pc3 c0 t2 t3\land ty3 g c0 t1 t2) as H10;
[id
|apply H8.(* 1 I *)
apply refl_equal(* 2 C C *)
].
elim H10 using and_ind names 0.(* 5 P P C I I 3 0 *)
intros 2 (H11 H12).
apply conj;(* 4 C C I I *)
[alias id "pc3_t" = "cic:/matita/LAMBDA-TYPES/LambdaDelta-1/pc3/props/pc3_t.con".
apply pc3_t;(* 6 P C C I C I *)
[apply t3(* dependent *)
|apply H11(* assumption *)
|apply H5(* assumption *)
]
|apply H12(* assumption *)
]
|intros 3 (c0 m H1).
alias id "K" = "cic:/matita/LAMBDA-TYPES/LambdaDelta-1/T/defs/K.ind#xpointer(1/1)".
cut match THead (Flat Cast) t2 t1 in T return \lambda _:T.Prop with 
[TSort (_:nat)\rArr True
|TLRef (_:nat)\rArr False
|THead (_:K) (_:T) (_:T)\rArr False] as H2;
[id
|rewrite < H1 in \vdash (%).
apply I
].
clearbody H2.
change in H2:(%) with match THead (Flat Cast) t2 t1 in T return \lambda _:T.Prop with 
[TSort (_:nat)\rArr True
|TLRef (_:nat)\rArr False
|THead (_:K) (_:T) (_:T)\rArr False].
elim H2 using False_ind names 0(* 2 C I 2 0 *)
|intros 9 (n c0 d u UNUSED t UNUSED UNUSED H4).
cut match THead (Flat Cast) t2 t1 in T return \lambda _:T.Prop with 
[TSort (_:nat)\rArr False
|TLRef (_:nat)\rArr True
|THead (_:K) (_:T) (_:T)\rArr False] as H5;
[id
|rewrite < H4 in \vdash (%).
apply I
].
clearbody H5.
change in H5:(%) with match THead (Flat Cast) t2 t1 in T return \lambda _:T.Prop with 
[TSort (_:nat)\rArr False
|TLRef (_:nat)\rArr True
|THead (_:K) (_:T) (_:T)\rArr False].
elim H5 using False_ind names 0(* 2 C I 2 0 *)
|intros 9 (n c0 d u UNUSED t UNUSED UNUSED H4).
cut match THead (Flat Cast) t2 t1 in T return \lambda _:T.Prop with 
[TSort (_:nat)\rArr False
|TLRef (_:nat)\rArr True
|THead (_:K) (_:T) (_:T)\rArr False] as H5;
[id
|rewrite < H4 in \vdash (%).
apply I
].
clearbody H5.
change in H5:(%) with match THead (Flat Cast) t2 t1 in T return \lambda _:T.Prop with 
[TSort (_:nat)\rArr False
|TLRef (_:nat)\rArr True
|THead (_:K) (_:T) (_:T)\rArr False].
elim H5 using False_ind names 0(* 2 C I 2 0 *)
|intros 14 (c0 u t UNUSED UNUSED b t0 t3 UNUSED UNUSED t4 UNUSED UNUSED H7).
alias id "F" = "cic:/matita/LAMBDA-TYPES/LambdaDelta-1/T/defs/F.ind#xpointer(1/1)".
alias id "B" = "cic:/matita/LAMBDA-TYPES/LambdaDelta-1/T/defs/B.ind#xpointer(1/1)".
cut match THead (Flat Cast) t2 t1 in T return \lambda _:T.Prop with 
[TSort (_:nat)\rArr False
|TLRef (_:nat)\rArr False
|THead (k:K) (_:T) (_:T)\rArr 
 match k in K return \lambda _:K.Prop with 
 [Bind (_:B)\rArr True|Flat (_:F)\rArr False]] as H8;
[id
|rewrite < H7 in \vdash (%).
apply I
].
clearbody H8.
change in H8:(%) with match THead (Flat Cast) t2 t1 in T return \lambda _:T.Prop with 
[TSort (_:nat)\rArr False
|TLRef (_:nat)\rArr False
|THead (k:K) (_:T) (_:T)\rArr 
 match k in K return \lambda _:K.Prop with 
 [Bind (_:B)\rArr True|Flat (_:F)\rArr False]].
elim H8 using False_ind names 0(* 2 C I 2 0 *)
|intros 10 (c0 w u UNUSED UNUSED v t UNUSED UNUSED H5).
cut match THead (Flat Cast) t2 t1 in T return \lambda _:T.Prop with 
[TSort (_:nat)\rArr False
|TLRef (_:nat)\rArr False
|THead (k:K) (_:T) (_:T)\rArr 
 match k in K return \lambda _:K.Prop with 
 [Bind (_:B)\rArr False
 |Flat (f:F)\rArr 
  match f in F return \lambda _:F.Prop with 
  [Appl\rArr True|Cast\rArr False]]] as H6;
[id
|rewrite < H5 in \vdash (%).
apply I
].
clearbody H6.
change in H6:(%) with match THead (Flat Cast) t2 t1 in T return \lambda _:T.Prop with 
[TSort (_:nat)\rArr False
|TLRef (_:nat)\rArr False
|THead (k:K) (_:T) (_:T)\rArr 
 match k in K return \lambda _:K.Prop with 
 [Bind (_:B)\rArr False
 |Flat (f:F)\rArr 
  match f in F return \lambda _:F.Prop with 
  [Appl\rArr True|Cast\rArr False]]].
elim H6 using False_ind names 0(* 2 C I 2 0 *)
|intros 9 (c0 t0 t3 H1 H2 t4 UNUSED UNUSED H5).
letin H6 \def (f_equal T T
 (\lambda e:T
  .match e in T return \lambda _:T.T with 
   [TSort (_:nat)\rArr t3
   |TLRef (_:nat)\rArr t3
   |THead (_:K) (t:T) (_:T)\rArr t]) (THead (Flat Cast) t3 t0)
 (THead (Flat Cast) t2 t1) H5).(* 6 C C C C C I *)
letin H7 \def (f_equal T T
 (\lambda e:T
  .match e in T return \lambda _:T.T with 
   [TSort (_:nat)\rArr t0
   |TLRef (_:nat)\rArr t0
   |THead (_:K) (_:T) (t:T)\rArr t]) (THead (Flat Cast) t3 t0)
 (THead (Flat Cast) t2 t1) H5).(* 6 C C C C C I *)
cut (t3=t2\rarr pc3 c0 t2 t3\land ty3 g c0 t1 t2) as DEFINED;
[id
|intros 1 (H8).
rewrite > H8 in H2:(%) as (UNUSED).
rewrite > H8 in H1:(%) as (H12).
rewrite > H8 in \vdash (%).
clearbody H7.
change in H7:(%) with (match THead (Flat Cast) t3 t0 in T return \lambda _:T.T with 
 [TSort (_:nat)\rArr t0
 |TLRef (_:nat)\rArr t0
 |THead (_:K) (_:T) (t:T)\rArr t]
 =match THead (Flat Cast) t2 t1 in T return \lambda _:T.T with 
  [TSort (_:nat)\rArr t0
  |TLRef (_:nat)\rArr t0
  |THead (_:K) (_:T) (t:T)\rArr t]).
rewrite > H7 in H12:(%) as (H14).
apply conj;(* 4 C C I I *)
[alias id "pc3_refl" = "cic:/matita/LAMBDA-TYPES/LambdaDelta-1/pc3/props/pc3_refl.con".
apply pc3_refl(* 2 C C *)
|apply H14(* assumption *)
]
].
apply DEFINED.(* 1 I *)
apply H6(* assumption *)
]
|apply H(* assumption *)
].
qed.
*)
(*
include "nat/orders.ma".

theorem le_inv:
 \forall P:nat \to Prop
 .\forall p2
  .\forall p1
   .p2 <= p1 \to
    (p1 = p2 \to P p2) \to 
     (\forall n1
      .p2 <= n1 \to 
      (p1 = n1 \to P n1) \to 
      p1 = S n1 \to P (S n1)) \to 
      P p1.
 intros 4; elim H names 0; clear H p1; intros;
 [ apply H; reflexivity
 | apply H3; clear H3; intros;
   [ apply H | apply H1; clear H1; intros; subst;
     [ apply H2; apply H3 | ]
   | reflexivity
 ]
*)

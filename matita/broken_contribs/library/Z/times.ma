(**************************************************************************)
(*       __                                                               *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||       A.Asperti, C.Sacerdoti Coen,                          *)
(*      ||A||       E.Tassi, S.Zacchiroli                                 *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU Lesser General Public License Version 2.1         *)
(*                                                                        *)
(**************************************************************************)

include "nat/lt_arith.ma".
include "Z/plus.ma".

definition Ztimes :Z \to Z \to Z \def
\lambda x,y.
  match x with
    [ OZ \Rightarrow OZ
    | (pos m) \Rightarrow
        match y with
         [ OZ \Rightarrow OZ
         | (pos n) \Rightarrow (pos (pred ((S m) * (S n))))
         | (neg n) \Rightarrow (neg (pred ((S m) * (S n))))]
    | (neg m) \Rightarrow
        match y with
         [ OZ \Rightarrow OZ
         | (pos n) \Rightarrow (neg (pred ((S m) * (S n))))
         | (neg n) \Rightarrow (pos (pred ((S m) * (S n))))]].
         
interpretation "integer times" 'times x y = (Ztimes x y).

theorem Ztimes_z_OZ:  \forall z:Z. z*OZ = OZ.
intro.elim z.
simplify.reflexivity.
simplify.reflexivity.
simplify.reflexivity.
qed.

definition Zone \def pos O.

theorem Ztimes_neg_Zopp: \forall n:nat.\forall x:Z.
neg n * x = - (pos n * x).
intros.elim x.
simplify.reflexivity.
simplify.reflexivity.
simplify.reflexivity.
qed.

theorem symmetric_Ztimes : symmetric Z Ztimes.
change with (\forall x,y:Z. x*y = y*x).
intros.elim x.rewrite > Ztimes_z_OZ.reflexivity.
elim y.simplify.reflexivity. 
change with (pos (pred ((S n) * (S n1))) = pos (pred ((S n1) * (S n)))).
rewrite < sym_times.reflexivity.
change with (neg (pred ((S n) * (S n1))) = neg (pred ((S n1) * (S n)))).
rewrite < sym_times.reflexivity.
elim y.simplify.reflexivity.
change with (neg (pred ((S n) * (S n1))) = neg (pred ((S n1) * (S n)))).
rewrite < sym_times.reflexivity.
change with (pos (pred ((S n) * (S n1))) = pos (pred ((S n1) * (S n)))).
rewrite < sym_times.reflexivity.
qed.

variant sym_Ztimes : \forall x,y:Z. x*y = y*x
\def symmetric_Ztimes.

theorem Ztimes_Zone_l: \forall z:Z. Ztimes Zone z = z.
intro.unfold Zone.simplify.
elim z;simplify
  [reflexivity
  |rewrite < plus_n_O.reflexivity
  |rewrite < plus_n_O.reflexivity
  ]
qed.

theorem Ztimes_Zone_r: \forall z:Z. Ztimes z Zone = z.
intro.
rewrite < sym_Ztimes.
apply Ztimes_Zone_l.
qed.

theorem associative_Ztimes: associative Z Ztimes.
unfold associative.
intros.elim x.
  simplify.reflexivity. 
  elim y.
    simplify.reflexivity.
    elim z.
      simplify.reflexivity.
      change with 
       (pos (pred ((S (pred ((S n) * (S n1)))) * (S n2))) =
       pos (pred ((S n) * (S (pred ((S n1) * (S n2))))))).
        rewrite < S_pred.rewrite < S_pred.rewrite < assoc_times.reflexivity.
         apply lt_O_times_S_S.apply lt_O_times_S_S.
      change with 
       (neg (pred ((S (pred ((S n) * (S n1)))) * (S n2))) =
       neg (pred ((S n) * (S (pred ((S n1) * (S n2))))))).
        rewrite < S_pred.rewrite < S_pred.rewrite < assoc_times.reflexivity.
         apply lt_O_times_S_S.apply lt_O_times_S_S.
    elim z.
      simplify.reflexivity.
      change with 
       (neg (pred ((S (pred ((S n) * (S n1)))) * (S n2))) =
       neg (pred ((S n) * (S (pred ((S n1) * (S n2))))))).
        rewrite < S_pred.rewrite < S_pred.rewrite < assoc_times.reflexivity.
         apply lt_O_times_S_S.apply lt_O_times_S_S.
      change with 
       (pos (pred ((S (pred ((S n) * (S n1)))) * (S n2))) =
       pos(pred ((S n) * (S (pred ((S n1) * (S n2))))))).
        rewrite < S_pred.rewrite < S_pred.rewrite < assoc_times.reflexivity.
        apply lt_O_times_S_S.apply lt_O_times_S_S.
  elim y.
    simplify.reflexivity.
    elim z.
      simplify.reflexivity.
      change with 
       (neg (pred ((S (pred ((S n) * (S n1)))) * (S n2))) =
       neg (pred ((S n) * (S (pred ((S n1) * (S n2))))))).
        rewrite < S_pred.rewrite < S_pred.rewrite < assoc_times.reflexivity.
         apply lt_O_times_S_S.apply lt_O_times_S_S.
      change with 
       (pos (pred ((S (pred ((S n) * (S n1)))) * (S n2))) =
       pos (pred ((S n) * (S (pred ((S n1) * (S n2))))))).
        rewrite < S_pred.rewrite < S_pred.rewrite < assoc_times.reflexivity.
         apply lt_O_times_S_S.apply lt_O_times_S_S.
    elim z.
      simplify.reflexivity.
      change with 
       (pos (pred ((S (pred ((S n) * (S n1)))) * (S n2))) =
       pos (pred ((S n) * (S (pred ((S n1) * (S n2))))))).
        rewrite < S_pred.rewrite < S_pred.rewrite < assoc_times.reflexivity.
         apply lt_O_times_S_S.apply lt_O_times_S_S.
      change with 
       (neg (pred ((S (pred ((S n) * (S n1)))) * (S n2))) =
       neg(pred ((S n) * (S (pred ((S n1) * (S n2))))))).
        rewrite < S_pred.rewrite < S_pred.rewrite < assoc_times.reflexivity.
         apply lt_O_times_S_S.apply lt_O_times_S_S.
qed.

variant assoc_Ztimes : \forall x,y,z:Z. 
(x * y) * z = x * (y * z) \def 
associative_Ztimes.

lemma times_minus1: \forall n,p,q:nat. lt q p \to
(S n) * (S (pred ((S p) - (S q)))) =
pred ((S n) * (S p)) - pred ((S n) * (S q)).
intros.
rewrite < S_pred.  
rewrite > minus_pred_pred.
rewrite < distr_times_minus. 
reflexivity.
(* we now close all positivity conditions *)
apply lt_O_times_S_S.                    
apply lt_O_times_S_S.
simplify.unfold lt.
apply le_SO_minus.  exact H.
qed.

lemma Ztimes_Zplus_pos_neg_pos: \forall n,p,q:nat.
(pos n)*((neg p)+(pos q)) = (pos n)*(neg p)+ (pos n)*(pos q). 
intros.
simplify. 
change in match (p + n * (S p)) with (pred ((S n) * (S p))).
change in match (q + n * (S q)) with (pred ((S n) * (S q))).
rewrite < nat_compare_pred_pred.
rewrite < nat_compare_times_l.
rewrite < nat_compare_S_S.
apply (nat_compare_elim p q).
intro.
(* uff *)
change with (pos (pred ((S n) * (S (pred ((S q) - (S p)))))) =
            pos (pred ((pred ((S n) * (S q))) - (pred ((S n) * (S p)))))).
rewrite < (times_minus1 n q p H).reflexivity.
intro.rewrite < H.simplify.reflexivity.
intro.
change with (neg (pred ((S n) * (S (pred ((S p) - (S q)))))) =
            neg (pred ((pred ((S n) * (S p))) - (pred ((S n) * (S q)))))). 
rewrite < (times_minus1 n p q H).reflexivity.                                 
(* two more positivity conditions from nat_compare_pred_pred *)   
apply lt_O_times_S_S.  
apply lt_O_times_S_S. 
qed. 

lemma Ztimes_Zplus_pos_pos_neg: \forall n,p,q:nat.
(pos n)*((pos p)+(neg q)) = (pos n)*(pos p)+ (pos n)*(neg q).
intros.
rewrite < sym_Zplus.
rewrite > Ztimes_Zplus_pos_neg_pos.
apply sym_Zplus.
qed.

lemma distributive2_Ztimes_pos_Zplus: 
distributive2 nat Z (\lambda n,z. (pos n) * z) Zplus.
change with (\forall n,y,z.
(pos n) * (y + z) = (pos n) * y + (pos n) * z).  
intros.elim y.
  reflexivity.
  elim z.
    reflexivity.
    change with
     (pos (pred ((S n) * ((S n1) + (S n2)))) =
     pos (pred ((S n) * (S n1) + (S n) * (S n2)))).
      rewrite < distr_times_plus.reflexivity.
    apply Ztimes_Zplus_pos_pos_neg.
  elim z.
    reflexivity.
    apply Ztimes_Zplus_pos_neg_pos.
    change with
     (neg (pred ((S n) * ((S n1) + (S n2)))) =
     neg (pred ((S n) * (S n1) + (S n) * (S n2)))).
    rewrite < distr_times_plus.reflexivity.
qed.

variant distr_Ztimes_Zplus_pos: \forall n,y,z.
(pos n) * (y + z) = ((pos n) * y + (pos n) * z) \def
distributive2_Ztimes_pos_Zplus.

lemma distributive2_Ztimes_neg_Zplus : 
distributive2 nat Z (\lambda n,z. (neg n) * z) Zplus.
change with (\forall n,y,z.
(neg n) * (y + z) = (neg n) * y + (neg n) * z).  
intros.
rewrite > Ztimes_neg_Zopp. 
rewrite > distr_Ztimes_Zplus_pos.
rewrite > Zopp_Zplus.
rewrite < Ztimes_neg_Zopp. rewrite < Ztimes_neg_Zopp.
reflexivity.
qed.

variant distr_Ztimes_Zplus_neg: \forall n,y,z.
(neg n) * (y + z) = (neg n) * y + (neg n) * z \def
distributive2_Ztimes_neg_Zplus.

theorem distributive_Ztimes_Zplus: distributive Z Ztimes Zplus.
change with (\forall x,y,z:Z. x * (y + z) = x*y + x*z).
intros.elim x.
(* case x = OZ *)
simplify.reflexivity.
(* case x = pos n *)
apply distr_Ztimes_Zplus_pos.
(* case x = neg n *)
apply distr_Ztimes_Zplus_neg.
qed.

variant distr_Ztimes_Zplus: \forall x,y,z.
x * (y + z) = x*y + x*z \def
distributive_Ztimes_Zplus.

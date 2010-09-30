(**************************************************************************)
(*       ___	                                                            *)
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

include "Z/z.ma".
include "nat/minus.ma".

definition Zplus :Z \to Z \to Z \def
\lambda x,y.
  match x with
    [ OZ \Rightarrow y
    | (pos m) \Rightarrow
        match y with
         [ OZ \Rightarrow x
         | (pos n) \Rightarrow (pos (pred ((S m)+(S n))))
         | (neg n) \Rightarrow 
              match nat_compare m n with
                [ LT \Rightarrow (neg (pred (n-m)))
                | EQ \Rightarrow OZ
                | GT \Rightarrow (pos (pred (m-n)))] ]
    | (neg m) \Rightarrow
        match y with
         [ OZ \Rightarrow x
         | (pos n) \Rightarrow 
              match nat_compare m n with
                [ LT \Rightarrow (pos (pred (n-m)))
                | EQ \Rightarrow OZ
                | GT \Rightarrow (neg (pred (m-n)))]     
         | (neg n) \Rightarrow (neg (pred ((S m)+(S n))))] ].

interpretation "integer plus" 'plus x y = (Zplus x y).

theorem eq_plus_Zplus: \forall n,m:nat. Z_of_nat (n+m) =
Z_of_nat n + Z_of_nat m.
intro.cases n;intro
  [reflexivity
  |cases m
    [simplify.rewrite < plus_n_O.reflexivity
    |simplify.reflexivity.
    ]]
qed.

theorem Zplus_z_OZ:  \forall z:Z. z+OZ = z.
intro.elim z.
simplify.reflexivity.
simplify.reflexivity.
simplify.reflexivity.
qed.

(* theorem symmetric_Zplus: symmetric Z Zplus. *)

theorem sym_Zplus : \forall x,y:Z. x+y = y+x.
intros.elim x.rewrite > Zplus_z_OZ.reflexivity.
elim y.simplify.reflexivity.
simplify.
rewrite < plus_n_Sm. rewrite < plus_n_Sm.rewrite < sym_plus.reflexivity.
simplify.
rewrite > nat_compare_n_m_m_n.
simplify.elim nat_compare.simplify.reflexivity.
simplify. reflexivity.
simplify. reflexivity.
elim y.simplify.reflexivity.
simplify.rewrite > nat_compare_n_m_m_n.
simplify.elim nat_compare.simplify.reflexivity.
simplify. reflexivity.
simplify. reflexivity.
simplify.rewrite < plus_n_Sm. rewrite < plus_n_Sm.rewrite < sym_plus.reflexivity.
qed.

theorem Zpred_Zplus_neg_O : \forall z:Z. Zpred z = (neg O)+z.
intros.elim z.
  simplify.reflexivity.
  elim n.
    simplify.reflexivity.
    simplify.reflexivity.
  simplify.reflexivity.
qed.

theorem Zsucc_Zplus_pos_O : \forall z:Z. Zsucc z = (pos O)+z.
intros.elim z.
  simplify.reflexivity.
  simplify.reflexivity.
  elim n.
    simplify.reflexivity.
    simplify.reflexivity.
qed.

theorem Zplus_pos_pos:
\forall n,m. (pos n)+(pos m) = (Zsucc (pos n))+(Zpred (pos m)).
intros.
elim n.elim m.
simplify.reflexivity.
simplify.reflexivity.
elim m.
simplify.rewrite < plus_n_Sm.
rewrite < plus_n_O.reflexivity.
simplify.rewrite < plus_n_Sm.
rewrite < plus_n_Sm.reflexivity.
qed.

theorem Zplus_pos_neg:
\forall n,m. (pos n)+(neg m) = (Zsucc (pos n))+(Zpred (neg m)).
intros.reflexivity.
qed.

theorem Zplus_neg_pos :
\forall n,m. (neg n)+(pos m) = (Zsucc (neg n))+(Zpred (pos m)).
intros.
elim n.elim m.
simplify.reflexivity.
simplify.reflexivity.
elim m.
simplify.reflexivity.
simplify.reflexivity.
qed.

theorem Zplus_neg_neg:
\forall n,m. (neg n)+(neg m) = (Zsucc (neg n))+(Zpred (neg m)).
intros.
elim n.elim m.
simplify.reflexivity.
simplify.reflexivity.
elim m.
simplify.rewrite > plus_n_Sm.reflexivity.
simplify.rewrite > plus_n_Sm.reflexivity.
qed.

theorem Zplus_Zsucc_Zpred:
\forall x,y. x+y = (Zsucc x)+(Zpred y).
intros.elim x. 
  elim y.
    simplify.reflexivity.
    rewrite < Zsucc_Zplus_pos_O.rewrite > Zsucc_Zpred.reflexivity.
    simplify.reflexivity.
  elim y.
    simplify.reflexivity.
    apply Zplus_pos_pos.
    apply Zplus_pos_neg.
  elim y.
    rewrite < sym_Zplus.rewrite < (sym_Zplus (Zpred OZ)).
     rewrite < Zpred_Zplus_neg_O.rewrite > Zpred_Zsucc.simplify.reflexivity.
    apply Zplus_neg_pos.
    rewrite < Zplus_neg_neg.reflexivity.
qed.

theorem Zplus_Zsucc_pos_pos : 
\forall n,m. (Zsucc (pos n))+(pos m) = Zsucc ((pos n)+(pos m)).
intros.reflexivity.
qed.

theorem Zplus_Zsucc_pos_neg: 
\forall n,m. (Zsucc (pos n))+(neg m) = (Zsucc ((pos n)+(neg m))).
intros.
apply (nat_elim2
(\lambda n,m. (Zsucc (pos n))+(neg m) = (Zsucc ((pos n)+(neg m))))).intro.
intros.elim n1.
simplify. reflexivity.
elim n2.simplify. reflexivity.
simplify. reflexivity.
intros. elim n1.
simplify. reflexivity.
simplify.reflexivity.
intros.
rewrite < (Zplus_pos_neg ? m1).
elim H.reflexivity.
qed.

theorem Zplus_Zsucc_neg_neg : 
\forall n,m. Zsucc (neg n) + neg m = Zsucc (neg n + neg m).
intros.
apply (nat_elim2
(\lambda n,m. Zsucc (neg n) + neg m = Zsucc (neg n + neg m))).intro.
intros.elim n1.
simplify. reflexivity.
elim n2.simplify. reflexivity.
simplify. reflexivity.
intros. elim n1.
simplify. reflexivity.
simplify.reflexivity.
intros.
rewrite < (Zplus_neg_neg ? m1).
reflexivity.
qed.

theorem Zplus_Zsucc_neg_pos: 
\forall n,m. Zsucc (neg n)+(pos m) = Zsucc ((neg n)+(pos m)).
intros.
apply (nat_elim2
(\lambda n,m. Zsucc (neg n) + (pos m) = Zsucc (neg n + pos m))).
intros.elim n1.
simplify. reflexivity.
elim n2.simplify. reflexivity.
simplify. reflexivity.
intros. elim n1.
simplify. reflexivity.
simplify.reflexivity.
intros.
rewrite < H.
rewrite < (Zplus_neg_pos ? (S m1)).
reflexivity.
qed.

theorem Zplus_Zsucc : \forall x,y:Z. (Zsucc x)+y = Zsucc (x+y).
intros.elim x.
  elim y.
    simplify. reflexivity.
    simplify.reflexivity.
    rewrite < Zsucc_Zplus_pos_O.reflexivity.
  elim y.
    rewrite < (sym_Zplus OZ).reflexivity.
    apply Zplus_Zsucc_pos_pos.
    apply Zplus_Zsucc_pos_neg.
  elim y.
    rewrite < sym_Zplus.rewrite < (sym_Zplus OZ).simplify.reflexivity.
    apply Zplus_Zsucc_neg_pos.
    apply Zplus_Zsucc_neg_neg.
qed.

theorem Zplus_Zpred: \forall x,y:Z. (Zpred x)+y = Zpred (x+y).
intros.
cut (Zpred (x+y) = Zpred ((Zsucc (Zpred x))+y)).
rewrite > Hcut.
rewrite > Zplus_Zsucc.
rewrite > Zpred_Zsucc.
reflexivity.
rewrite > Zsucc_Zpred.
reflexivity.
qed.


theorem associative_Zplus: associative Z Zplus.
change with (\forall x,y,z:Z. (x + y) + z = x + (y + z)). 
(* simplify. *)
intros.elim x.
  simplify.reflexivity.
  elim n.
    rewrite < Zsucc_Zplus_pos_O.rewrite < Zsucc_Zplus_pos_O.
     rewrite > Zplus_Zsucc.reflexivity.
    rewrite > (Zplus_Zsucc (pos n1)).rewrite > (Zplus_Zsucc (pos n1)).
     rewrite > (Zplus_Zsucc ((pos n1)+y)).apply eq_f.assumption.
  elim n.
    rewrite < (Zpred_Zplus_neg_O (y+z)).rewrite < (Zpred_Zplus_neg_O y).
     rewrite < Zplus_Zpred.reflexivity.
    rewrite > (Zplus_Zpred (neg n1)).rewrite > (Zplus_Zpred (neg n1)).
     rewrite > (Zplus_Zpred ((neg n1)+y)).apply eq_f.assumption.
qed.

variant assoc_Zplus : \forall x,y,z:Z.  (x+y)+z = x+(y+z)
\def associative_Zplus.

(* Zopp *)
definition Zopp : Z \to Z \def
\lambda x:Z. match x with
[ OZ \Rightarrow OZ
| (pos n) \Rightarrow (neg n)
| (neg n) \Rightarrow (pos n) ].

interpretation "integer unary minus" 'uminus x = (Zopp x).

theorem eq_OZ_Zopp_OZ : OZ = (- OZ).
reflexivity.
qed.

theorem Zopp_Zplus: \forall x,y:Z. -(x+y) = -x + -y.
intros.
elim x.elim y.
simplify. reflexivity.
simplify. reflexivity.
simplify. reflexivity.
elim y.
simplify. reflexivity.
simplify. reflexivity.
simplify. apply nat_compare_elim.
intro.simplify.reflexivity.
intro.simplify.reflexivity.
intro.simplify.reflexivity.
elim y.
simplify. reflexivity.
simplify. apply nat_compare_elim.
intro.simplify.reflexivity.
intro.simplify.reflexivity.
intro.simplify.reflexivity.
simplify.reflexivity.
qed.

theorem Zopp_Zopp: \forall x:Z. --x = x.
intro. elim x.
reflexivity.reflexivity.reflexivity.
qed.

theorem Zplus_Zopp: \forall x:Z. x+ -x = OZ.
intro.elim x.
apply refl_eq.
simplify.
rewrite > nat_compare_n_n.
simplify.apply refl_eq.
simplify.
rewrite > nat_compare_n_n.
simplify.apply refl_eq.
qed.

theorem injective_Zplus_l: \forall x:Z.injective Z Z (\lambda y.y+x).
intro.simplify.intros (z y).
rewrite < Zplus_z_OZ.
rewrite < (Zplus_z_OZ y).
rewrite < (Zplus_Zopp x).
rewrite < assoc_Zplus.
rewrite < assoc_Zplus.
apply eq_f2
  [assumption|reflexivity]
qed.

theorem injective_Zplus_r: \forall x:Z.injective Z Z (\lambda y.x+y).
intro.simplify.intros (z y).
apply (injective_Zplus_l x).
rewrite < sym_Zplus.
rewrite > H.
apply sym_Zplus.
qed.

(* minus *)
definition Zminus : Z \to Z \to Z \def \lambda x,y:Z. x + (-y).

interpretation "integer minus" 'minus x y = (Zminus x y).

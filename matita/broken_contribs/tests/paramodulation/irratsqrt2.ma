(**************************************************************************)
(*       ___	                                                            *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||       A.Asperti, C.Sacerdoti Coen,                          *)
(*      ||A||       E.Tassi, S.Zacchiroli                                 *)
(*      \   /                                                             *)
(*       \ /        Matita is distributed under the terms of the          *)
(*        v         GNU Lesser General Public License Version 2.1         *)
(*                                                                        *)
(**************************************************************************)



include "nat/times.ma".
include "nat/minus.ma".

theorem prova :
  \forall n,m:nat.
  \forall P:nat \to Prop.
  \forall H:P (S (S O)).
  \forall H:P (S (S (S O))).
  \forall H1: \forall x.P x \to O = x.
   O = S (S (S (S (S O)))).
   intros.
   autobatch.
 qed.
 
theorem example2:
\forall x: nat. (x+S O)*(x-S O) = x*x - S O.
intro;
apply (nat_case x);
 [ autobatch timeout = 1.|intro.autobatch timeout = 1.]
qed.

theorem irratsqrt2_byhand:
  \forall A:Set.
  \forall m:A \to A \to A.
  \forall divides: A \to A \to Prop.
  \forall o,a,b,two:A.
  \forall H1:\forall x.m o x = x.
  \forall H1:\forall x.m x o = x.
  \forall H1:\forall x,y,z.m x (m y z) = m (m x y) z.
  \forall H1:\forall x.m x o = x.
  \forall H2:\forall x,y.m x y = m y x.
  \forall H3:\forall x,y,z. m x y = m x z \to y = z. 
  (* \forall H4:\forall x,y.(\exists z.m x z = y) \to divides x y. *)
  \forall H4:\forall x,y.(divides x y \to (\exists z.m x z = y)). 
  \forall H4:\forall x,y,z.m x z = y \to divides x y.
  \forall H4:\forall x,y.divides two (m x y) \to divides two x ∨ divides two y.
  \forall H5:m a a = m two (m b b).
  \forall H6:\forall x.divides x a \to divides x b \to x = o.
  two = o.
  intros.
  cut (divides two a);
    [2:elim (H8 a a);[assumption.|assumption|rewrite > H9.autobatch.]
    |elim (H6 ? ? Hcut).
     cut (divides two b);
       [ apply (H10 ? Hcut Hcut1).
       | elim (H8 b b);[assumption.|assumption|
         apply (H7 ? ? (m a1 a1));
         apply (H5 two ? ?);rewrite < H9.
         rewrite < H11.rewrite < H2.
         apply eq_f.rewrite > H2.rewrite > H4.reflexivity.
         ]
         ]
         ]
qed.
         
theorem irratsqrt2_byhand':
  \forall A:Set.
  \forall m,f:A \to A \to A.
  \forall divides: A \to A \to Prop.
  \forall o,a,b,two:A.
  \forall H1:\forall x.m o x = x.
  \forall H1:\forall x.m x o = x.
  \forall H1:\forall x,y,z.m x (m y z) = m (m x y) z.
  \forall H1:\forall x.m x o = x.
  \forall H2:\forall x,y.m x y = m y x.
  \forall H3:\forall x,y,z. m x y = m x z \to y = z. 
  (* \forall H4:\forall x,y.(\exists z.m x z = y) \to divides x y. *)
  \forall H4:\forall x,y.(divides x y \to m x (f x y) = y). 
  \forall H4:\forall x,y,z.m x z = y \to divides x y.
  \forall H4:\forall x,y.divides two (m x y) \to divides two x ∨ divides two y.
  \forall H5:m a a = m two (m b b).
  \forall H6:\forall x.divides x a \to divides x b \to x = o.
  two = o.
  intros.
  cut (divides two a);
    [2:elim (H8 a a);[assumption.|assumption|rewrite > H9.autobatch.]
    |(*elim (H6 ? ? Hcut). *)
     cut (divides two b);
       [ apply (H10 ? Hcut Hcut1).
       | elim (H8 b b);[assumption.|assumption|
       
         apply (H7 ? ? (m (f two a) (f two a)));
         apply (H5 two ? ?);
         rewrite < H9.
         rewrite < (H6 two a Hcut) in \vdash (? ? ? %).
         rewrite < H2.apply eq_f.
         rewrite < H4 in \vdash (? ? ? %).
         rewrite > H2.reflexivity.
         ]
         ]
         ]
qed.  
     
theorem irratsqrt2:
  \forall A:Set.
  \forall m,f:A \to A \to A.
  \forall divides: A \to A \to Prop.
  \forall o,a,b,two:A.
  \forall H1:\forall x.m o x = x.
  \forall H1:\forall x.m x o = x.
  \forall H1:\forall x,y,z.m x (m y z) = m (m x y) z.
  \forall H1:\forall x.m x o = x.
  \forall H2:\forall x,y.m x y = m y x.
  \forall H3:\forall x,y,z. m x y = m x z \to y = z. 
  (* \forall H4:\forall x,y.(\exists z.m x z = y) \to divides x y. *)
  \forall H4:\forall x,y.(divides x y \to m x (f x y) = y). 
  \forall H4:\forall x,y,z.m x z = y \to divides x y.
  \forall H4:\forall x.divides two (m x x) \to divides two x.
  \forall H5:m a a = m two (m b b).
  \forall H6:\forall x.divides x a \to divides x b \to x = o.
  two = o.
intros.
autobatch depth = 5 timeout = 180.
qed.

(* time: 146s *)

 
(* intermediate attempts 

  cut (divides two a);[|
    (* apply H8;apply (H7 two (m a a) (m b b));symmetry;assumption. *)
    autobatch depth = 4 width = 3 use_paramod = false. ]
  (*autobatch depth = 5.*)
  
  apply H10;
  [ assumption.
  |(*autobatch depth = 4.*) apply H8;   
         (*autobatch.*)
         apply (H7 ? ? (m (f two a) (f two a)));
         apply (H5 two ? ?);
         cut ((\lambda x:A.m x (m two ?)=m x (m b b))?);
         [|||simplify;
         autobatch paramodulation.
         (*autobatch new.*)
         rewrite < H9.
         rewrite < (H6 two a Hcut) in \vdash (? ? ? %).
         rewrite < H2.apply eq_f.
         rewrite < H4 in \vdash (? ? ? %).
         rewrite > H2.reflexivity.
  ]
         
qed.
*)    

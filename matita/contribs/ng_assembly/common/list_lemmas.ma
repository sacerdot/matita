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

(* ********************************************************************** *)
(*                          Progetto FreeScale                            *)
(*                                                                        *)
(*   Sviluppato da: Ing. Cosimo Oliboni, oliboni@cs.unibo.it              *)
(*   Sviluppo: 2008-2010                                                  *)
(*                                                                        *)
(* ********************************************************************** *)

include "common/list.ma".

(* *************** *)
(* LISTE GENERICHE *)
(* *************** *)

nlemma list_destruct_1 : ∀T.∀x1,x2:T.∀y1,y2:list T.cons T x1 y1 = cons T x2 y2 → x1 = x2.
 #T; #x1; #x2; #y1; #y2; #H;
 nchange with (match cons T x2 y2 with [ nil ⇒ False | cons a _ ⇒ x1 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma list_destruct_2 : ∀T.∀x1,x2:T.∀y1,y2:list T.cons T x1 y1 = cons T x2 y2 → y1 = y2.
 #T; #x1; #x2; #y1; #y2; #H;
 nchange with (match cons T x2 y2 with [ nil ⇒ False | cons _ b ⇒ y1 = b ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

(* !!! da togliere *)
nlemma list_destruct_cons_nil : ∀T.∀x:T.∀y:list T.cons T x y = nil T → False.
 #T; #x; #y; #H;
 nchange with (match cons T x y with [ nil ⇒ True | cons a b ⇒ False ]);
 nrewrite > H;
 nnormalize;
 napply I.
nqed.

(* !!! da togliere *)
nlemma list_destruct_nil_cons : ∀T.∀x:T.∀y:list T.nil T = cons T x y → False.
 #T; #x; #y; #H;
 nchange with (match cons T x y with [ nil ⇒ True | cons a b ⇒ False ]);
 nrewrite < H;
 nnormalize;
 napply I.
nqed.

nlemma append_nil : ∀T:Type.∀l:list T.(l@[]) = l.
 #T; #l;
 nelim l;
 nnormalize;
 ##[ ##1: napply refl_eq
 ##| ##2: #x; #y; #H;
          nrewrite > H;
          napply refl_eq
 ##]
nqed.

nlemma associative_list : ∀T.associative (list T) (append T).
 #T; #x; #y; #z;
 nelim x;
 nnormalize;
 ##[ ##1: napply refl_eq
 ##| ##2: #a; #b; #H;
          nrewrite > H;
          napply refl_eq
 ##]
nqed.

nlemma cons_append_commute : ∀T:Type.∀l1,l2:list T.∀a:T.a :: (l1 @ l2) = (a :: l1) @ l2.
 #T; #l1; #l2; #a;
 nnormalize;
 napply refl_eq.
nqed.

nlemma append_cons_commute : ∀T:Type.∀a:T.∀l,l1:list T.l @ (a::l1) = (l@[a]) @ l1.
 #T; #a; #l; #l1;
 nrewrite > (associative_list T l [a] l1);
 nnormalize;
 napply refl_eq.
nqed.

(* ************** *)
(* NON-EMPTY LIST *)
(* ************** *)

nlemma nelist_destruct_nil_nil : ∀T.∀x1,x2:T.ne_nil T x1 = ne_nil T x2 → x1 = x2.
 #T; #x1; #x2; #H;
 nchange with (match ne_nil T x2 with [ ne_cons _ _ ⇒ False | ne_nil a ⇒ x1 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma nelist_destruct_cons_cons_1 : ∀T.∀x1,x2:T.∀y1,y2:ne_list T.ne_cons T x1 y1 = ne_cons T x2 y2 → x1 = x2.
 #T; #x1; #x2; #y1; #y2; #H;
 nchange with (match ne_cons T x2 y2 with [ ne_nil _ ⇒ False | ne_cons a _ ⇒ x1 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma nelist_destruct_cons_cons_2 : ∀T.∀x1,x2:T.∀y1,y2:ne_list T.ne_cons T x1 y1 = ne_cons T x2 y2 → y1 = y2.
 #T; #x1; #x2; #y1; #y2; #H;
 nchange with (match ne_cons T x2 y2 with [ ne_nil _ ⇒ False | ne_cons _ b ⇒ y1 = b ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

(* !!! da togliere *)
nlemma nelist_destruct_cons_nil : ∀T.∀x1,x2:T.∀y1:ne_list T.ne_cons T x1 y1 = ne_nil T x2 → False.
 #T; #x1; #x2; #y1; #H;
 nchange with (match ne_cons T x1 y1 with [ ne_nil _ ⇒ True | ne_cons a b ⇒ False ]);
 nrewrite > H;
 nnormalize;
 napply I.
nqed.

(* !!! da togliere *)
nlemma nelist_destruct_nil_cons : ∀T.∀x1,x2:T.∀y2:ne_list T.ne_nil T x1 = ne_cons T x2 y2 → False.
 #T; #x1; #x2; #y2; #H;
 nchange with (match ne_cons T x2 y2 with [ ne_nil _ ⇒ True | ne_cons a b ⇒ False ]);
 nrewrite < H;
 nnormalize;
 napply I.
nqed.

nlemma associative_nelist : ∀T.associative (ne_list T) (ne_append T).
 #T; #x; #y; #z;
 nelim x;
 nnormalize;
 ##[ ##1: #hh; napply refl_eq
 ##| ##2: #hh; #tt; #H;
          nrewrite > H;
          napply refl_eq
 ##]
nqed.

nlemma necons_append_commute : ∀T:Type.∀l1,l2:ne_list T.∀a:T.(a §§ (l1 & l2)) = ((a §§ l1) & l2).
 #T; #l1; #l2; #a;
 nnormalize;
 napply refl_eq.
nqed.

nlemma append_necons_commute : ∀T:Type.∀a:T.∀l,l1:ne_list T.(l & (a §§ l1)) = (l & «£a») & l1.
 #T; #a; #l; #l1;
 nrewrite > (associative_nelist T l «£a» l1);
 nnormalize;
 napply refl_eq.
nqed.

(**************************************************************************)
(*       ___	                                                          *)
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

include "common/comp.ma".
include "common/option.ma".
include "common/nat.ma".

(* *************** *)
(* LISTE GENERICHE *)
(* *************** *)

ninductive list (A:Type) : Type ≝
  nil: list A
| cons: A → list A → list A.

nlet rec append A (l1: list A) l2 on l1 ≝
 match l1 with
  [ nil ⇒ l2
  | (cons hd tl) ⇒ cons A hd (append A tl l2) ].

notation "hvbox(hd break :: tl)"
  right associative with precedence 47
  for @{'cons $hd $tl}.

notation "[ list0 x sep ; ]"
  non associative with precedence 90
  for ${fold right @'nil rec acc @{'cons $x $acc}}.

notation "hvbox(l1 break @ l2)"
  right associative with precedence 47
  for @{'append $l1 $l2 }.

interpretation "nil" 'nil = (nil ?).
interpretation "cons" 'cons hd tl = (cons ? hd tl).
interpretation "append" 'append l1 l2 = (append ? l1 l2).

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

nlemma list_destruct_cons_nil : ∀T.∀x:T.∀y:list T.cons T x y = nil T → False.
 #T; #x; #y; #H;
 nchange with (match cons T x y with [ nil ⇒ True | cons a b ⇒ False ]);
 nrewrite > H;
 nnormalize;
 napply I.
nqed.

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

(* listlen *)
nlet rec len_list (T:Type) (l:list T) on l ≝
 match l with [ nil ⇒ O | cons _ t ⇒ S (len_list T t) ].

(* vuota? *)
ndefinition is_empty_list ≝
λT:Type.λl:list T.match l with [ nil ⇒ True | cons _ _ ⇒ False ].

ndefinition isb_empty_list ≝
λT:Type.λl:list T.match l with [ nil ⇒ true | cons _ _ ⇒ false ].

ndefinition isnot_empty_list ≝
λT:Type.λl:list T.match l with [ nil ⇒ False | cons _ _ ⇒ True ].

ndefinition isnotb_empty_list ≝
λT:Type.λl:list T.match l with [ nil ⇒ false | cons _ _ ⇒ true ].

(* reverse *)
nlet rec reverse_list (T:Type) (l:list T) on l ≝
 match l with
  [ nil ⇒ nil T
  | cons h t ⇒ (reverse_list T t)@[h]
  ].

(* getFirst *)
ndefinition get_first_list ≝
λT:Type.λl:list T.match l with
 [ nil ⇒ None ?
 | cons h _ ⇒ Some ? h ].

(* getLast *)
ndefinition get_last_list ≝
λT:Type.λl:list T.match reverse_list T l with
 [ nil ⇒ None ?
 | cons h _ ⇒ Some ? h ].

(* cutFirst *)
ndefinition cut_first_list ≝
λT:Type.λl:list T.match l with
 [ nil ⇒ nil T
 | cons _ t ⇒ t ].

(* cutLast *)
ndefinition cut_last_list ≝
λT:Type.λl:list T.match reverse_list T l with
 [ nil ⇒ nil T
 | cons _ t ⇒ reverse_list T t ].

(* apply f *)
nlet rec apply_f_list (T1,T2:Type) (l:list T1) (f:T1 → T2) on l ≝
match l with
 [ nil ⇒ nil T2
 | cons h t ⇒ cons T2 (f h) (apply_f_list T1 T2 t f) ].

(* fold right *)
nlet rec fold_right_list (T1,T2:Type) (f:T1 → T2 → T2) (acc:T2) (l:list T1) on l ≝
  match l with
   [ nil ⇒ acc
   | cons h t ⇒ f h (fold_right_list T1 T2 f acc t)
   ].

(* double fold right *)
nlemma fold_right_list2_aux1 :
∀T.∀h,t.len_list T [] = len_list T (h::t) → False.
 #T; #h; #t;
 nnormalize;
 #H;
 ndestruct (*napply (nat_destruct_0_S ? H)*).
nqed.

nlemma fold_right_list2_aux2 :
∀T.∀h,t.len_list T (h::t) = len_list T [] → False.
 #T; #h; #t;
 nnormalize;
 #H;
 ndestruct (*napply (nat_destruct_S_0 ? H)*).
nqed.

nlemma fold_right_list2_aux3 :
∀T.∀h,h',t,t'.len_list T (h::t) = len_list T (h'::t') → len_list T t = len_list T t'.
 #T; #h; #h'; #t; #t';
 nelim t;
 nelim t';
 ##[ ##1: nnormalize; #H; napply refl_eq
 ##| ##2: #a; #l'; #H; #H1;
          nchange in H1:(%) with ((S O) = (S (S (len_list T l'))));
          ndestruct (*nelim (nat_destruct_0_S ? (nat_destruct_S_S … H1))*)
 ##| ##3: #a; #l'; #H; #H1;
          nchange in H1:(%) with ((S (S (len_list T l'))) = (S O));
          ndestruct (*nelim (nat_destruct_S_0 ? (nat_destruct_S_S … H1))*)
 ##| ##4: #a; #l; #H; #a1; #l1; #H1; #H2;
          nchange in H2:(%) with ((S (S (len_list T l1))) = (S (S (len_list T l))));
          nchange with ((S (len_list T l1)) = (S (len_list T l)));
          nrewrite > (nat_destruct_S_S … H2);
          napply refl_eq
 ##]
nqed.

nlet rec fold_right_list2 (T1,T2:Type) (f:T1 → T1 → T2 → T2) (acc:T2) (l1:list T1) on l1 ≝
 match l1
  return λl1.Πl2.len_list T1 l1 = len_list T1 l2 → T2
 with
  [ nil ⇒ λl2.match l2 return λl2.len_list T1 [] = len_list T1 l2 → T2 with
   [ nil ⇒ λp:len_list T1 [] = len_list T1 [].acc
   | cons h t ⇒ λp:len_list T1 [] = len_list T1 (h::t).
    False_rect_Type0 ? (fold_right_list2_aux1 T1 h t p)
   ]
  | cons h t ⇒ λl2.match l2 return λl2.len_list T1 (h::t) = len_list T1 l2 → T2 with
   [ nil ⇒ λp:len_list T1 (h::t) = len_list T1 [].
    False_rect_Type0 ? (fold_right_list2_aux2 T1 h t p)
   | cons h' t' ⇒ λp:len_list T1 (h::t) = len_list T1 (h'::t').
    f h h' (fold_right_list2 T1 T2 f acc t t' (fold_right_list2_aux3 T1 h h' t t' p))
   ]
  ].

nlet rec bfold_right_list2 (T1:Type) (f:T1 → T1 → bool) (l1,l2:list T1) on l1 ≝
 match l1 with
  [ nil ⇒ match l2 with
   [ nil ⇒ true | cons h t ⇒ false ]
  | cons h t ⇒ match l2 with
   [ nil ⇒ false | cons h' t' ⇒ (f h h') ⊗ (bfold_right_list2 T1 f t t')
   ]
  ].

(* nth elem *)
nlet rec nth_list (T:Type) (l:list T) (n:nat) on l ≝
 match l with
  [ nil ⇒ None ?
  | cons h t ⇒ match n with
   [ O ⇒ Some ? h | S n' ⇒ nth_list T t n' ]
  ].

(* abs elem *)
ndefinition abs_list_aux1 : ∀T:Type.∀n.((len_list T []) > n) = true → False.
 #T; nnormalize; #n; #H; ndestruct (*napply (bool_destruct … H)*). nqed.

ndefinition abs_list_aux2 : ∀T:Type.∀h:T.∀t:list T.∀n.((len_list T (h::t)) > (S n) = true) → ((len_list T t) > n) = true.
 #T; #h; #t; #n; nnormalize; #H; napply H. nqed.

nlet rec abs_list (T:Type) (l:list T) on l ≝
 match l
  return λl.Πn.(((len_list T l) > n) = true) → T
 with
  [ nil ⇒ λn.λp:(((len_list T []) > n) = true).False_rect_Type0 ? (abs_list_aux1 T n p)
  | cons h t ⇒ λn.
   match n with
    [ O ⇒ λp:(((len_list T (h::t)) > O) = true).h
    | S n' ⇒ λp:(((len_list T (h::t)) > (S n')) = true).
     abs_list T t n' (abs_list_aux2 T h t n' p)
    ]
  ].

(* esempio: abs_list ? [ 1; 2; 3 ; 4 ] 0 (refl_eq …) = 1. *)

nlemma symmetric_lenlist : ∀T.∀l1,l2:list T.len_list T l1 = len_list T l2 → len_list T l2 = len_list T l1.
 #T; #l1;
 nelim l1;
 ##[ ##1: #l2; ncases l2; nnormalize;
          ##[ ##1: #H; napply refl_eq
          ##| ##2: #h; #t; #H; ndestruct (*nelim (nat_destruct_0_S ? H)*)
          ##]
 ##| ##2: #h; #l2; ncases l2; nnormalize;
          ##[ ##1: #H; #l; #H1; nrewrite < H1; napply refl_eq
          ##| ##2: #h; #l; #H; #l3; #H1; nrewrite < H1; napply refl_eq
          ##]
 ##]
nqed.

nlemma symmetric_foldrightlist2_aux :
∀T1,T2:Type.∀f:T1 → T1 → T2 → T2.
 (∀x,y,z.f x y z = f y x z) →
 (∀acc:T2.∀l1,l2:list T1.
  ∀H1:(len_list T1 l1 = len_list T1 l2).
  ∀H2:(len_list T1 l2 = len_list T1 l1).
   (fold_right_list2 T1 T2 f acc l1 l2 H1 = fold_right_list2 T1 T2 f acc l2 l1 H2)).
 #T1; #T2; #f; #H; #acc; #l1;
 nelim l1;
 ##[ ##1: #l2; ncases l2;
          ##[ ##1: nnormalize; #H1; #H2; napply refl_eq
          ##| ##2: #h; #l; #H1; #H2;
                   nchange in H1:(%) with (O = (S (len_list ? l)));
                   ndestruct (*nelim (nat_destruct_0_S ? H1)*)
          ##]
 ##| ##2: #h3; #l3; #H1; #l2; ncases l2;
          ##[ ##1: #H2; #H3; nchange in H2:(%) with ((S (len_list ? l3)) = O);
                   ndestruct (*nelim (nat_destruct_S_0 ? H1)*)
          ##| ##2: #h4; #l4; #H2; #H3;
                   nchange in H2:(%) with ((S (len_list ? l3)) = (S (len_list ? l4)));
                   nchange in H3:(%) with ((S (len_list ? l4)) = (S (len_list ? l3)));
                   nchange with ((f h3 h4 (fold_right_list2 T1 T2 f acc l3 l4 (fold_right_list2_aux3 T1 h3 h4 l3 l4 ?))) =
                                 (f h4 h3 (fold_right_list2 T1 T2 f acc l4 l3 (fold_right_list2_aux3 T1 h4 h3 l4 l3 ?))));
                   nrewrite < (H1 l4 (fold_right_list2_aux3 T1 h3 h4 l3 l4 H2) (fold_right_list2_aux3 T1 h4 h3 l4 l3 H3));
                   nrewrite > (H h3 h4 (fold_right_list2 T1 T2 f acc l3 l4 ?));
                   napply refl_eq
          ##]
 ##]
nqed.

nlemma symmetric_foldrightlist2 :
∀T1,T2:Type.∀f:T1 → T1 → T2 → T2.
 (∀x,y,z.f x y z = f y x z) →
 (∀acc:T2.∀l1,l2:list T1.∀H:len_list T1 l1 = len_list T1 l2.
   fold_right_list2 T1 T2 f acc l1 l2 H = fold_right_list2 T1 T2 f acc l2 l1 (symmetric_lenlist T1 l1 l2 H)).
 #T1; #T2; #f; #H; #acc; #l1; #l2; #H1;
 nrewrite > (symmetric_foldrightlist2_aux T1 T2 f H acc l1 l2 H1 (symmetric_lenlist T1 l1 l2 H1));
 napply refl_eq.
nqed.

nlemma symmetric_bfoldrightlist2 :
∀T1:Type.∀f:T1 → T1 → bool.
 (∀x,y.f x y = f y x) →
 (∀l1,l2:list T1.
  bfold_right_list2 T1 f l1 l2 = bfold_right_list2 T1 f l2 l1).
 #T; #f; #H; #l1;
 nelim l1;
 ##[ ##1: #l2; ncases l2;
          ##[ ##1: nnormalize; napply refl_eq
          ##| ##2: #hh2; #ll2; nnormalize; napply refl_eq
          ##]
 ##| ##2: #hh1; #ll1; #H1; #l2; ncases l2;
          ##[ ##1: nnormalize; napply refl_eq
          ##| ##2: #hh2; #ll2; nnormalize;
                   nrewrite > (H1 ll2);
                   nrewrite > (H hh1 hh2);
                   napply refl_eq
          ##]
 ##]
nqed.

nlemma bfoldrightlist2_to_eq :
∀T1:Type.∀f:T1 → T1 → bool.
 (∀x,y.(f x y = true → x = y)) →
 (∀l1,l2:list T1.
  (bfold_right_list2 T1 f l1 l2 = true → l1 = l2)).
 #T; #f; #H; #l1;
 nelim l1;
 ##[ ##1: #l2; ncases l2;
          ##[ ##1: #H1; napply refl_eq
          ##| ##2: #hh2; #ll2; nnormalize; #H1;
                   ndestruct (*napply (bool_destruct … H1)*)
          ##]
 ##| ##2: #hh1; #ll1; #H1; #l2; ncases l2;
          ##[ ##1: nnormalize; #H2;
                   ndestruct (*napply (bool_destruct … H2)*)
          ##| ##2: #hh2; #ll2; #H2;
                   nchange in H2:(%) with (((f hh1 hh2)⊗(bfold_right_list2 T f ll1 ll2)) = true);
                   nrewrite > (H hh1 hh2 (andb_true_true_l … H2));
                   nrewrite > (H1 ll2 (andb_true_true_r … H2));
                   napply refl_eq
          ##]
 ##]
nqed.

nlemma eq_to_bfoldrightlist2 :
∀T1:Type.∀f:T1 → T1 → bool.
 (∀x,y.(x = y → f x y = true)) →
 (∀l1,l2:list T1.
  (l1 = l2 → bfold_right_list2 T1 f l1 l2 = true)).
 #T; #f; #H; #l1;
 nelim l1;
 ##[ ##1: #l2; ncases l2;
          ##[ ##1: #H1; nnormalize; napply refl_eq
          ##| ##2: #hh2; #ll2; #H1;
                   (* !!! ndestruct: assert false *)
                   nelim (list_destruct_nil_cons ??? H1)
          ##]
 ##| ##2: #hh1; #ll1; #H1; #l2; ncases l2;
          ##[ ##1: #H2;
                   (* !!! ndestruct: assert false *)
                   nelim (list_destruct_cons_nil ??? H2)
          ##| ##2: #hh2; #ll2; #H2; nnormalize;
                   nrewrite > (list_destruct_1 … H2);
                   nrewrite > (H hh2 hh2 (refl_eq …));
                   nnormalize;
                   nrewrite > (H1 ll2 (list_destruct_2 … H2));
                   napply refl_eq
          ##]
 ##]
nqed.

nlemma bfoldrightlist2_to_lenlist :
∀T.∀f:T → T → bool.
 (∀l1,l2:list T.bfold_right_list2 T f l1 l2 = true → len_list T l1 = len_list T l2).
 #T; #f; #l1;
 nelim l1;
 ##[ ##1: #l2; ncases l2;
          ##[ ##1: nnormalize; #H; napply refl_eq
          ##| ##2: nnormalize; #hh; #tt; #H;
                   ndestruct (*napply (bool_destruct … H)*)
          ##]
 ##| ##2: #hh; #tt; #H; #l2; ncases l2;
          ##[ ##1: nnormalize; #H1;
                   ndestruct (*napply (bool_destruct … H1)*)
          ##| ##2: #hh1; #tt1; #H1; nnormalize;
                   nrewrite > (H tt1 ?);
                   ##[ ##1: napply refl_eq
                   ##| ##2: nchange in H1:(%) with ((? ⊗ (bfold_right_list2 T f tt tt1)) = true);
                            napply (andb_true_true_r … H1)
                   ##]
          ##]
 ##]
nqed.

nlemma decidable_list :
∀T.(∀x,y:T.decidable (x = y)) →
   (∀x,y:list T.decidable (x = y)).
 #T; #H; #x; nelim x;
 ##[ ##1: #y; ncases y;
          ##[ ##1: nnormalize; napply (or2_intro1 (? = ?) (? ≠ ?) (refl_eq …))
          ##| ##2: #hh2; #tt2; nnormalize; napply (or2_intro2 (? = ?) (? ≠ ?) ?);
                   nnormalize; #H1;
                   (* !!! ndestruct: assert false *)
                   napply (list_destruct_nil_cons T … H1)
          ##]
 ##| ##2: #hh1; #tt1; #H1; #y; ncases y;
          ##[ ##1: nnormalize; napply (or2_intro2 (? = ?) (? ≠ ?) ?);
                   nnormalize; #H2;
                   (* !!! ndestruct: assert false *)
                   napply (list_destruct_cons_nil T … H2)
          ##| ##2: #hh2; #tt2; nnormalize; napply (or2_elim (hh1 = hh2) (hh1 ≠ hh2) ? (H …));
                   ##[ ##2: #H2; napply (or2_intro2 (? = ?) (? ≠ ?) ?);
                            nnormalize; #H3; napply (H2 (list_destruct_1 T … H3))
                   ##| ##1: #H2; napply (or2_elim (tt1 = tt2) (tt1 ≠ tt2) ? (H1 tt2));
                            ##[ ##2: #H3; napply (or2_intro2 (? = ?) (? ≠ ?) ?);
                                     nnormalize; #H4; napply (H3 (list_destruct_2 T … H4))
                            ##| ##1: #H3; napply (or2_intro1 (? = ?) (? ≠ ?) ?);
                                     nrewrite > H2; nrewrite > H3; napply refl_eq
                            ##]
                   ##]
          ##]
 ##]
nqed.

nlemma nbfoldrightlist2_to_neq :
∀T1:Type.∀f:T1 → T1 → bool.
 (∀x,y.(f x y = false → x ≠ y)) →
 (∀l1,l2:list T1.
  (bfold_right_list2 T1 f l1 l2 = false → l1 ≠ l2)).
 #T; #f; #H; #l1;
 nelim l1;
 ##[ ##1: #l2; ncases l2;
          ##[ ##1: nnormalize; #H1;
                   ndestruct (*napply (bool_destruct … H1)*)
          ##| ##2: #hh2; #ll2; #H1; nnormalize; #H2;
                   (* !!! ndestruct: assert false *)
                   napply (list_destruct_nil_cons T … H2)
          ##]
 ##| ##2: #hh1; #ll1; #H1; #l2; ncases l2;
          ##[ ##1: #H2; nnormalize; #H3;
                   (* !!! ndestruct: assert false *)
                   napply (list_destruct_cons_nil T … H3)
          ##| ##2: #hh2; #ll2; #H2; nnormalize; #H3;
                   nchange in H2:(%) with (((f hh1 hh2)⊗(bfold_right_list2 T f ll1 ll2)) = false);
                   napply (H1 ll2 ? (list_destruct_2 T … H3));
                   napply (or2_elim ??? (andb_false2 … H2) );
                   ##[ ##1: #H4; napply (absurd (hh1 = hh2) …);
                            ##[ ##1: nrewrite > (list_destruct_1 T … H3); napply refl_eq
                            ##| ##2: napply (H … H4)
                            ##]
                   ##| ##2: #H4; napply H4
                   ##]
          ##]
 ##]
nqed.

nlemma list_destruct :
∀T.(∀x,y:T.decidable (x = y)) →
   (∀h1,h2:T.∀l1,l2:list T.
    (h1::l1) ≠ (h2::l2) → h1 ≠ h2 ∨ l1 ≠ l2).
 #T; #H; #h1; #h2; #l1; nelim l1;
 ##[ ##1: #l2; ncases l2;
          ##[ ##1: #H1; napply (or2_intro1 (h1 ≠ h2) ([] ≠ []) …);
                   nnormalize; #H2; nrewrite > H2 in H1:(%);
                   nnormalize; #H1; napply (H1 (refl_eq …))
          ##| ##2: #hh2; #ll2; #H1; napply (or2_intro2 (h1 ≠ h2) ([] ≠ (hh2::ll2)) …);
                   nnormalize; #H2;
                   (* !!! ndestruct: assert false *)
                   napply (list_destruct_nil_cons T … H2)
          ##]
 ##| ##2: #hh1; #ll1; #H1; #l2; ncases l2;
          ##[ ##1: #H2; napply (or2_intro2 (h1 ≠ h2) ((hh1::ll1) ≠ []) …);
                   nnormalize; #H3;
                   (* !!! ndestruct: assert false *)
                   napply (list_destruct_cons_nil T … H3)
          ##| ##2: #hh2; #ll2; #H2;     
                   napply (or2_elim (h1 = h2) (h1 ≠ h2) ? (H h1 h2) …);
                   ##[ ##2: #H3; napply (or2_intro1 (h1 ≠ h2) ((hh1::ll1) ≠ (hh2::ll2)) H3)
                   ##| ##1: #H3; napply (or2_intro2 (h1 ≠ h2) ((hh1::ll1) ≠ (hh2::ll2) …));
                            nrewrite > H3 in H2:(%); #H2;
                            nnormalize; #H4; nrewrite > (list_destruct_1 T … H4) in H2:(%); #H2;
                            nrewrite > (list_destruct_2 T … H4) in H2:(%); #H2;
                            napply (H2 (refl_eq …))
                   ##]
          ##]
 ##]
nqed.

nlemma neq_to_nbfoldrightlist2 :
∀T:Type.∀f:T → T → bool.
 (∀x,y:T.decidable (x = y)) →
 (∀x,y.(x ≠ y → f x y = false)) →
 (∀l1,l2:list T.
  (l1 ≠ l2 → bfold_right_list2 T f l1 l2 = false)).
 #T; #f; #H; #H1; #l1;
 nelim l1;
 ##[ ##1: #l2; ncases l2;
          ##[ ##1: nnormalize; #H2; nelim (H2 (refl_eq …))
          ##| ##2: #hh2; #ll2; nnormalize; #H2; napply refl_eq
          ##]
 ##| ##2: #hh1; #ll1; #H2; #l2; ncases l2;
          ##[ ##1: nnormalize; #H3; napply refl_eq
          ##| ##2: #hh2; #ll2; #H3;
                   nchange with (((f hh1 hh2)⊗(bfold_right_list2 T f ll1 ll2)) = false);
                   napply (or2_elim (hh1 ≠ hh2) (ll1 ≠ ll2) ? (list_destruct T H … H3) …);
                   ##[ ##1: #H4; nrewrite > (H1 hh1 hh2 H4); nnormalize; napply refl_eq
                   ##| ##2: #H4; nrewrite > (H2 ll2 H4);
                            nrewrite > (symmetric_andbool (f hh1 hh2) false);
                            nnormalize; napply refl_eq
                   ##]
          ##]
 ##]
nqed.

nlemma isbemptylist_to_isemptylist : ∀T,l.isb_empty_list T l = true → is_empty_list T l.
 #T; #l;
 ncases l;
 nnormalize;
 ##[ ##1: #H; napply I
 ##| ##2: #x; #l; #H; ndestruct (*napply (bool_destruct … H)*)
 ##]
nqed.

nlemma isnotbemptylist_to_isnotemptylist : ∀T,l.isnotb_empty_list T l = true → isnot_empty_list T l.
 #T; #l;
 ncases l;
 nnormalize;
 ##[ ##1: #H; ndestruct (*napply (bool_destruct … H)*)
 ##| ##2: #x; #l; #H; napply I
 ##]
nqed.

nlemma list_is_comparable : comparable → comparable.
 #T; napply (mk_comparable (list T));
 ##[ napply (nil ?)
 ##| napply (λx.false)
 ##| napply (bfold_right_list2 T (eqc T))
 ##| napply (bfoldrightlist2_to_eq … (eqc T));
     napply (eqc_to_eq T)
 ##| napply (eq_to_bfoldrightlist2 … (eqc T));
     napply (eq_to_eqc T)
 ##| napply (nbfoldrightlist2_to_neq … (eqc T));
     napply (neqc_to_neq T)
 ##| napply (neq_to_nbfoldrightlist2 … (eqc T));
     ##[ napply (decidable_c T)
     ##| napply (neq_to_neqc T)
     ##]
 ##| napply decidable_list;
     napply (decidable_c T)
 ##| napply symmetric_bfoldrightlist2;
     napply (symmetric_eqc T)
 ##]
nqed.

unification hint 0 ≔ S: comparable;
         T ≟ (carr S),
         X ≟ (list_is_comparable S)
 (*********************************************) ⊢
         carr X ≡ list T.

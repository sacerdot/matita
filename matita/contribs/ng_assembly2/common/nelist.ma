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

(* ************** *)
(* NON-EMPTY LIST *)
(* ************** *)

(* lista non vuota *)
ninductive ne_list (A:Type) : Type ≝
  | ne_nil: A → ne_list A
  | ne_cons: A → ne_list A → ne_list A.

(* append *)
nlet rec ne_append (A:Type) (l1,l2:ne_list A) on l1 ≝
 match l1 with
  [ ne_nil hd ⇒ ne_cons A hd l2
  | ne_cons hd tl ⇒ ne_cons A hd (ne_append A tl l2) ].

notation "hvbox(hd break §§ tl)"
  right associative with precedence 46
  for @{'ne_cons $hd $tl}.

(* \laquo \raquo *)
notation "« list0 x sep ; break £ y break »"
  non associative with precedence 90
  for ${fold right @{'ne_nil $y } rec acc @{'ne_cons $x $acc}}.

notation "hvbox(l1 break & l2)"
  right associative with precedence 47
  for @{'ne_append $l1 $l2 }.

interpretation "ne_nil" 'ne_nil hd = (ne_nil ? hd).
interpretation "ne_cons" 'ne_cons hd tl = (ne_cons ? hd tl).
interpretation "ne_append" 'ne_append l1 l2 = (ne_append ? l1 l2).

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

nlemma nelist_destruct_cons_nil : ∀T.∀x1,x2:T.∀y1:ne_list T.ne_cons T x1 y1 = ne_nil T x2 → False.
 #T; #x1; #x2; #y1; #H;
 nchange with (match ne_cons T x1 y1 with [ ne_nil _ ⇒ True | ne_cons a b ⇒ False ]);
 nrewrite > H;
 nnormalize;
 napply I.
nqed.

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

(* listlen *)
nlet rec len_neList (T:Type) (nl:ne_list T) on nl ≝
 match nl with [ ne_nil _ ⇒ (S O) | ne_cons _ t ⇒ S (len_neList T t) ].

(* reverse *)
nlet rec reverse_neList (T:Type) (nl:ne_list T) on nl ≝
 match nl with
  [ ne_nil h ⇒ ne_nil T h
  | ne_cons h t ⇒ (reverse_neList T t)&(ne_nil T h)
  ].

(* getFirst *)
ndefinition get_first_neList ≝
λT:Type.λnl:ne_list T.match nl with
 [ ne_nil h ⇒ h
 | ne_cons h _ ⇒ h ].

(* getLast *)
ndefinition get_last_neList ≝
λT:Type.λnl:ne_list T.match reverse_neList T nl with
 [ ne_nil h ⇒ h
 | ne_cons h _ ⇒ h ].

(* cutFirst *)
ndefinition cut_first_neList ≝
λT:Type.λnl:ne_list T.match nl with
 [ ne_nil h ⇒ ne_nil T h
 | ne_cons _ t ⇒ t ].

(* cutLast *)
ndefinition cut_last_neList ≝
λT:Type.λnl:ne_list T.match reverse_neList T nl with
 [ ne_nil h ⇒ ne_nil T h
 | ne_cons _ t ⇒ reverse_neList T t ].

(* apply f *)
nlet rec apply_f_neList (T1,T2:Type) (nl:ne_list T1) (f:T1 → T2) on nl ≝
match nl with
 [ ne_nil h ⇒ ne_nil T2 (f h)
 | ne_cons h t ⇒ ne_cons T2 (f h) (apply_f_neList T1 T2 t f) ].

(* fold right *)
nlet rec fold_right_neList (T1,T2:Type) (f:T1 → T2 → T2) (acc:T2) (nl:ne_list T1) on nl ≝
  match nl with
   [ ne_nil h ⇒ f h acc
   | ne_cons h t ⇒ f h (fold_right_neList T1 T2 f acc t)
   ].

(* double fold right *)
nlemma fold_right_neList2_aux1 :
∀T.∀h,h',t'.len_neList T «£h» = len_neList T (h'§§t') → False.
 #T; #h; #h'; #t';
 nnormalize;
 ncases t';
 nnormalize;
 ##[ ##1: #x; #H; ndestruct (*nelim (nat_destruct_0_S ? (nat_destruct_S_S … H))*)
 ##| ##2: #x; #l; #H; ndestruct (*nelim (nat_destruct_0_S ? (nat_destruct_S_S … H))*)
 ##]
nqed.

nlemma fold_right_neList2_aux2 :
∀T.∀h,h',t.len_neList T (h§§t) = len_neList T «£h'» → False.
 #T; #h; #h'; #t;
 nnormalize;
 ncases t;
 nnormalize;
 ##[ ##1: #x; #H; ndestruct (*nelim (nat_destruct_S_0 ? (nat_destruct_S_S … H))*)
 ##| ##2: #x; #l; #H; ndestruct (*nelim (nat_destruct_S_0 ? (nat_destruct_S_S … H))*)
 ##]
nqed.

nlemma fold_right_neList2_aux3 :
∀T.∀h,h',t,t'.len_neList T (h§§t) = len_neList T (h'§§t') → len_neList T t = len_neList T t'.
 #T; #h; #h'; #t; #t';
 nelim t;
 nelim t';
 ##[ ##1: nnormalize; #x; #y; #H; napply refl_eq
 ##| ##2: #a; #l'; #H; #x; #H1;
          nchange in H1:(%) with ((S (len_neList T «£x»)) = (S (len_neList T (a§§l'))));
          nrewrite > (nat_destruct_S_S … H1);
          napply refl_eq
 ##| ##3: #x; #a; #l'; #H; #H1;
          nchange in H1:(%) with ((S (len_neList T (a§§l')))= (S (len_neList T «£x»)));
          nrewrite > (nat_destruct_S_S … H1);
          napply refl_eq
 ##| ##4: #a; #l; #H; #a1; #l1; #H1; #H2;
          nchange in H2:(%) with ((S (len_neList T (a1§§l1))) = (S (len_neList T (a§§l))));
          nrewrite > (nat_destruct_S_S … H2);
          napply refl_eq
 ##]
nqed.

nlet rec fold_right_neList2 (T1,T2:Type) (f:T1 → T1 → T2 → T2) (acc:T2) (l1:ne_list T1) on l1 ≝
 match l1
  return λl1.Πl2.len_neList T1 l1 = len_neList T1 l2 → T2
 with
  [ ne_nil h ⇒ λl2.match l2 return λl2.len_neList T1 «£h» = len_neList T1 l2 → T2 with
   [ ne_nil h' ⇒ λp:len_neList T1 «£h» = len_neList T1 «£h'».
    f h h' acc
   | ne_cons h' t' ⇒ λp:len_neList T1 «£h» = len_neList T1 (h'§§t').
    False_rect_Type0 ? (fold_right_neList2_aux1 T1 h h' t' p)
   ]
  | ne_cons h t ⇒ λl2.match l2 return λl2.len_neList T1 (h§§t) = len_neList T1 l2 → T2 with
   [ ne_nil h' ⇒ λp:len_neList T1 (h§§t) = len_neList T1 «£h'».
    False_rect_Type0 ? (fold_right_neList2_aux2 T1 h h' t p)
   | ne_cons h' t' ⇒ λp:len_neList T1 (h§§t) = len_neList T1 (h'§§t').
    f h h' (fold_right_neList2 T1 T2 f acc t t' (fold_right_neList2_aux3 T1 h h' t t' p))
   ]
  ].

nlet rec bfold_right_neList2 (T1:Type) (f:T1 → T1 → bool) (l1,l2:ne_list T1) on l1 ≝
 match l1 with
  [ ne_nil h ⇒ match l2 with
   [ ne_nil h' ⇒ f h h' | ne_cons h' t' ⇒ false ]
  | ne_cons h t ⇒ match l2 with
   [ ne_nil h' ⇒ false | ne_cons h' t' ⇒ (f h h') ⊗ (bfold_right_neList2 T1 f t t')
   ]
  ].

(* nth elem *)
nlet rec nth_neList (T:Type) (nl:ne_list T) (n:nat) on nl ≝
 match nl with
  [ ne_nil h ⇒ match n with
   [ O ⇒ Some ? h | S _ ⇒ None ? ]
  | ne_cons h t ⇒ match n with
   [ O ⇒ Some ? h | S n' ⇒ nth_neList T t n' ]
  ].

(* abs elem *)
ndefinition abs_neList_aux1 : ∀T:Type.∀h:T.∀n.((len_neList T («£h»)) > (S n)) = true → False.
 #T; #h; #n; nnormalize; #H; ndestruct (*napply (bool_destruct … H)*). nqed.

ndefinition abs_neList_aux2 : ∀T:Type.∀h:T.∀t:ne_list T.∀n.((len_neList T (h§§t)) > (S n) = true) → ((len_neList T t) > n) = true.
 #T; #h; #t; #n; nnormalize; #H; napply H. nqed.

nlet rec abs_neList (T:Type) (l:ne_list T) on l ≝
 match l
  return λl.Πn.(((len_neList T l) > n) = true) → T
 with
  [ ne_nil h ⇒ λn.
   match n
    return λn.(((len_neList T (ne_nil T h)) > n) = true) → T
   with
    [ O ⇒ λp:(((len_neList T (ne_nil T h)) > O) = true).h
    | S n' ⇒ λp:(((len_neList T (ne_nil T h)) > (S n')) = true).
     False_rect_Type0 ? (abs_neList_aux1 T h n' p)
    ]
  | ne_cons h t ⇒ λn.
   match n with
    [ O ⇒ λp:(((len_neList T (ne_cons T h t)) > O) = true).h
    | S n' ⇒ λp:(((len_neList T (ne_cons T h t)) > (S n')) = true).
     abs_neList T t n' (abs_neList_aux2 T h t n' p)
    ]
  ].

(* esempio: abs_neList ? « 1; 2; 3 £ 4 » 0 (refl_eq …) = 1. *)

(* conversione *)
nlet rec neList_to_list (T:Type) (nl:ne_list T) on nl : list T ≝
 match nl with [ ne_nil h ⇒ [h] | ne_cons h t ⇒ [h]@(neList_to_list T t) ].

nlemma symmetric_lennelist : ∀T.∀l1,l2:ne_list T.len_neList T l1 = len_neList T l2 → len_neList T l2 = len_neList T l1.
 #T; #l1;
 nelim l1;
 ##[ ##1: #h; #l2; ncases l2; nnormalize;
          ##[ ##1: #H; #H1; napply refl_eq
          ##| ##2: #h; #t; #H; nrewrite > H; napply refl_eq
          ##]
 ##| ##2: #h; #l2; ncases l2; nnormalize;
          ##[ ##1: #h1; #H; #l; #H1; nrewrite < H1; napply refl_eq
          ##| ##2: #h; #l; #H; #l3; #H1; nrewrite < H1; napply refl_eq
          ##]
 ##]
nqed.

nlemma symmetric_foldrightnelist2_aux :
∀T1,T2:Type.∀f:T1 → T1 → T2 → T2.
 (∀x,y,z.f x y z = f y x z) →
 (∀acc:T2.∀l1,l2:ne_list T1.
  ∀H1:len_neList T1 l1 = len_neList T1 l2.∀H2:len_neList T1 l2 = len_neList T1 l1.
   fold_right_neList2 T1 T2 f acc l1 l2 H1 = fold_right_neList2 T1 T2 f acc l2 l1 H2).
 #T1; #T2; #f; #H; #acc; #l1;
 nelim l1;
 ##[ ##1: #h; #l2; ncases l2;
          ##[ ##1: #h1; nnormalize; #H1; #H2; nrewrite > (H h h1 acc); napply refl_eq
          ##| ##2: #h1; #l; ncases l;
                   ##[ ##1: #h3; #H1; #H2;
                            nchange in H1:(%) with ((S O) = (S (S O)));
                            (* !!! ndestruct: si inceppa su un'ipotesi che non e' H1 *)
                            nelim (nat_destruct_0_S ? (nat_destruct_S_S … H1))
                   ##| ##2: #h3; #l3; #H1; #H2;
                            nchange in H1:(%) with ((S O) = (S (S (len_neList ? l3))));
                            (* !!! ndestruct: si inceppa su un'ipotesi che non e' H1 *)
                            nelim (nat_destruct_0_S ? (nat_destruct_S_S … H1))
                   ##]                   
          ##]
 ##| ##2: #h3; #l3; #H1; #l2; ncases l2;
          ##[ ##1: #h4; ncases l3;
                   ##[ ##1: #h5; #H2; #H3;
                            nchange in H2:(%) with ((S (S O)) = (S O));
                            (* !!! ndestruct: si inceppa su un'ipotesi che non e' H1 *)
                            nelim (nat_destruct_S_0 ? (nat_destruct_S_S … H2))
                   ##| ##2: #h5; #l5; #H2; #H3;
                            nchange in H2:(%) with ((S (S (len_neList ? l5))) = (S O));
                            (* !!! ndestruct: si inceppa su un'ipotesi che non e' H1 *)
                            nelim (nat_destruct_S_0 ? (nat_destruct_S_S … H2))
                   ##]
          ##| ##2: #h4; #l4; #H2; #H3;
                   nchange in H2:(%) with ((S (len_neList ? l3)) = (S (len_neList ? l4)));
                   nchange in H3:(%) with ((S (len_neList ? l4)) = (S (len_neList ? l3)));
                   nchange with ((f h3 h4 (fold_right_neList2 T1 T2 f acc l3 l4 (fold_right_neList2_aux3 T1 h3 h4 l3 l4 ?))) =
                                 (f h4 h3 (fold_right_neList2 T1 T2 f acc l4 l3 (fold_right_neList2_aux3 T1 h4 h3 l4 l3 ?))));
                   nrewrite < (H1 l4 (fold_right_neList2_aux3 T1 h3 h4 l3 l4 H2) (fold_right_neList2_aux3 T1 h4 h3 l4 l3 H3));
                   nrewrite > (H h3 h4 (fold_right_neList2 T1 T2 f acc l3 l4 ?));
                   napply refl_eq
          ##]
 ##]
nqed.

nlemma symmetric_foldrightnelist2 :
∀T1,T2:Type.∀f:T1 → T1 → T2 → T2.
 (∀x,y,z.f x y z = f y x z) →
 (∀acc:T2.∀l1,l2:ne_list T1.∀H:len_neList T1 l1 = len_neList T1 l2.
  fold_right_neList2 T1 T2 f acc l1 l2 H = fold_right_neList2 T1 T2 f acc l2 l1 (symmetric_lennelist T1 l1 l2 H)).
 #T1; #T2; #f; #H; #acc; #l1; #l2; #H1;
 nrewrite > (symmetric_foldrightnelist2_aux T1 T2 f H acc l1 l2 H1 (symmetric_lennelist T1 l1 l2 H1));
 napply refl_eq.
nqed.

nlemma symmetric_bfoldrightnelist2 :
∀T1:Type.∀f:T1 → T1 → bool.
 (∀x,y.f x y = f y x) →
 (∀l1,l2:ne_list T1.
  bfold_right_neList2 T1 f l1 l2 = bfold_right_neList2 T1 f l2 l1).
 #T; #f; #H; #l1;
 nelim l1;
 ##[ ##1: #hh1; #l2; ncases l2;
          ##[ ##1: #hh2; nnormalize; nrewrite > (H hh1 hh2); napply refl_eq
          ##| ##2: #hh2; #ll2; nnormalize; napply refl_eq
          ##]
 ##| ##2: #hh1; #ll1; #H1; #l2; ncases l2;
          ##[ ##1: #hh2; nnormalize; napply refl_eq
          ##| ##2: #hh2; #ll2; nnormalize;
                   nrewrite > (H1 ll2);
                   nrewrite > (H hh1 hh2);
                   napply refl_eq
          ##]
 ##]
nqed.

nlemma bfoldrightnelist2_to_eq :
∀T1:Type.∀f:T1 → T1 → bool.
 (∀x,y.(f x y = true → x = y)) →
 (∀l1,l2:ne_list T1.
  (bfold_right_neList2 T1 f l1 l2 = true → l1 = l2)).
 #T; #f; #H; #l1;
 nelim l1;
 ##[ ##1: #hh1; #l2; ncases l2;
          ##[ ##1: #hh2; #H1; nnormalize in H1:(%); nrewrite > (H hh1 hh2 H1); napply refl_eq
          ##| ##2: #hh2; #ll2; nnormalize; #H1; ndestruct (*napply (bool_destruct … H1)*)
          ##]
 ##| ##2: #hh1; #ll1; #H1; #l2; ncases l2;
          ##[ ##1: #hh2; nnormalize; #H2; ndestruct (*napply (bool_destruct … H2)*)
          ##| ##2: #hh2; #ll2; #H2;
                   nchange in H2:(%) with (((f hh1 hh2)⊗(bfold_right_neList2 T f ll1 ll2)) = true);
                   nrewrite > (H hh1 hh2 (andb_true_true_l … H2));
                   nrewrite > (H1 ll2 (andb_true_true_r … H2));
                   napply refl_eq
          ##]
 ##]
nqed.

nlemma eq_to_bfoldrightnelist2 :
∀T1:Type.∀f:T1 → T1 → bool.
 (∀x,y.(x = y → f x y = true)) →
 (∀l1,l2:ne_list T1.
  (l1 = l2 → bfold_right_neList2 T1 f l1 l2 = true)).
 #T; #f; #H; #l1;
 nelim l1;
 ##[ ##1: #hh1; #l2; ncases l2;
          ##[ ##1: #hh2; #H1; nnormalize;
                   nrewrite > (H hh1 hh2 (nelist_destruct_nil_nil … H1));
                   napply refl_eq
          ##| ##2: #hh2; #ll2; #H1;
                   (* !!! ndestruct: assert false *)
                   nelim (nelist_destruct_nil_cons ???? H1)
          ##]
 ##| ##2: #hh1; #ll1; #H1; #l2; ncases l2;
          ##[ ##1: #hh2; #H2;
                   (* !!! ndestruct: assert false *)
                   nelim (nelist_destruct_cons_nil ???? H2)
          ##| ##2: #hh2; #ll2; #H2; nnormalize;
                   nrewrite > (nelist_destruct_cons_cons_1 … H2);
                   nrewrite > (H hh2 hh2 (refl_eq …));
                   nnormalize;
                   nrewrite > (H1 ll2 (nelist_destruct_cons_cons_2 … H2));
                   napply refl_eq
          ##]
 ##]
nqed.

nlemma bfoldrightnelist2_to_lennelist :
∀T.∀f:T → T → bool.
 (∀l1,l2:ne_list T.bfold_right_neList2 T f l1 l2 = true → len_neList T l1 = len_neList T l2).
 #T; #f; #l1;
 nelim l1;
 ##[ ##1: #hh1; #l2; ncases l2;
          ##[ ##1: nnormalize; #hh2; #H; napply refl_eq
          ##| ##2: nnormalize; #hh2; #tt2; #H; ndestruct (*napply (bool_destruct … H)*)
          ##]
 ##| ##2: #hh1; #tt1; #H; #l2; ncases l2;
          ##[ ##1: nnormalize; #hh2; #H1; ndestruct (*napply (bool_destruct … H1)*)
          ##| ##2: #hh2; #tt2; #H1; nnormalize;
                   nrewrite > (H tt2 ?);
                   ##[ ##1: napply refl_eq
                   ##| ##2: nchange in H1:(%) with ((? ⊗ (bfold_right_neList2 T f tt1 tt2)) = true);
                            napply (andb_true_true_r … H1)
                   ##]
          ##]
 ##]
nqed.

nlemma decidable_nelist :
∀T.(∀x,y:T.decidable (x = y)) →
   (∀x,y:ne_list T.decidable (x = y)).
 #T; #H; #x; nelim x;
 ##[ ##1: #hh1; #y; ncases y;
          ##[ ##1: #hh2; nnormalize; napply (or2_elim (hh1 = hh2) (hh1 ≠ hh2) ? (H hh1 hh2));
                   ##[ ##1: #H1; nrewrite > H1; napply (or2_intro1 (? = ?) (? ≠ ?) (refl_eq …))
                   ##| ##2: #H1; napply (or2_intro2 (? = ?) (? ≠ ?) ?); nnormalize;
                            #H2; napply (H1 (nelist_destruct_nil_nil T … H2))
                   ##]
          ##| ##2: #hh2; #tt2; nnormalize; napply (or2_intro2 (? = ?) (? ≠ ?) ?);
                   nnormalize; #H1;
                   (* !!! ndestruct: assert false *)
                   napply (nelist_destruct_nil_cons T … H1)
          ##]
 ##| ##2: #hh1; #tt1; #H1; #y; ncases y;
          ##[ ##1: #hh1; nnormalize; napply (or2_intro2 (? = ?) (? ≠ ?) ?);
                   nnormalize; #H2;
                   (* !!! ndestruct: assert false *)
                   napply (nelist_destruct_cons_nil T … H2)
          ##| ##2: #hh2; #tt2; nnormalize; napply (or2_elim (hh1 = hh2) (hh1 ≠ hh2) ? (H …));
                   ##[ ##2: #H2; napply (or2_intro2 (? = ?) (? ≠ ?) ?);
                            nnormalize; #H3; napply (H2 (nelist_destruct_cons_cons_1 T … H3))
                   ##| ##1: #H2; napply (or2_elim (tt1 = tt2) (tt1 ≠ tt2) ? (H1 tt2));
                            ##[ ##2: #H3; napply (or2_intro2 (? = ?) (? ≠ ?) ?);
                                     nnormalize; #H4; napply (H3 (nelist_destruct_cons_cons_2 T … H4))
                            ##| ##1: #H3; napply (or2_intro1 (? = ?) (? ≠ ?) ?);
                                     nrewrite > H2; nrewrite > H3; napply refl_eq
                            ##]
                   ##]
          ##]
 ##]
nqed.

nlemma nbfoldrightnelist2_to_neq :
∀T1:Type.∀f:T1 → T1 → bool.
 (∀x,y.(f x y = false → x ≠ y)) →
 (∀l1,l2:ne_list T1.
  (bfold_right_neList2 T1 f l1 l2 = false → l1 ≠ l2)).
 #T; #f; #H; #l1;
 nelim l1;
 ##[ ##1: #hh1; #l2; ncases l2;
          ##[ ##1: #hh2; nnormalize; #H1; #H2; napply (H hh1 hh2 H1 (nelist_destruct_nil_nil T … H2))
          ##| ##2: #hh2; #ll2; #H1; nnormalize; #H2;
                   (* !!! ndestruct: assert false *)
                   napply (nelist_destruct_nil_cons T … H2)
          ##]
 ##| ##2: #hh1; #ll1; #H1; #l2; ncases l2;
          ##[ ##1: #hh2; #H2; nnormalize; #H3;
                   (* !!! ndestruct: assert false *)
                   napply (nelist_destruct_cons_nil T … H3)
          ##| ##2: #hh2; #ll2; #H2; nnormalize; #H3;
                   nchange in H2:(%) with (((f hh1 hh2)⊗(bfold_right_neList2 T f ll1 ll2)) = false);
                   napply (H1 ll2 ? (nelist_destruct_cons_cons_2 T … H3));
                   napply (or2_elim ??? (andb_false2 … H2) );
                   ##[ ##1: #H4; napply (absurd (hh1 = hh2) …);
                            ##[ ##1: nrewrite > (nelist_destruct_cons_cons_1 T … H3); napply refl_eq
                            ##| ##2: napply (H … H4)
                            ##]
                   ##| ##2: #H4; napply H4
                   ##]
          ##]
 ##]
nqed.

nlemma nelist_destruct :
∀T.(∀x,y:T.decidable (x = y)) →
   (∀h1,h2:T.∀l1,l2:ne_list T.
    (h1§§l1) ≠ (h2§§l2) → h1 ≠ h2 ∨ l1 ≠ l2).
 #T; #H; #h1; #h2; #l1; nelim l1;
 ##[ ##1: #hh1; #l2; ncases l2;
          ##[ ##1: #hh2; #H1; napply (or2_elim (h1 = h2) (h1 ≠ h2) ? (H …) …);
                   ##[ ##2: #H2; napply (or2_intro1 (h1 ≠ h2) («£hh1» ≠ «£hh2») H2)
                   ##| ##1: #H2; nrewrite > H2 in H1:(%); #H1;
                            napply (or2_elim (hh1 = hh2) (hh1 ≠ hh2) ? (H …) …);
                            ##[ ##2: #H3; napply (or2_intro2 (h2 ≠ h2) («£hh1» ≠ «£hh2») ?);
                                     nnormalize; #H4; napply (H3 (nelist_destruct_nil_nil T … H4))
                            ##| ##1: #H3; nrewrite > H3 in H1:(%); #H1; nelim (H1 (refl_eq …))
                            ##]
                   ##]
          ##| ##2: #hh2; #ll2; #H1; napply (or2_intro2 (h1 ≠ h2) («£hh1» ≠ (hh2§§ll2)) …);
                   nnormalize; #H2;
                   (* !!! ndestruct: assert false *)
                   napply (nelist_destruct_nil_cons T … H2)
          ##]
 ##| ##2: #hh1; #ll1; #H1; #l2; ncases l2;
          ##[ ##1: #hh2; #H2; napply (or2_intro2 (h1 ≠ h2) ((hh1§§ll1) ≠ «£hh2») …);
                   nnormalize; #H3;
                   (* !!! ndestruct: assert false *)
                   napply (nelist_destruct_cons_nil T … H3)
          ##| ##2: #hh2; #ll2; #H2;     
                   napply (or2_elim (h1 = h2) (h1 ≠ h2) ? (H h1 h2) …);
                   ##[ ##2: #H3; napply (or2_intro1 (h1 ≠ h2) ((hh1§§ll1) ≠ (hh2§§ll2)) H3)
                   ##| ##1: #H3; napply (or2_intro2 (h1 ≠ h2) ((hh1§§ll1) ≠ (hh2§§ll2) …));
                            nrewrite > H3 in H2:(%); #H2;
                            nnormalize; #H4; nrewrite > (nelist_destruct_cons_cons_1 T … H4) in H2:(%); #H2;
                            nrewrite > (nelist_destruct_cons_cons_2 T … H4) in H2:(%); #H2;
                            napply (H2 (refl_eq …))
                   ##]
          ##]
 ##]
nqed.

nlemma neq_to_nbfoldrightnelist2 :
∀T:Type.∀f:T → T → bool.
 (∀x,y:T.decidable (x = y)) →
 (∀x,y.(x ≠ y → f x y = false)) →
 (∀l1,l2:ne_list T.
  (l1 ≠ l2 → bfold_right_neList2 T f l1 l2 = false)).
 #T; #f; #H; #H1; #l1;
 nelim l1;
 ##[ ##1: #hh1; #l2; ncases l2;
          ##[ ##1: #hh2; nnormalize; #H2; napply (H1 hh1 hh2 ?);
                   nnormalize; #H3; nrewrite > H3 in H2:(%); #H2; napply (H2 (refl_eq …))
          ##| ##2: #hh2; #ll2; nnormalize; #H2; napply refl_eq
          ##]
 ##| ##2: #hh1; #ll1; #H2; #l2; ncases l2;
          ##[ ##1: #hh2; nnormalize; #H3; napply refl_eq
          ##| ##2: #hh2; #ll2; #H3;
                   nchange with (((f hh1 hh2)⊗(bfold_right_neList2 T f ll1 ll2)) = false);
                   napply (or2_elim (hh1 ≠ hh2) (ll1 ≠ ll2) ? (nelist_destruct T H … H3) …);
                   ##[ ##1: #H4; nrewrite > (H1 hh1 hh2 H4); nnormalize; napply refl_eq
                   ##| ##2: #H4; nrewrite > (H2 ll2 H4);
                            nrewrite > (symmetric_andbool (f hh1 hh2) false);
                            nnormalize; napply refl_eq
                   ##]
          ##]
 ##]
nqed.

nlemma nelist_is_comparable : comparable → comparable.
 #T; napply (mk_comparable (ne_list T));
 ##[ napply (ne_nil ? (zeroc T))
 ##| napply (λx.false)
 ##| napply (bfold_right_neList2 T (eqc T))
 ##| napply (bfoldrightnelist2_to_eq … (eqc T));
     napply (eqc_to_eq T)
 ##| napply (eq_to_bfoldrightnelist2 … (eqc T));
     napply (eq_to_eqc T)
 ##| napply (nbfoldrightnelist2_to_neq … (eqc T));
     napply (neqc_to_neq T)
 ##| napply (neq_to_nbfoldrightnelist2 … (eqc T));
     ##[ napply (decidable_c T)
     ##| napply (neq_to_neqc T)
     ##]
 ##| napply decidable_nelist;
     napply (decidable_c T)
 ##| napply symmetric_bfoldrightnelist2;
     napply (symmetric_eqc T)
 ##]
nqed.

unification hint 0 ≔ S: comparable;
         T ≟ (carr S),
         X ≟ (nelist_is_comparable S)
 (*********************************************) ⊢
         carr X ≡ ne_list T.

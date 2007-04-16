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

set "baseuri" "cic:/matita/decidable_kit/eqtype/".

include "decidable_kit/decidable.ma".
include "datatypes/constructors.ma".

(* ### types with a decidable AND rewrite (leibniz) compatible ### *)

definition eq_compatible ≝ λT:Type.λa,b:T. reflect (a = b).
    
record eqType : Type ≝ {
  sort :> Type;
  cmp : sort → sort → bool ;
  eqP : ∀x,y:sort. eq_compatible sort x y (cmp x y)
}.

lemma cmp_refl : ∀d:eqType.∀x. cmp d x x = true.
intros (d x); generalize in match (eqP d x x); intros (H);
unfold in H; (* inversion non fa whd!!! *)
inversion H; [ intros; reflexivity | intros (ABS); cases (ABS (refl_eq ? ?)) ]
qed. 

(* to use streicher *)
lemma eqType_decidable : ∀d:eqType. decT d.
intros (d); unfold decT; intros (x y); unfold decidable;
generalize in match (eqP d x y); intros (H);
cases H; [left | right] assumption;
qed.

lemma eqbP : ∀x,y:nat. eq_compatible nat x y (eqb x y).
intros (x y);
generalize in match (refl_eq ? (eqb x y));
generalize in match (eqb x y) in ⊢ (? ? ? % → %); intros 1 (b);
cases b; intros (H); [ apply reflect_true | apply reflect_false ];
[ apply (eqb_true_to_eq ? ? H) | apply (eqb_false_to_not_eq ? ? H) ]
qed.

definition nat_eqType : eqType ≝ mk_eqType ? ? eqbP.
(* XXX le coercion nel cast non vengono inserite *)
definition nat_canonical_eqType : nat → nat_eqType := 
  λn : nat.(n : sort nat_eqType).
coercion cic:/matita/decidable_kit/eqtype/nat_canonical_eqType.con.

definition bcmp ≝ λx,y:bool. match x with [ true ⇒ y | false => notb y ].

lemma bcmpP : ∀x,y:bool. eq_compatible bool x y (bcmp x y).
intros (x y);
generalize in match (refl_eq ? (bcmp x y));
generalize in match (bcmp x y) in ⊢ (? ? ? % → %); intros 1 (b);
cases b; intros (H); [ apply reflect_true | apply reflect_false ];
generalize in match H; clear H;
cases x; cases y; simplify; intros (H); [1,4: reflexivity];
(* non va: try destruct H; *)
[1,2,3,6: destruct H | *: unfold Not; intros (H1); destruct H1]
qed.

definition bool_eqType : eqType ≝  mk_eqType ? ? bcmpP.
definition bool_canonical_eqType : bool → bool_eqType := 
  λb : bool.(b : sort bool_eqType).
coercion cic:/matita/decidable_kit/eqtype/bool_canonical_eqType.con.

(* ### subtype of an eqType ### *)

record sigma (d : eqType) (p : d -> bool) : Type ≝ {
  sval : d;
  sprop : p sval = true
}.

notation "{x, h}"
  right associative with precedence 80
for @{'sig $x $h}.

interpretation "sub_eqType" 'sig x h = 
  (cic:/matita/decidable_kit/eqtype/sigma.ind#xpointer(1/1/1) _ _ x h).

(* restricting an eqType gives an eqType *)
lemma sigma_eq_dec : ∀d:eqType.∀p.∀x,y:sigma d p. 
  eq_compatible ? x y (cmp ? (sval ? ? x) (sval ? ?y)).
intros (d p x y);
generalize in match (refl_eq ? (cmp d (sval d p x) (sval d p y)));
generalize in match (cmp d (sval d p x) (sval d p y)) in ⊢ (? ? ? % → %); intros 1 (b);
cases b; cases x (s ps); cases y (t pt); simplify; intros (Hcmp);
[ constructor 1;
  generalize in match (eqP d s t); intros (Est);
  cases Est (H); clear Est;
  [ generalize in match ps;
    rewrite > H; intros (pt'); 
    rewrite < (pirrel bool (p t) true pt pt' (eqType_decidable bool_eqType));
    reflexivity;
  | cases (H (b2pT ? ? (eqP d s t) Hcmp))
  ]
| constructor 2; unfold Not; intros (H);
  (* XXX destruct H; *)
  change in Hcmp with (cmp d (match {?,ps} with [(mk_sigma s _)⇒s]) t = false);
  rewrite > H in Hcmp; simplify in Hcmp; rewrite > cmp_refl in Hcmp; destruct Hcmp;
]
qed. 

definition sub_eqType ≝ λd : eqType.λp. mk_eqType ? ? (sigma_eq_dec d p).

inductive in_sub (d : eqType) (p : d → bool) (x : d) : option (sigma d p) → Type ≝
| in_sig : ∀s : sigma d p. sval ? ? s = x → in_sub d p x (Some ? s)
| out_sig : p x = false → in_sub d p x (None ?).

definition if_p ≝ λd:eqType.λp:d→bool.λx:d. 
  match (eqP bool_eqType (p x) true) with 
  [ (reflect_true H) ⇒ Some ? {?,H} 
  | (reflect_false _) ⇒ None ?].

lemma in_sub_eq : ∀d,p,x. in_sub d p x (if_p d p x).
intros (d p x); unfold if_p;
cases (eqP bool_eqType (p x) true); simplify;
[ apply in_sig; reflexivity; | apply out_sig; apply (p2bF ? ? (idP ?) H)]
qed.  

definition ocmp : ∀d:eqType.∀a,b:option d.bool ≝
  λd:eqType.λa,b:option d.
  match a with 
  [ None ⇒ match b with [ None ⇒ true | (Some _) ⇒ false] 
  | (Some x) ⇒ match b with [ None ⇒ false | (Some y) ⇒ cmp d x y]].  
  
lemma ocmpP : ∀d:eqType.∀a,b:option d.eq_compatible ? a b (ocmp d a b).
intros (d a b);
generalize in match (refl_eq ? (ocmp ? a b));
generalize in match (ocmp ? a b) in ⊢ (? ? ? % → %); intros 1 (c);
cases c; intros (H); [ apply reflect_true | apply reflect_false ];
generalize in match H; clear H;
cases a; cases b; simplify; intros (H);
[1: reflexivity;
|2,3,5: destruct H;
|4: rewrite > (b2pT ? ? (eqP d ? ?) H); reflexivity; 
|6,7: unfold Not; intros (H1); destruct H1
|8: unfold Not; intros (H1); 
    (* ancora injection non va *)
    cut (s = s1); [ rewrite > Hcut in H;  rewrite > cmp_refl in H;  destruct H;].
    change with (match (Some d s) with
                 [ None ⇒ s | (Some s) ⇒ s] = s1); rewrite > H1;
                 simplify; reflexivity;] 
qed.

definition option_eqType : eqType → eqType ≝ λd:eqType.mk_eqType ? ? (ocmpP d).
definition option_canonical_eqType : ∀d:eqType.d → option_eqType d ≝
  λd:eqType.λx:d.(Some ? x : sort (option_eqType d)).
coercion cic:/matita/decidable_kit/eqtype/option_canonical_eqType.con.

(* belle le coercions! *)
definition test_canonical_option_eqType ≝ 
  (eq (option_eqType nat_eqType) O (S O)).

(* OUT OF PLACE *)       
lemma eqbC : ∀x,y:nat. eqb x y = eqb y x.
intros (x y); apply bool_to_eq; split; intros (H); 
rewrite > (b2pT ? ? (eqbP ? ?) H); rewrite > (cmp_refl nat_eqType);
reflexivity;
qed.

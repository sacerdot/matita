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

set "baseuri" "cic:/matita/library_autobatch/Q/q".

include "auto/Z/compare.ma".
include "auto/Z/plus.ma".

(* a fraction is a list of Z-coefficients for primes, in natural
order. The last coefficient must eventually be different from 0 *)

inductive fraction : Set \def
  pp : nat \to fraction
| nn: nat \to fraction
| cons : Z \to fraction \to fraction.

inductive ratio : Set \def
      one :  ratio
    | frac : fraction \to ratio.

(* a rational number is either O or a ratio with a sign *)
inductive Q : Set \def 
    OQ : Q
  | Qpos : ratio  \to Q
  | Qneg : ratio  \to Q.

(* double elimination principles *)
theorem fraction_elim2:
\forall R:fraction \to fraction \to Prop.
(\forall n:nat.\forall g:fraction.R (pp n) g) \to
(\forall n:nat.\forall g:fraction.R (nn n) g) \to
(\forall x:Z.\forall f:fraction.\forall m:nat.R (cons x f) (pp m)) \to
(\forall x:Z.\forall f:fraction.\forall m:nat.R (cons x f) (nn m)) \to
(\forall x,y:Z.\forall f,g:fraction.R f g \to R (cons x f) (cons y g)) \to
\forall f,g:fraction. R f g.
intros 7.
elim f
[ apply H
| apply H1
| elim g
  [ apply H2
  | apply H3
  | autobatch
    (*apply H4.
    apply H5*)
  ]
]
qed. 

(* boolean equality *)
let rec eqfb f g \def
match f with
[ (pp n) \Rightarrow 
  match g with 
  [ (pp m) \Rightarrow eqb n m
  | (nn m) \Rightarrow false
  | (cons y g1) \Rightarrow false]
| (nn n) \Rightarrow 
  match g with 
  [ (pp m) \Rightarrow false
  | (nn m) \Rightarrow eqb n m
  | (cons y g1) \Rightarrow false] 
| (cons x f1) \Rightarrow 
  match g with 
  [ (pp m) \Rightarrow false
  | (nn m) \Rightarrow false
  | (cons y g1) \Rightarrow andb (eqZb x y) (eqfb f1 g1)]]. 

(* discrimination *)
definition aux \def
  \lambda f. match f with
    [ (pp n) \Rightarrow n
    | (nn n) \Rightarrow n
    | (cons x f) \Rightarrow O].

definition fhd \def
\lambda f. match f with
    [ (pp n) \Rightarrow (pos n)
    | (nn n) \Rightarrow (neg n)
    | (cons x f) \Rightarrow x].

definition ftl \def
\lambda f. match f with
    [ (pp n) \Rightarrow (pp n)
    | (nn n) \Rightarrow (nn n)
    | (cons x f) \Rightarrow f].
    
theorem injective_pp : injective nat fraction pp.
unfold injective.
intros.
change with ((aux(pp x)) = (aux (pp y))).
autobatch.
(*apply eq_f.
assumption.*)
qed.

theorem injective_nn : injective nat fraction nn.
unfold injective.
intros.
change with ((aux (nn x)) = (aux (nn y))).
autobatch.
(*apply eq_f.
assumption.*)
qed.

theorem eq_cons_to_eq1: \forall f,g:fraction.\forall x,y:Z. 
(cons x f) = (cons y g) \to x = y.
intros.
change with ((fhd (cons x f)) = (fhd (cons y g))).
autobatch.
(*apply eq_f.assumption.*)
qed.

theorem eq_cons_to_eq2: \forall x,y:Z.\forall f,g:fraction.
(cons x f) = (cons y g) \to f = g.
intros.
change with ((ftl (cons x f)) = (ftl (cons y g))).
autobatch.
(*apply eq_f.assumption.*)
qed.

theorem not_eq_pp_nn: \forall n,m:nat. pp n \neq nn m.
intros.
unfold Not.
intro.
change with match (pp n) with
[ (pp n) \Rightarrow False
| (nn n) \Rightarrow True
| (cons x f) \Rightarrow True].
rewrite > H.
simplify.
exact I.
qed.

theorem not_eq_pp_cons: 
\forall n:nat.\forall x:Z. \forall f:fraction. 
pp n \neq cons x f.
intros.
unfold Not.
intro.
change with match (pp n) with
[ (pp n) \Rightarrow False
| (nn n) \Rightarrow True
| (cons x f) \Rightarrow True].
rewrite > H.
simplify.
exact I.
qed.

theorem not_eq_nn_cons: 
\forall n:nat.\forall x:Z. \forall f:fraction. 
nn n \neq cons x f.
intros.
unfold Not.
intro.
change with match (nn n) with
[ (pp n) \Rightarrow True
| (nn n) \Rightarrow False
| (cons x f) \Rightarrow True].
rewrite > H.
simplify.
exact I.
qed.

theorem decidable_eq_fraction: \forall f,g:fraction.
decidable (f = g).
intros.
unfold decidable.
apply (fraction_elim2 (\lambda f,g. f=g \lor (f=g \to False)))
[ intros.
  elim g1
  [ elim ((decidable_eq_nat n n1) : n=n1 \lor (n=n1 \to False))
    [ autobatch
      (*left.
      apply eq_f.
      assumption*)
    | right.
      intro.
      autobatch
      (*apply H.
      apply injective_pp.
      assumption*)
    ]
  | autobatch
    (*right.
    apply not_eq_pp_nn*)
  | autobatch
    (*right.
    apply not_eq_pp_cons*)
  ]
| intros.
  elim g1
  [ right.
    intro.
    apply (not_eq_pp_nn n1 n).
    autobatch
    (*apply sym_eq. 
    assumption*)
  | elim ((decidable_eq_nat n n1) : n=n1 \lor (n=n1 \to False))
    [ autobatch
      (*left. 
      apply eq_f. 
      assumption*)
    | right.
      intro.
      autobatch
      (*apply H.
      apply injective_nn.
      assumption*)
    ]
  | autobatch
    (*right.
    apply not_eq_nn_cons*)
  ]
| intros.
  right.
  intro.
  apply (not_eq_pp_cons m x f1).
  autobatch
  (*apply sym_eq.
  assumption*)
| intros.
  right.
  intro.
  apply (not_eq_nn_cons m x f1).
  autobatch
  (*apply sym_eq.
  assumption*)
| intros.
  elim H
  [ elim ((decidable_eq_Z x y) : x=y \lor (x=y \to False))
    [ autobatch
      (*left.
      apply eq_f2;
        assumption*)
    | right.
      intro.
      autobatch
      (*apply H2.
      apply (eq_cons_to_eq1 f1 g1).
      assumption*)
    ]    
  | right.
    intro.
    autobatch
    (*apply H1.
    apply (eq_cons_to_eq2 x y f1 g1).
    assumption*)
  ]
]
qed.

theorem eqfb_to_Prop: \forall f,g:fraction.
match (eqfb f g) with
[true \Rightarrow f=g
|false \Rightarrow f \neq g].
intros.
apply (fraction_elim2 
(\lambda f,g.match (eqfb f g) with
[true \Rightarrow f=g
|false \Rightarrow f \neq g]))
[ intros.
  elim g1
  [ simplify.
    apply eqb_elim
    [ intro.
      simplify.
      autobatch
      (*apply eq_f.
      assumption*)
    | intro.
      simplify.
      unfold Not.
      intro.
      autobatch
      (*apply H.
      apply injective_pp.
      assumption*)
    ]
  | simplify.
    apply not_eq_pp_nn
  | simplify.
    apply not_eq_pp_cons
  ]
| intros.
  elim g1
  [ simplify.
    unfold Not.
    intro.
    apply (not_eq_pp_nn n1 n).
    autobatch
    (*apply sym_eq.
    assumption*)
  | simplify.
    apply eqb_elim
    [ intro.
      simplify.
      autobatch
      (*apply eq_f.
      assumption*)
    | intro.
      simplify.
      unfold Not.
      intro.
      autobatch
      (*apply H.
      apply injective_nn.
      assumption*)
    ]
  | simplify.
    apply not_eq_nn_cons
  ]
| intros.
  simplify.
  unfold Not.
  intro.
  apply (not_eq_pp_cons m x f1).
  autobatch
  (*apply sym_eq.
  assumption*)
| intros.
  simplify.
  unfold Not.
  intro.
  apply (not_eq_nn_cons m x f1).
  autobatch
  (*apply sym_eq.
  assumption*)
| intros.
  simplify.
  apply eqZb_elim
  [ intro.
    generalize in match H.
    elim (eqfb f1 g1)
    [ simplify.
      apply eq_f2
      [ assumption
      | (*qui autobatch non chiude il goal*)
        apply H2
      ]
    | simplify.
      unfold Not.
      intro.
      apply H2.
      autobatch
      (*apply (eq_cons_to_eq2 x y).
      assumption*)
    ]
  | intro.
    simplify.
    unfold Not.
    intro.
    autobatch
    (*apply H1.
    apply (eq_cons_to_eq1 f1 g1).
    assumption*)
  ]
]
qed.

let rec finv f \def
  match f with
  [ (pp n) \Rightarrow (nn n)
  | (nn n) \Rightarrow (pp n)
  | (cons x g) \Rightarrow (cons (Zopp x) (finv g))].

definition Z_to_ratio :Z \to ratio \def
\lambda x:Z. match x with
[ OZ \Rightarrow one
| (pos n) \Rightarrow frac (pp n)
| (neg n) \Rightarrow frac (nn n)].

let rec ftimes f g \def
  match f with
  [ (pp n) \Rightarrow 
    match g with
    [(pp m) \Rightarrow Z_to_ratio (pos n + pos m)
    | (nn m) \Rightarrow Z_to_ratio (pos n + neg m)
    | (cons y g1) \Rightarrow frac (cons (pos n + y) g1)]
  | (nn n) \Rightarrow 
    match g with
    [(pp m) \Rightarrow Z_to_ratio (neg n + pos m)
    | (nn m) \Rightarrow Z_to_ratio (neg n + neg m)
    | (cons y g1) \Rightarrow frac (cons (neg n + y) g1)]
  | (cons x f1) \Rightarrow
    match g with
    [ (pp m) \Rightarrow frac (cons (x + pos m) f1)
    | (nn m) \Rightarrow frac (cons (x + neg m) f1)
    | (cons y g1) \Rightarrow 
      match ftimes f1 g1 with
        [ one \Rightarrow Z_to_ratio (x + y)
        | (frac h) \Rightarrow frac (cons (x + y) h)]]].
        
theorem symmetric2_ftimes: symmetric2 fraction ratio ftimes.
unfold symmetric2.
intros.
apply (fraction_elim2 (\lambda f,g.ftimes f g = ftimes g f))
[ intros.
  elim g
  [ change with (Z_to_ratio (pos n + pos n1) = Z_to_ratio (pos n1 + pos n)).
    autobatch
    (*apply eq_f.
    apply sym_Zplus*)
  | change with (Z_to_ratio (pos n + neg n1) = Z_to_ratio (neg n1 + pos n)).
    autobatch
    (*apply eq_f.
    apply sym_Zplus*)
  | change with (frac (cons (pos n + z) f) = frac (cons (z + pos n) f)).
    autobatch
    (*rewrite < sym_Zplus.
    reflexivity*)
  ]
| intros.
  elim g
  [ change with (Z_to_ratio (neg n + pos n1) = Z_to_ratio (pos n1 + neg n)).
    autobatch
    (*apply eq_f.
    apply sym_Zplus*)
  | change with (Z_to_ratio (neg n + neg n1) = Z_to_ratio (neg n1 + neg n)).
    autobatch
    (*apply eq_f.
    apply sym_Zplus*)
  | change with (frac (cons (neg n + z) f) = frac (cons (z + neg n) f)).
    autobatch
    (*rewrite < sym_Zplus.
    reflexivity*)
  ]
| intros.
  change with (frac (cons (x1 + pos m) f) = frac (cons (pos m + x1) f)).
  autobatch
  (*rewrite < sym_Zplus.
  reflexivity*)
| intros.
  change with (frac (cons (x1 + neg m) f) = frac (cons (neg m + x1) f)).
  autobatch
  (*rewrite < sym_Zplus.
  reflexivity*)
| intros.
   (*CSC: simplify does something nasty here because of a redex in Zplus *)
   change with 
   (match ftimes f g with
   [ one \Rightarrow Z_to_ratio (x1 + y1)
   | (frac h) \Rightarrow frac (cons (x1 + y1) h)] =
   match ftimes g f with
   [ one \Rightarrow Z_to_ratio (y1 + x1)
   | (frac h) \Rightarrow frac (cons (y1 + x1) h)]).
   rewrite < H.
   rewrite < sym_Zplus.
   reflexivity
]
qed.

theorem ftimes_finv : \forall f:fraction. ftimes f (finv f) = one.
intro.
elim f
[ change with (Z_to_ratio (pos n + - (pos n)) = one).
  autobatch
  (*rewrite > Zplus_Zopp.
  reflexivity*)
| change with (Z_to_ratio (neg n + - (neg n)) = one).
  autobatch
  (*rewrite > Zplus_Zopp.
  reflexivity*)
|
  (*CSC: simplify does something nasty here because of a redex in Zplus *)
  (* again: we would need something to help finding the right change *)
  change with 
  (match ftimes f1 (finv f1) with
  [ one \Rightarrow Z_to_ratio (z + - z)
  | (frac h) \Rightarrow frac (cons (z + - z) h)] = one).
  rewrite > H.
  rewrite > Zplus_Zopp.
  reflexivity
]
qed.

definition rtimes : ratio \to ratio \to ratio \def
\lambda r,s:ratio.
  match r with
  [one \Rightarrow s
  | (frac f) \Rightarrow 
      match s with 
      [one \Rightarrow frac f
      | (frac g) \Rightarrow ftimes f g]].

theorem symmetric_rtimes : symmetric ratio rtimes.
change with (\forall r,s:ratio. rtimes r s = rtimes s r).
intros.
elim r
[ elim s;reflexivity
| elim s
  [ reflexivity
  | simplify.
    apply symmetric2_ftimes
  ]
]
qed.

definition rinv : ratio \to ratio \def
\lambda r:ratio.
  match r with
  [one \Rightarrow one
  | (frac f) \Rightarrow frac (finv f)].

theorem rtimes_rinv: \forall r:ratio. rtimes r (rinv r) = one.
intro.
elim r
[ reflexivity
| simplify.
  apply ftimes_finv
]
qed.

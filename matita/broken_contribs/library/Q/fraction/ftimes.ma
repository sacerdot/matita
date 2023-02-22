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

include "Q/ratio/ratio.ma".
include "Q/fraction/finv.ma".
include "Q/nat_fact/times.ma".
include "Z/times.ma".

definition nat_frac_item_to_ratio: Z \to ratio \def
\lambda x:Z. match x with
[ OZ \Rightarrow one
| (pos n) \Rightarrow frac (pp n)
| (neg n) \Rightarrow frac (nn n)].

let rec ftimes f g \def
  match f with
  [ (pp n) \Rightarrow 
    match g with
    [(pp m) \Rightarrow nat_frac_item_to_ratio (pos n + pos m)
    | (nn m) \Rightarrow nat_frac_item_to_ratio (pos n + neg m)
    | (cons y g1) \Rightarrow frac (cons (pos n + y) g1)]
  | (nn n) \Rightarrow 
    match g with
    [(pp m) \Rightarrow nat_frac_item_to_ratio (neg n + pos m)
    | (nn m) \Rightarrow nat_frac_item_to_ratio (neg n + neg m)
    | (cons y g1) \Rightarrow frac (cons (neg n + y) g1)]
  | (cons x f1) \Rightarrow
    match g with
    [ (pp m) \Rightarrow frac (cons (x + pos m) f1)
    | (nn m) \Rightarrow frac (cons (x + neg m) f1)
    | (cons y g1) \Rightarrow 
      match ftimes f1 g1 with
        [ one \Rightarrow nat_frac_item_to_ratio (x + y)
        | (frac h) \Rightarrow frac (cons (x + y) h)]]].
        
theorem symmetric2_ftimes: symmetric2 fraction ratio ftimes.
unfold symmetric2. intros.apply (fraction_elim2 (\lambda f,g.ftimes f g = ftimes g f)).
  intros.elim g.
    change with (nat_frac_item_to_ratio (pos n + pos n1) = nat_frac_item_to_ratio (pos n1 + pos n)).
     apply eq_f.apply sym_Zplus.
    change with (nat_frac_item_to_ratio (pos n + neg n1) = nat_frac_item_to_ratio (neg n1 + pos n)).
     apply eq_f.apply sym_Zplus.
    change with (frac (cons (pos n + z) f) = frac (cons (z + pos n) f)).
     rewrite < sym_Zplus.reflexivity.
  intros.elim g.
    change with (nat_frac_item_to_ratio (neg n + pos n1) = nat_frac_item_to_ratio (pos n1 + neg n)).
     apply eq_f.apply sym_Zplus.
    change with (nat_frac_item_to_ratio (neg n + neg n1) = nat_frac_item_to_ratio (neg n1 + neg n)).
     apply eq_f.apply sym_Zplus.
    change with (frac (cons (neg n + z) f) = frac (cons (z + neg n) f)).
     rewrite < sym_Zplus.reflexivity.
  intros.change with (frac (cons (x1 + pos m) f) = frac (cons (pos m + x1) f)).
   rewrite < sym_Zplus.reflexivity.
  intros.change with (frac (cons (x1 + neg m) f) = frac (cons (neg m + x1) f)).
   rewrite < sym_Zplus.reflexivity.
  intros.
   (*CSC: simplify does something nasty here because of a redex in Zplus *)
   change with 
   (match ftimes f g with
   [ one \Rightarrow nat_frac_item_to_ratio (x1 + y1)
   | (frac h) \Rightarrow frac (cons (x1 + y1) h)] =
   match ftimes g f with
   [ one \Rightarrow nat_frac_item_to_ratio (y1 + x1)
   | (frac h) \Rightarrow frac (cons (y1 + x1) h)]).
    rewrite < H.rewrite < sym_Zplus.reflexivity.
qed.

theorem ftimes_finv : \forall f:fraction. ftimes f (finv f) = one.
intro.elim f.
  change with (nat_frac_item_to_ratio (pos n + - (pos n)) = one).
   rewrite > Zplus_Zopp.reflexivity.
  change with (nat_frac_item_to_ratio (neg n + - (neg n)) = one).
   rewrite > Zplus_Zopp.reflexivity.
   (*CSC: simplify does something nasty here because of a redex in Zplus *)
(* again: we would need something to help finding the right change *)
  change with 
  (match ftimes f1 (finv f1) with
  [ one \Rightarrow nat_frac_item_to_ratio (z + - z)
  | (frac h) \Rightarrow frac (cons (z + - z) h)] = one).
  rewrite > H.rewrite > Zplus_Zopp.reflexivity.
qed.

theorem times_f_ftimes: \forall n,m.
frac (nat_fact_to_fraction (times_f n m))
= ftimes (nat_fact_to_fraction n) (nat_fact_to_fraction m).
intro.
elim n
  [elim m
    [simplify.
     rewrite < plus_n_Sm.reflexivity
    |elim n2
      [simplify.rewrite < plus_n_O.reflexivity
      |simplify.reflexivity.
      ]
    ]
  |elim m
    [elim n1
      [simplify.reflexivity
      |simplify.rewrite < plus_n_Sm.reflexivity
      ]
    |simplify.
     cut (\exist h.ftimes (nat_fact_to_fraction n2) (nat_fact_to_fraction n4) = frac h)
      [elim Hcut.
       rewrite > H2.
       simplify.apply eq_f.
       apply eq_f2
        [apply eq_plus_Zplus
        |apply injective_frac.
         rewrite < H2.
         apply H
        ]
      |generalize in match n4.
       elim n2
        [cases n6;simplify;
          [ exists; [2: autobatch;]
          | exists; [2:autobatch;]
          ]
        |cases n7;simplify
          [exists;[2:autobatch]
          |elim (H2 n9).
           rewrite > H3.
           simplify.
           exists;[2:autobatch]
          ]]]]]
qed.
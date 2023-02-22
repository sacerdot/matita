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

include "Q/ratio/rinv.ma".
include "Q/fraction/ftimes.ma".

definition rtimes : ratio → ratio → ratio ≝
λr,s:ratio.
  match r with
  [one ⇒ s
  | (frac f) ⇒ 
      match s with 
      [one ⇒ frac f
      | (frac g) ⇒ ftimes f g]].

theorem symmetric_rtimes : symmetric ratio rtimes.
change with (∀r,s:ratio. rtimes r s = rtimes s r).
intros.
elim r. elim s.
reflexivity.
reflexivity.
elim s.
reflexivity.
simplify.apply symmetric2_ftimes.
qed.

variant sym_rtimes : ∀x,y:ratio. rtimes x y = rtimes y x ≝ symmetric_rtimes.

theorem rtimes_r_one: ∀r.rtimes r one = r.
 intro; cases r;reflexivity.
qed.

theorem rtimes_one_r: ∀r.rtimes one r = r.
intro; cases r;reflexivity.
qed.

theorem rtimes_Zplus: \forall x,y.
rtimes (nat_frac_item_to_ratio x) (nat_frac_item_to_ratio y) =
nat_frac_item_to_ratio (x + y).
intro.
elim x
  [reflexivity
  |*:elim y;reflexivity
  ]
qed.

theorem rtimes_Zplus1: \forall x,y,f.
rtimes (nat_frac_item_to_ratio x) (frac (cons y f)) =
frac (cons ((x + y)) f).
intro.
elim x
  [reflexivity
  |*:elim y;reflexivity
  ]
qed.

theorem rtimes_Zplus2: \forall x,y,f.
rtimes (frac (cons y f)) (nat_frac_item_to_ratio x) =
frac (cons ((y + x)) f).
intros.
elim x
  [elim y;reflexivity
  |*:elim y;reflexivity
  ]
qed.

theorem or_one_frac: \forall f,g.
rtimes (frac f) (frac g) = one \lor
\exists h.rtimes (frac f) (frac g) = frac h.
intros.
elim (rtimes (frac f) (frac g))
  [left.reflexivity
  |right.apply (ex_intro ? ? f1).reflexivity
  ]
qed.

theorem one_to_rtimes_Zplus3: \forall x,y:Z.\forall f,g:fraction.
rtimes (frac f) (frac g) = one \to
rtimes (frac (cons x f)) (frac (cons y g)) = nat_frac_item_to_ratio (x + y).
intros.simplify.simplify in H.rewrite > H.simplify.
reflexivity.
qed.

theorem frac_to_rtimes_Zplus3: \forall x,y:Z.\forall f,g:fraction.
\forall h.rtimes (frac f) (frac g) = frac h \to
rtimes (frac (cons x f)) (frac (cons y g)) = frac (cons (x + y) h).
intros.simplify.simplify in H.rewrite > H.simplify.
reflexivity.
qed.


theorem nat_frac_item_to_ratio_frac_frac: \forall z,f1,f2.
rtimes (rtimes (nat_frac_item_to_ratio z) (frac f1)) (frac f2)
=rtimes (nat_frac_item_to_ratio z) (rtimes (frac f1) (frac f2)).
intros 2.elim f1
  [elim f2
    [change with
     (rtimes (rtimes (nat_frac_item_to_ratio z) (nat_frac_item_to_ratio (pos n))) (nat_frac_item_to_ratio (pos n1))
      =rtimes (nat_frac_item_to_ratio z) (rtimes (nat_frac_item_to_ratio (pos n)) (nat_frac_item_to_ratio (pos n1)))).
     rewrite > rtimes_Zplus.rewrite > rtimes_Zplus.
     rewrite > rtimes_Zplus.rewrite > rtimes_Zplus.
     rewrite > assoc_Zplus.reflexivity
    |change with
     (rtimes (rtimes (nat_frac_item_to_ratio z) (nat_frac_item_to_ratio (pos n))) (nat_frac_item_to_ratio (neg n1))
      =rtimes (nat_frac_item_to_ratio z) (rtimes (nat_frac_item_to_ratio (pos n)) (nat_frac_item_to_ratio (neg n1)))).
     rewrite > rtimes_Zplus.rewrite > rtimes_Zplus.
     rewrite > rtimes_Zplus.rewrite > rtimes_Zplus.
     rewrite > assoc_Zplus.reflexivity
    |change with
      (rtimes (rtimes (nat_frac_item_to_ratio z) (nat_frac_item_to_ratio (pos n))) (frac (cons z1 f))
       = rtimes (nat_frac_item_to_ratio z) (rtimes (nat_frac_item_to_ratio (pos n)) (frac (cons z1 f)))).
     rewrite > rtimes_Zplus.rewrite > rtimes_Zplus1.
     rewrite > rtimes_Zplus1.rewrite > rtimes_Zplus1.
     rewrite > assoc_Zplus.reflexivity
    ]
  |elim f2
    [change with
     (rtimes (rtimes (nat_frac_item_to_ratio z) (nat_frac_item_to_ratio (neg n))) (nat_frac_item_to_ratio (pos n1))
      =rtimes (nat_frac_item_to_ratio z) (rtimes (nat_frac_item_to_ratio (neg n)) (nat_frac_item_to_ratio (pos n1)))).
     rewrite > rtimes_Zplus.rewrite > rtimes_Zplus.
     rewrite > rtimes_Zplus.rewrite > rtimes_Zplus.
     rewrite > assoc_Zplus.reflexivity
    |change with
     (rtimes (rtimes (nat_frac_item_to_ratio z) (nat_frac_item_to_ratio (neg n))) (nat_frac_item_to_ratio (neg n1))
      =rtimes (nat_frac_item_to_ratio z) (rtimes (nat_frac_item_to_ratio (neg n)) (nat_frac_item_to_ratio (neg n1)))).
     rewrite > rtimes_Zplus.rewrite > rtimes_Zplus.
     rewrite > rtimes_Zplus.rewrite > rtimes_Zplus.
     rewrite > assoc_Zplus.reflexivity
    |change with
      (rtimes (rtimes (nat_frac_item_to_ratio z) (nat_frac_item_to_ratio (neg n))) (frac (cons z1 f))
       = rtimes (nat_frac_item_to_ratio z) (rtimes (nat_frac_item_to_ratio (neg n)) (frac (cons z1 f)))).
     rewrite > rtimes_Zplus.rewrite > rtimes_Zplus1.
     rewrite > rtimes_Zplus1.rewrite > rtimes_Zplus1.
     rewrite > assoc_Zplus.reflexivity
    ]
  |elim f2
    [change with
     (rtimes (rtimes (nat_frac_item_to_ratio z) (frac (cons z1 f))) (nat_frac_item_to_ratio (pos n))
      =rtimes (nat_frac_item_to_ratio z) (rtimes (frac (cons z1 f)) (nat_frac_item_to_ratio (pos n)))).
     rewrite > rtimes_Zplus1.rewrite > rtimes_Zplus2.
     rewrite > rtimes_Zplus2.rewrite > rtimes_Zplus1.
     rewrite > assoc_Zplus.reflexivity
    |change with
     (rtimes (rtimes (nat_frac_item_to_ratio z) (frac (cons z1 f))) (nat_frac_item_to_ratio (neg n))
      =rtimes (nat_frac_item_to_ratio z) (rtimes (frac (cons z1 f)) (nat_frac_item_to_ratio (neg n)))).  
     rewrite > rtimes_Zplus1.rewrite > rtimes_Zplus2.
     rewrite > rtimes_Zplus2.rewrite > rtimes_Zplus1.
     rewrite > assoc_Zplus.reflexivity
    |elim (or_one_frac f f3)
      [rewrite > rtimes_Zplus1.
       rewrite > (one_to_rtimes_Zplus3 ? ? ? ? H2).
       rewrite > (one_to_rtimes_Zplus3 ? ? ? ? H2).
       rewrite > rtimes_Zplus.
       rewrite > assoc_Zplus.reflexivity
      |elim H2.clear H2.
       rewrite > rtimes_Zplus1.
       rewrite > (frac_to_rtimes_Zplus3 ? ? ? ? a H3).
       rewrite > (frac_to_rtimes_Zplus3 ? ? ? ? a H3).
       rewrite > rtimes_Zplus1.
       rewrite > assoc_Zplus.reflexivity
      ]
    ]
  ]
qed.

theorem cons_frac_frac: \forall f1,z,f,f2.
rtimes (rtimes (frac (cons z f)) (frac f1)) (frac f2)
=rtimes (frac (cons z f)) (rtimes (frac f1) (frac f2)).
intro.elim f1
  [elim f2
    [change with
     (rtimes (rtimes (frac (cons z f)) (nat_frac_item_to_ratio (pos n))) (nat_frac_item_to_ratio (pos n1))
      =rtimes (frac (cons z f)) (rtimes (nat_frac_item_to_ratio (pos n)) (nat_frac_item_to_ratio (pos n1)))).
     rewrite > rtimes_Zplus2.rewrite > rtimes_Zplus2.
     rewrite > rtimes_Zplus.rewrite > rtimes_Zplus2.
     rewrite > assoc_Zplus.reflexivity
    |change with
     (rtimes (rtimes (frac (cons z f)) (nat_frac_item_to_ratio (pos n))) (nat_frac_item_to_ratio (neg n1))
      =rtimes (frac (cons z f)) (rtimes (nat_frac_item_to_ratio (pos n)) (nat_frac_item_to_ratio (neg n1)))).
     rewrite > rtimes_Zplus2.rewrite > rtimes_Zplus2.
     rewrite > rtimes_Zplus.rewrite > rtimes_Zplus2.
     rewrite > assoc_Zplus.reflexivity
    |change with
      (rtimes (rtimes (frac (cons z f)) (nat_frac_item_to_ratio (pos n))) (frac (cons z1 f3))
       = rtimes (frac (cons z f)) (rtimes (nat_frac_item_to_ratio (pos n)) (frac (cons z1 f3)))).
     rewrite > rtimes_Zplus2.rewrite > rtimes_Zplus1.
     elim (or_one_frac f f3)
      [rewrite > (one_to_rtimes_Zplus3 ? ? ? ? H1).
       rewrite > (one_to_rtimes_Zplus3 ? ? ? ? H1).
       rewrite > assoc_Zplus.reflexivity
      |elim H1.clear H1.
       rewrite > (frac_to_rtimes_Zplus3 ? ? ? ? a H2).
       rewrite > (frac_to_rtimes_Zplus3 ? ? ? ? a H2).
       rewrite > assoc_Zplus.reflexivity
      ]
    ]
  |elim f2
    [change with
     (rtimes (rtimes (frac (cons z f)) (nat_frac_item_to_ratio (neg n))) (nat_frac_item_to_ratio (pos n1))
      =rtimes (frac (cons z f)) (rtimes (nat_frac_item_to_ratio (neg n)) (nat_frac_item_to_ratio (pos n1)))).
     rewrite > rtimes_Zplus2.rewrite > rtimes_Zplus2.
     rewrite > rtimes_Zplus.rewrite > rtimes_Zplus2.
     rewrite > assoc_Zplus.reflexivity
    |change with
     (rtimes (rtimes (frac (cons z f)) (nat_frac_item_to_ratio (neg n))) (nat_frac_item_to_ratio (neg n1))
      =rtimes (frac (cons z f)) (rtimes (nat_frac_item_to_ratio (neg n)) (nat_frac_item_to_ratio (neg n1)))).
     rewrite > rtimes_Zplus2.rewrite > rtimes_Zplus2.
     rewrite > rtimes_Zplus.rewrite > rtimes_Zplus2.
     rewrite > assoc_Zplus.reflexivity
    |change with
      (rtimes (rtimes (frac (cons z f)) (nat_frac_item_to_ratio (neg n))) (frac (cons z1 f3))
       = rtimes (frac (cons z f)) (rtimes (nat_frac_item_to_ratio (neg n)) (frac (cons z1 f3)))).
     rewrite > rtimes_Zplus2.rewrite > rtimes_Zplus1.
     elim (or_one_frac f f3)
      [rewrite > (one_to_rtimes_Zplus3 ? ? ? ? H1).
       rewrite > (one_to_rtimes_Zplus3 ? ? ? ? H1).
       rewrite > assoc_Zplus.reflexivity
      |elim H1.clear H1.
       rewrite > (frac_to_rtimes_Zplus3 ? ? ? ? a H2).
       rewrite > (frac_to_rtimes_Zplus3 ? ? ? ? a H2).
       rewrite > assoc_Zplus.reflexivity
      ]
    ]
  |elim f3
    [change with
     (rtimes (rtimes (frac (cons z1 f2)) (frac (cons z f))) (nat_frac_item_to_ratio (pos n))
      =rtimes (frac (cons z1 f2)) (rtimes (frac (cons z f)) (nat_frac_item_to_ratio (pos n)))).
     rewrite > rtimes_Zplus2.
     elim (or_one_frac f2 f)
      [rewrite > (one_to_rtimes_Zplus3 ? ? ? ? H1).
       rewrite > (one_to_rtimes_Zplus3 ? ? ? ? H1).
       rewrite > rtimes_Zplus.
       rewrite > assoc_Zplus.reflexivity
      |elim H1.clear H1.
       rewrite > (frac_to_rtimes_Zplus3 ? ? ? ? a H2).
       rewrite > (frac_to_rtimes_Zplus3 ? ? ? ? a H2).
       rewrite > rtimes_Zplus2.
       rewrite > assoc_Zplus.reflexivity
      ]
    |change with
     (rtimes (rtimes (frac (cons z1 f2)) (frac (cons z f))) (nat_frac_item_to_ratio (neg n))
      =rtimes (frac (cons z1 f2)) (rtimes (frac (cons z f)) (nat_frac_item_to_ratio (neg n)))).
     rewrite > rtimes_Zplus2.
     elim (or_one_frac f2 f)
      [rewrite > (one_to_rtimes_Zplus3 ? ? ? ? H1).
       rewrite > (one_to_rtimes_Zplus3 ? ? ? ? H1).
       rewrite > rtimes_Zplus.
       rewrite > assoc_Zplus.reflexivity
      |elim H1.clear H1.
       rewrite > (frac_to_rtimes_Zplus3 ? ? ? ? a H2).
       rewrite > (frac_to_rtimes_Zplus3 ? ? ? ? a H2).
       rewrite > rtimes_Zplus2.
       rewrite > assoc_Zplus.reflexivity
      ]
    |elim (or_one_frac f2 f)
      [rewrite > (one_to_rtimes_Zplus3 ? ? ? ? H2).
       rewrite > rtimes_Zplus1.
       elim (or_one_frac f f4)
        [rewrite > (one_to_rtimes_Zplus3 ? ? ? ? H3).
         rewrite > rtimes_Zplus2.
         cut (f4 = f2)
          [rewrite > Hcut.
           rewrite > assoc_Zplus.reflexivity
          |apply injective_frac.
           rewrite < rtimes_one_r.
           rewrite < H2.
           (* problema inaspettato: mi serve l'unicita' dell'inversa,
              che richiede (?) l'associativita. Per fortuna basta 
              l'ipotesi induttiva. *)
           cases f2
            [change with 
             (rtimes (rtimes (nat_frac_item_to_ratio (pos n)) (frac f)) (frac f4)=nat_frac_item_to_ratio (pos n)).
             rewrite > nat_frac_item_to_ratio_frac_frac.
             rewrite > H3.
             rewrite > rtimes_r_one.
             reflexivity
            |change with 
             (rtimes (rtimes (nat_frac_item_to_ratio (neg n)) (frac f)) (frac f4)=nat_frac_item_to_ratio (neg n)).
             rewrite > nat_frac_item_to_ratio_frac_frac.
             rewrite > H3.
             rewrite > rtimes_r_one.
             reflexivity
            |rewrite > H.
             rewrite > H3.
             rewrite > rtimes_r_one.
             reflexivity
            ]
          ]
        |elim H3.clear H3.
         rewrite > (frac_to_rtimes_Zplus3 ? ? ? ? a H4).
         cut (rtimes (frac f2) (frac a) = frac f4)
          [rewrite > (frac_to_rtimes_Zplus3 ? ? ? ? f4 Hcut).
           rewrite > assoc_Zplus.reflexivity
          |rewrite < H4.
           generalize in match H2.
           cases f2;intro
            [change with 
             (rtimes (nat_frac_item_to_ratio (pos n)) (rtimes (frac f)(frac f4)) =frac f4).
             rewrite < nat_frac_item_to_ratio_frac_frac.
             rewrite > H3.
             rewrite > rtimes_one_r.
             reflexivity
            |change with 
             (rtimes (nat_frac_item_to_ratio (neg n)) (rtimes (frac f)(frac f4)) =frac f4).
             rewrite < nat_frac_item_to_ratio_frac_frac.
             rewrite > H3.
             rewrite > rtimes_one_r.
             reflexivity
            |rewrite < H.
             rewrite > H3.
             rewrite > rtimes_one_r.
             reflexivity
            ]
          ]
        ]
      |elim H2.clear H2.
       rewrite > (frac_to_rtimes_Zplus3 ? ? ? ? a H3).
       elim (or_one_frac f f4)
        [rewrite > (one_to_rtimes_Zplus3 ? ? ? ? H2).
         rewrite > rtimes_Zplus2.
         cut (rtimes (frac a) (frac f4) = frac f2)
          [rewrite > (frac_to_rtimes_Zplus3 ? ? ? ? f2 Hcut).
           rewrite > assoc_Zplus.reflexivity
          |rewrite < H3.
           generalize in match H2.
           cases f2;intro
            [change with 
             (rtimes (rtimes (nat_frac_item_to_ratio (pos n)) (frac f)) (frac f4)=nat_frac_item_to_ratio (pos n)).
             rewrite > nat_frac_item_to_ratio_frac_frac.
             rewrite > H4.
             rewrite > rtimes_r_one.
             reflexivity
            |change with 
             (rtimes (rtimes (nat_frac_item_to_ratio (neg n)) (frac f)) (frac f4)=nat_frac_item_to_ratio (neg n)).
             rewrite > nat_frac_item_to_ratio_frac_frac.
             rewrite > H4.
             rewrite > rtimes_r_one.
             reflexivity
            |rewrite > H.
             rewrite > H4.
             rewrite > rtimes_r_one.
             reflexivity
            ]
          ]
        |elim H2.clear H2.
         rewrite > (frac_to_rtimes_Zplus3 ? ? ? ? a1 H4).
         elim (or_one_frac a f4)
          [rewrite > (one_to_rtimes_Zplus3 ? ? ? ? H2).
           cut (rtimes (frac f2) (frac a1) = one)
            [rewrite > (one_to_rtimes_Zplus3 ? ? ? ? Hcut).
             rewrite > assoc_Zplus.reflexivity
            |rewrite < H4.
             generalize in match H3.
             cases f2;intro
              [change with 
               (rtimes (nat_frac_item_to_ratio (pos n)) (rtimes (frac f)(frac f4)) = one).
               rewrite < nat_frac_item_to_ratio_frac_frac.
               rewrite > H5.
               assumption
              |change with 
               (rtimes (nat_frac_item_to_ratio (neg n)) (rtimes (frac f)(frac f4)) = one).
               rewrite < nat_frac_item_to_ratio_frac_frac.
               rewrite > H5.
               assumption
              |rewrite < H.
               rewrite > H5.
               assumption
              ]
            ]
          |elim H2.clear H2.
           rewrite > (frac_to_rtimes_Zplus3 ? ? ? ? a2 H5).
           cut (rtimes (frac f2) (frac a1) = frac a2)
            [rewrite > (frac_to_rtimes_Zplus3 ? ? ? ? a2 Hcut).
             rewrite > assoc_Zplus.reflexivity
            |rewrite < H4.
             generalize in match H3.
             cases f2;intro
              [change with 
               (rtimes (nat_frac_item_to_ratio (pos n)) (rtimes (frac f)(frac f4)) = frac a2).
               rewrite < nat_frac_item_to_ratio_frac_frac.
               rewrite > H2.
               assumption
              |change with 
               (rtimes (nat_frac_item_to_ratio (neg n)) (rtimes (frac f)(frac f4)) = frac a2).
               rewrite < nat_frac_item_to_ratio_frac_frac.
               rewrite > H2.
               assumption
              |rewrite < H.
               rewrite > H2.
               assumption
              ]
            ]
          ]
        ]
      ]
    ]
  ]
qed.
       
theorem frac_frac_fracaux: ∀f,f1,f2.
rtimes (rtimes (frac f) (frac f1)) (frac f2)
=rtimes (frac f) (rtimes (frac f1) (frac f2)).
intros.
cases f
  [change with
   (rtimes (rtimes (nat_frac_item_to_ratio (pos n)) (frac f1)) (frac f2)
    =rtimes (nat_frac_item_to_ratio (pos n)) (rtimes (frac f1) (frac f2))).
   apply nat_frac_item_to_ratio_frac_frac
  |change with
   (rtimes (rtimes (nat_frac_item_to_ratio (neg n)) (frac f1)) (frac f2)
    =rtimes (nat_frac_item_to_ratio (neg n)) (rtimes (frac f1) (frac f2))).
   apply nat_frac_item_to_ratio_frac_frac
  |apply cons_frac_frac]
qed.


theorem associative_rtimes:associative ? rtimes.
unfold.intros.
cases x
  [reflexivity
  |cases y
    [reflexivity.
    |cases z
      [rewrite > rtimes_r_one.rewrite > rtimes_r_one.reflexivity
      |apply frac_frac_fracaux
      ]]]
qed.


theorem rtimes_rinv: ∀r:ratio. rtimes r (rinv r) = one.
intro.elim r.
reflexivity.
simplify.apply ftimes_finv.
qed.

theorem rtimes_Zplus3: \forall x,y:Z.\forall f,g:fraction.
(rtimes (frac f) (frac g) = one \land
 rtimes (frac (cons x f)) (frac (cons y g)) = nat_frac_item_to_ratio (x + y))
\lor (\exists h.rtimes (frac f) (frac g) = frac h \land
rtimes (frac (cons x f)) (frac (cons y g)) =
frac (cons (x + y) h)).
intros.
simplify.
elim (rtimes (frac f) (frac g));simplify
  [left.split;reflexivity
  |right.
   apply (ex_intro ? ? f1).
   split;reflexivity]
qed.
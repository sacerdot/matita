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

include "lift.ma".

(* DELIFTING SUBSTITUTION ***************************************************)

(* Policy: depth (level) metavariables: d, e (as for lift) *)
let rec dsubst C d M on M ≝ match M with
[ VRef i   ⇒ tri … i d (#i) (↑[i] C) (#(i-1))
| Abst A   ⇒ 𝛌. (dsubst C (d+1) A)
| Appl B A ⇒ @ (dsubst C d B). (dsubst C d A)
].

interpretation "delifting substitution"
   'DSubst C d M = (dsubst C d M).

(* Note: the notation with "/" does not work *)
notation "hvbox( [ d ⬐ break C ] break term 55 M )"
   non associative with precedence 55
   for @{ 'DSubst $C $d $M }.

notation > "hvbox( [ ⬐ C ] break term 55 M )"
   non associative with precedence 55
   for @{ 'DSubst $C 0 $M }.

lemma dsubst_vref_lt: ∀i,d,C. i < d → [ d ⬐ C ] #i = #i.
normalize /2 width=1/
qed.

lemma dsubst_vref_eq: ∀d,C. [ d ⬐ C ] #d = ↑[d]C.
normalize //
qed.

lemma dsubst_vref_gt: ∀i,d,C. d < i → [ d ⬐ C ] #i = #(i-1).
normalize /2 width=1/
qed.

theorem dsubst_lift_le: ∀h,C,M,d1,d2. d2 ≤ d1 →
                        [ d2 ⬐ ↑[d1 - d2, h] C ] ↑[d1 + 1, h] M = ↑[d1, h] [ d2 ⬐ C ] M.
#h #C #M elim M -M
[ #i #d1 #d2 #Hd21 elim (lt_or_eq_or_gt i d2) #Hid2
  [ lapply (lt_to_le_to_lt … Hid2 Hd21) -Hd21 #Hid1
    >(dsubst_vref_lt … Hid2) >(lift_vref_lt … Hid1) >lift_vref_lt /2 width=1/
  | destruct >dsubst_vref_eq >lift_vref_lt /2 width=1/
  | >(dsubst_vref_gt … Hid2) -Hd21 elim (lt_or_ge (i-1) d1) #Hi1d1
    [ >(lift_vref_lt … Hi1d1) >lift_vref_lt /2 width=1/
    | lapply (ltn_to_ltO … Hid2) #Hi
      >(lift_vref_ge … Hi1d1) >lift_vref_ge /2 width=1/ -Hi1d1 >plus_minus // /3 width=1/
    ]
  ]
| normalize #A #IHA #d1 #d2 #Hd21
  lapply (IHA (d1+1) (d2+1) ?) -IHA /2 width=1/
| normalize #B #A #IHB #IHA #d1 #d2 #Hd21
  >IHB -IHB // >IHA -IHA //
]
qed.
 
theorem dsubst_lift_be: ∀h,C,M,d1,d2. d1 ≤ d2 → d2 ≤ d1 + h →
                        [ d2 ⬐ C ] ↑[d1, h + 1] M = ↑[d1, h] M.
#h #C #M elim M -M
[ #i #d1 #d2 #Hd12 #Hd21 elim (lt_or_ge i d1) #Hid1
  [ lapply (lt_to_le_to_lt … Hid1 Hd12) -Hd12 -Hd21 #Hid2
    >(lift_vref_lt … Hid1) >(lift_vref_lt … Hid1) /2 width=1/
  | lapply (transitive_le … (i+h) Hd21 ?) -Hd12 -Hd21 /2 width=1/ #Hd2
    >(lift_vref_ge … Hid1) >(lift_vref_ge … Hid1) -Hid1
    >dsubst_vref_gt // /2 width=1/
  ]
| normalize #A #IHA #d1 #d2 #Hd12 #Hd21
  >IHA -IHA // /2 width=1/
| normalize #B #A #IHB #IHA #d1 #d2 #Hd12 #Hd21
  >IHB -IHB // >IHA -IHA //
]
qed.

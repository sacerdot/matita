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

lemma dsubst_vref_lt: ∀i,d,C. i < d → [d ⬐ C] #i = #i.
normalize /2 width=1/
qed.

lemma dsubst_vref_eq: ∀d,C. [d ⬐ C] #d = ↑[d]C.
normalize //
qed.

lemma dsubst_vref_gt: ∀i,d,C. d < i → [d ⬐ C] #i = #(i-1).
normalize /2 width=1/
qed.

theorem dsubst_lift_le: ∀h,C,M,d1,d2. d2 ≤ d1 →
                        [d2 ⬐ ↑[d1 - d2, h] C] ↑[d1 + 1, h] M = ↑[d1, h] [d2 ⬐ C] M.
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
                        [d2 ⬐ C] ↑[d1, h + 1] M = ↑[d1, h] M.
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

theorem dsubst_lift_ge: ∀h,C,M,d1,d2. d1 + h ≤ d2 →
                        [d2 ⬐ C] ↑[d1, h] M = ↑[d1, h] [d2 - h ⬐ C] M.
#h #C #M elim M -M
[ #i #d1 #d2 #Hd12 elim (lt_or_eq_or_gt i (d2-h)) #Hid2h
  [ >(dsubst_vref_lt … Hid2h) elim (lt_or_ge i d1) #Hid1
    [ lapply (lt_to_le_to_lt … (d1+h) Hid1 ?) -Hid2h // #Hid1h
      lapply (lt_to_le_to_lt … Hid1h Hd12) -Hid1h -Hd12 #Hid2
      >(lift_vref_lt … Hid1) -Hid1 /2 width=1/
    | >(lift_vref_ge … Hid1) -Hid1 -Hd12 /3 width=1/
    ]
  | destruct elim (le_inv_plus_l … Hd12) -Hd12 #Hd12 #Hhd2
    >dsubst_vref_eq >lift_vref_ge // >lift_lift_be // <plus_minus_m_m //
  | elim (le_inv_plus_l … Hd12) -Hd12 #Hd12 #_
    lapply (le_to_lt_to_lt … Hd12 Hid2h) -Hd12 #Hid1
    lapply (ltn_to_ltO … Hid2h) #Hi
    >(dsubst_vref_gt … Hid2h)
    >lift_vref_ge /2 width=1/ >lift_vref_ge /2 width=1/ -Hid1
    >dsubst_vref_gt /2 width=1/ -Hid2h >plus_minus //
  ]
| normalize #A #IHA #d1 #d2 #Hd12
  elim (le_inv_plus_l … Hd12) #_ #Hhd2
  >IHA -IHA /2 width=1/ <plus_minus //
| normalize #B #A #IHB #IHA #d1 #d2 #Hd12
  >IHB -IHB // >IHA -IHA //
]
qed.

theorem subst_subst_ge: ∀C1,C2,M,d1,d2. d1 ≤ d2 →
                        [d2 ⬐ C2] [d1 ⬐ C1] M = [d1 ⬐ [d2 - d1 ⬐ C2] C1] [d2 + 1 ⬐ C2] M.
#C1 #C2 #M elim M -M
[ #i #d1 #d2 #Hd12 elim (lt_or_eq_or_gt i d1) #Hid1
  [ lapply (lt_to_le_to_lt … Hid1 Hd12) -Hd12 #Hid2
    >(dsubst_vref_lt … Hid1) >(dsubst_vref_lt … Hid2) >dsubst_vref_lt /2 width=1/
  | destruct >dsubst_vref_eq >dsubst_vref_lt /2 width=1/
  | >(dsubst_vref_gt … Hid1) elim (lt_or_eq_or_gt i (d2+1)) #Hid2
    [ lapply (ltn_to_ltO … Hid1) #Hi
      >(dsubst_vref_lt … Hid2) >dsubst_vref_lt /2 width=1/
    | destruct /2 width=1/
    | lapply (le_to_lt_to_lt (d1+1) … Hid2) -Hid1 /2 width=1/ -Hd12 #Hid1
      >(dsubst_vref_gt … Hid2) >dsubst_vref_gt /2 width=1/
      >dsubst_vref_gt // /2 width=1/
    ]
  ]
| normalize #A #IHA #d1 #d2 #Hd12
  lapply (IHA (d1+1) (d2+1) ?) -IHA /2 width=1/
| normalize #B #A #IHB #IHA #d1 #d2 #Hd12
  >IHB -IHB // >IHA -IHA //
]
qed.

theorem subst_subst_lt: ∀C1,C2,M,d1,d2. d2 < d1 →
                        [d2 ⬐ [d1 - d2 -1 ⬐ C1] C2] [d1 ⬐ C1] M = [d1 - 1 ⬐ C1] [d2 ⬐ C2] M.
#C1 #C2 #M #d1 #d2 #Hd21
lapply (ltn_to_ltO … Hd21) #Hd1
>subst_subst_ge in ⊢ (???%); /2 width=1/ <plus_minus_m_m //
qed.

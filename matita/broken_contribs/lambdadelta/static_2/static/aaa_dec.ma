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

include "static_2/static/aaa_drops.ma".
include "static_2/static/aaa_aaa.ma".

(* ATONIC ARITY ASSIGNMENT ON TERMS *****************************************)

(* Main properties **********************************************************)

theorem aaa_dec (G) (L) (T): Decidable (∃A. ❨G,L❩ ⊢ T ⁝ A).
#G #L #T @(fqup_wf_ind_eq (Ⓣ) … G L T) -G -L -T
#G0 #L0 #T0 #IH #G #L * * [||| #p * | * ]
[ #s #HG #HL #HT destruct -IH
  /3 width=2 by aaa_sort, ex_intro, or_introl/
| #i #HG #HL #HT destruct
  elim (drops_F_uni L i) [| * * #I [| #V ] #K ] #HLK
  [1,2: -IH
    @or_intror * #A #H
    elim (aaa_inv_lref_drops … H) -H #J #Y #X #HLY #_ -G -A
    lapply (drops_mono … HLY … HLK) -L -i #H destruct
  | elim (IH G K V) -IH [3: /2 width=2 by fqup_lref/ ]
    [ * /4 width=6 by aaa_lref_drops, ex_intro, or_introl/
    | #H0 @or_intror * #A #H
      lapply (aaa_pair_inv_lref … H … HLK) -I -L -i
      /3 width=2 by ex_intro/
    ]
  ]
| #l #HG #HL #HT destruct -IH
  @or_intror * #A #H
  @(aaa_inv_gref … H)
| #V #T #HG #HL #HT destruct
  elim (IH G L V) [ * #B #HB | #HnB | // ]
  [ elim (IH G (L.ⓓV) T) [ * #A #HA | #HnA | // ] ] -IH
  [ /4 width=2 by aaa_abbr, ex_intro, or_introl/ ]
  @or_intror * #A #H
  elim (aaa_inv_abbr … H) -H #B0 #HB0 #HA0
  /3 width=2 by ex_intro/
| #W #T #HG #HL #HT destruct
  elim (IH G L W) [ * #B #HB | #HnB | // ]
  [ elim (IH G (L.ⓛW) T) [ * #A #HA | #HnA | // ] ] -IH
  [ /4 width=2 by aaa_abst, ex_intro, or_introl/ ]
  @or_intror * #A #H
  elim (aaa_inv_abst … H) -H #B0 #A0 #HB0 #HA0 #H destruct
  /3 width=2 by ex_intro/
| #V #T #HG #HL #HT destruct
  elim (IH G L V) [ * #B #HB | #HnB | // ]
  [ elim (IH G L T) [ * #X #HX | #HnX | // ] ] -IH
  [ elim (is_apear_dec B X) [ * #A #H destruct | #HnX ]
    [ /4 width=4 by aaa_appl, ex_intro, or_introl/ ]
  ]
  @or_intror * #A #H
  [ lapply (aaa_aaa_inv_appl … H HB HX) -G -L -V -T
  |*: elim (aaa_inv_appl … H) -H #B0 #HB0 #HA0
  ]
  /3 width=2 by ex_intro/
| #U #T #HG #HL #HT destruct
  elim (IH G L U) [ * #B #HB | #HnB | // ]
  [ elim (IH G L T) [ * #A #HA | #HnA | // ] ] -IH
  [ elim (eq_aarity_dec B A) [ #H destruct | #HnA ]
    [ /4 width=3 by aaa_cast, ex_intro, or_introl/ ]
  ]
  @or_intror * #X #H
  [ elim (aaa_aaa_inv_cast … H HB HA) -G -L -U -T
  |*: elim (aaa_inv_cast … H) -H #HU #HT
  ]
  /3 width=2 by ex_intro/
]
qed-.

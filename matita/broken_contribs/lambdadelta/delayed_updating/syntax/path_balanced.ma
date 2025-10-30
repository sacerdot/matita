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

include "delayed_updating/syntax/path_help.ma".
include "delayed_updating/notation/functions/subset_b_0.ma".
include "ground/subsets/subset.ma".
include "ground/generated/insert_eq_1.ma".
include "ground/xoa/ex_3_2.ma".

(* BALANCE CONDITION FOR PATH ***********************************************)

(* Note: this condition applies to a structural path *)
inductive pbc: 𝒫❨ℙ❩ ≝
| pbc_empty: pbc (𝐞)
| pbc_redex: ∀b. pbc b → pbc (𝗔◗b◖𝗟)
| pbc_after: ∀b1,b2. pbc b1 → pbc b2 → pbc (b1●b2)
.

interpretation
  "balance condition (path)"
  'SubsetB = (pbc).

(* Advanced constructions ***************************************************)

lemma pbc_dx (b1) (b2):
      b1 ϵ 𝐁 → b2 ϵ 𝐁 → b1●𝗔◗b2◖𝗟  ϵ 𝐁.
/3 width=1 by pbc_redex, pbc_after/
qed.

lemma pbc_after_redex (b):
      b ϵ 𝐁 → b◖𝗔◖𝗟 ϵ 𝐁.
/2 width=1 by pbc_dx, pbc_empty/
qed.

lemma pbc_insert_redex (p) (q):
      p●q ϵ 𝐁 → p◖𝗔◖𝗟●q ϵ 𝐁.
#p #q @(insert_eq_1 … (p●q))
#b #Hb generalize in match q; generalize in match p; -p -q
elim Hb -b
[ #p #q #H0
  elim (eq_inv_list_append_empty … H0) -H0 #H1 #H2 destruct
  /2 width=1 by pbc_dx, pbc_empty/
| #b #Hb #IH #p #q #H0
  elim (eq_inv_list_append_bi … H0) -H0 * #b0 #H1 #H2 destruct
  elim (eq_inv_list_lcons_append ????? H2) -H2 *
  [ -IH #H1 #H2 destruct <list_append_empty_dx
    /4 width=1 by pbc_empty, pbc_redex, pbc_after/
  | -IH #r #H1 #H2 destruct
    elim (eq_inv_list_empty_append ??? H2) -H2 #H1 #H2 destruct
    /3 width=1 by pbc_dx, pbc_empty/
  | -IH #H1 #H2 destruct <list_append_empty_sx
    /3 width=1 by pbc_after_redex, pbc_redex, pbc_empty/
  | -Hb #r #H1 #H2 destruct
    lapply (IH ???) -IH [ // | skip | skip ] #Hb
    /2 width=1 by pbc_dx, pbc_empty/
  ]
| #b1 #b2 #Hb1 #Hb2 #IH1 #IH2 #p #q #H0
  elim (eq_inv_list_append_bi … H0) -H0 * #b #H1 #H2 destruct
  [ >list_append_assoc -IH2 -Hb1
    /3 width=4 by pbc_after/
  | >list_append_lcons_sx >list_append_lcons_sx
    <list_append_assoc -IH1 -Hb2
    /3 width=4 by pbc_after/
  ]
]
qed.

lemma pbc_insert_pbc (b):
      b ϵ 𝐁 → ∀q,p. p●q ϵ 𝐁 → p●b●q ϵ 𝐁.
#b #H0 elim H0 -b
[ #q #p //
| #b #_ #IH #q #p #Hb
  >path_append_append_lcons <path_append_lcons_append
  /3 width=1 by pbc_insert_redex/
| #b1 #b2 #_ #_ #IH1 #IH2 #q #p #Hb
  /3 width=1 by/
]
qed.

(* Advanced inversions ******************************************************)

lemma pbc_inv_gen_dx (b):
      b ϵ 𝐁 →
      ∨∨ 𝐞 = b
       | ∃∃b1,b2. b1 ϵ 𝐁 & b2 ϵ 𝐁 & b1●𝗔◗b2◖𝗟 = b.
#b #H elim H -b
[ /2 width=1 by or_introl/
| #b #_ *
  [ #H0 destruct
    /3 width=5 by pbc_empty, ex3_2_intro, or_intror/
  | * #b1 #b2 #Hb1 #Hb2 #H0 destruct
    /5 width=5 by pbc_redex, pbc_after, ex3_2_intro, or_intror/
  ]
| #b1 #b2 #_ #_
  * [ #H1 | * #c1 #c2 #Hc1 #Hc2 #H1 ]
  * [1,3: #H2 |*: * #d1 #d2 #Hd1 #Hd2 #H2 ] destruct
  [ /2 width=1 by or_introl/
  | /3 width=5 by ex3_2_intro, or_intror/
  | /3 width=5 by ex3_2_intro, or_intror/
  | /6 width=5 by pbc_redex, pbc_after, ex3_2_intro, or_intror/
]
qed-.

lemma pbc_inv_gen_sx (b):
      b ϵ 𝐁 →
      ∨∨ 𝐞 = b
       | ∃∃b1,b2. b1 ϵ 𝐁 & b2 ϵ 𝐁 & 𝗔◗b1◖𝗟●b2 = b.
#b #H elim H -b
[ /2 width=1 by or_introl/
| #b #_ *
  [ #H0 destruct
    /3 width=5 by pbc_empty, ex3_2_intro, or_intror/
  | * #b1 #b2 #Hb1 #Hb2 #H0 destruct
    @or_intror (**) (* full auto fails *)
    @(ex3_2_intro … ((𝗔◗b1◖𝗟)●b2) (𝐞)) //
    /3 width=1 by pbc_redex, pbc_after/
  ]
| #b1 #b2 #_ #_
  * [ #H1 | * #c1 #c2 #Hc1 #Hc2 #H1 ]
  * [1,3: #H2 |*: * #d1 #d2 #Hd1 #Hd2 #H2 ] destruct
  [ /2 width=1 by or_introl/
  | /3 width=5 by ex3_2_intro, or_intror/
  | /3 width=5 by ex3_2_intro, or_intror/
  | @or_intror (**) (* full auto fails *)
    @(ex3_2_intro … c1 (c2●(𝗔◗d1◖𝗟)●d2)) //
    /4 width=1 by pbc_redex, pbc_after/
]
qed-.

lemma pbc_inv_L_sx (q):
      (𝗟◗q) ⧸ϵ 𝐁.
#q @(insert_eq_1 … (𝗟◗q))
#b #Hb generalize in match q; -q
elim Hb -b
[ #q #H0 elim (eq_inv_list_rcons_empty ??? H0)
| #b #_ #_ #q #H0
  elim (eq_inv_list_rcons_bi ????? H0) -H0 #_ #H0 destruct
| #b1 #b2 #_ #_ #IH1 #IH2 #q #H0
  elim (eq_inv_list_rcons_append ????? H0) -H0 *
  [ #H0 #_ -IH1 destruct /2 width=2 by/
  | #x #_ #H0 -IH2 destruct /2 width=2 by/
  ]
]
qed-.

lemma pbc_inv_A_dx (p):
      p◖𝗔 ⧸ϵ 𝐁.
#p @(insert_eq_1 … (p◖𝗔))
#b #Hb generalize in match p; -p
elim Hb -b
[ #p #H0 destruct
| #b #_ #_ #p <list_cons_shift #H0 destruct
| #b1 #b2 #_ #_ #IH1 #IH2 #p #H0
  elim (eq_inv_list_lcons_append ????? H0) -H0 *
  [ #_ #H0 -IH2 destruct /2 width=2 by/
  | #x #H0 #_ -IH1 destruct /2 width=2 by/
  ]
]
qed-.

lemma pbc_inv_S_sx (q):
      (𝗦◗q) ⧸ϵ 𝐁.
#q @(insert_eq_1 … (𝗦◗q))
#b #Hb generalize in match q; -q
elim Hb -b
[ #q #H0 elim (eq_inv_list_rcons_empty ??? H0)
| #b #_ #_ #q #H0
  elim (eq_inv_list_rcons_bi ????? H0) -H0 #_ #H0 destruct
| #b1 #b2 #_ #_ #IH1 #IH2 #q #H0
  elim (eq_inv_list_rcons_append ????? H0) -H0 *
  [ #H0 #_ -IH1 destruct /2 width=2 by/
  | #x #_ #H0 -IH2 destruct /2 width=2 by/
  ]
]
qed-.

lemma pbc_inv_S_dx (p):
      p◖𝗦 ⧸ϵ 𝐁.
#p @(insert_eq_1 … (p◖𝗦))
#b #Hb generalize in match p; -p
elim Hb -b
[ #p #H0 destruct
| #b #_ #_ #p <list_cons_shift #H0 destruct
| #b1 #b2 #_ #_ #IH1 #IH2 #p #H0
  elim (eq_inv_list_lcons_append ????? H0) -H0 *
  [ #_ #H0 -IH2 destruct /2 width=2 by/
  | #x #H0 #_ -IH1 destruct /2 width=2 by/
  ]
]
qed-.

lemma pbc_inv_insert_redex (p) (q):
      p◖𝗔◖𝗟●q ϵ 𝐁 → p●q ϵ 𝐁.
#p #q @(insert_eq_1 … (p◖𝗔◖𝗟●q))
#b #Hb generalize in match q; generalize in match p; -p -q
elim Hb -b
[ #p #q #H0
  elim (eq_inv_list_append_empty … H0) -H0 #_ #H0 destruct
| #b #Hb #IH #p #q #H0
  elim (eq_inv_list_lcons_append ????? (sym_eq … H0)) -H0 *
  [ #H1 #H0
    elim (eq_inv_list_lcons_bi ????? H0) -H0 #_ #H0
    elim (eq_inv_list_lcons_append ????? (sym_eq … H0)) -H0 *
    [ #_ #H0 destruct //
    | #x #H0 #_ destruct
      elim (pbc_inv_A_dx … Hb)
    ]
  | #y #H1
    >list_append_rcons_sx in ⊢ (???%→?);
    >list_append_rcons_sx in ⊢ (???%→?); #H0
    elim (eq_inv_list_rcons_append ????? H0) -H0 *
    [ #H0 #_ -IH -H1
      elim (eq_inv_list_rcons_bi ????? H0) -H0 #H0 #_ destruct
      elim (pbc_inv_L_sx … Hb)
    | #x <list_append_rcons_sx <list_append_rcons_sx #H2 #H3 destruct -Hb
      /3 width=1 by pbc_redex/
    ]
  ]
| #b1 #b2 #Hb1 #Hb2 #IH1 #IH2 #p #q #H0
  elim (eq_inv_list_append_bi … H0) -H0 * #z1
  [ -Hb1 -IH2 #H1 #H2 destruct >list_append_assoc
    /3 width=1 by pbc_after/
  | #H0 #H1
    elim (eq_inv_list_lcons_append ????? H0) -H0 *
    [ -Hb1 -IH2 #H2 #H3 destruct
      /3 width=1 by pbc_after/
    | -Hb2 -IH1 #z2 #H2 #H0
      elim (eq_inv_list_lcons_append ????? H0) -H0 *
      [ -IH2 #H3 #H4 destruct
        elim (pbc_inv_A_dx … Hb1)
      | #z3 #H3 #H4 destruct <list_append_assoc
        /3 width=1 by pbc_after/
      ]
    ]
  ]
]
qed-.

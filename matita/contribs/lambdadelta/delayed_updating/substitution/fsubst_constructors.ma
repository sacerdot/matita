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

include "delayed_updating/substitution/fsubst.ma".
include "delayed_updating/syntax/prototerm_constructors.ma".
include "ground/lib/subset_equivalence.ma".

(* FOCALIZED SUBSTITUTION ***************************************************)

(* Constructions with constructors for prototerm ****************************)

lemma fsubst_abst_hd (t) (u) (p):
      𝛌.(t[⋔p←u]) ⇔ (𝛌.t)[⋔𝗟◗p←u].
#t #u #p @conj #r
[ #Hr
  elim (in_comp_inv_abst … Hr) -Hr #s #H0 * *
  [ #q #Hq #H1 destruct
    /3 width=3 by ex2_intro, or_introl/
  | #H1s #H2s destruct
    @or_intror @conj
    [ /2 width=1 by in_comp_abst_hd/ ]
    #s0 <list_append_rcons_dx #Hs0
    elim (eq_inv_list_rcons_bi ????? Hs0) -Hs0 #H1 #H2 destruct
    /2 width=2 by/
  ]
| * *
  [ #q #Hq #H0 destruct
    /4 width=3 by in_comp_abst_hd, ex2_intro, or_introl/
  | #H1r #H2r
    elim (in_comp_inv_abst … H1r) -H1r #s #H0 #Hs destruct
    /5 width=2 by in_comp_abst_hd, conj, or_intror/
  ]
]
qed.

lemma fsubst_appl_sd (v) (t) (u) (p):
      ＠v[⋔p←u].t ⇔ (＠v.t)[⋔𝗦◗p←u].
#v #t #u #p @conj #r
[ #Hr
  elim (in_comp_inv_appl … Hr) -Hr * #s #H0
  [ * *
    [ #q #Hq #H1 destruct
      /3 width=3 by ex2_intro, or_introl/
    | #H1s #H2s destruct
      @or_intror @conj
      [ /2 width=1 by in_comp_appl_sd/ ]
      #s0 <list_append_rcons_dx #Hs0
      elim (eq_inv_list_rcons_bi ????? Hs0) -Hs0 #H1 #H2 destruct
      /2 width=2 by/
    ]
  | #Hs destruct
    @or_intror @conj [ /2 width=1 by in_comp_appl_hd/ ]
    #r <list_append_rcons_dx #H0
    elim (eq_inv_list_rcons_bi ????? H0) -H0 #H1 #H2 destruct
  ]
| * *
  [ #q #Hq #H0 destruct
    /4 width=3 by in_comp_appl_sd, ex2_intro, or_introl/
  | #H1r #H2r
    elim (in_comp_inv_appl … H1r) -H1r * #s #H0 #Hs destruct
    /5 width=2 by in_comp_appl_hd, in_comp_appl_sd, or_intror, conj/
  ]
]
qed.

lemma fsubst_appl_hd (v) (t) (u) (p):
      ＠v.(t[⋔p←u]) ⇔ (＠v.t)[⋔𝗔◗p←u].
#v #t #u #p @conj #r
[ #Hr
  elim (in_comp_inv_appl … Hr) -Hr * #s #H0
  [ #Hs destruct
    @or_intror @conj [ /2 width=1 by in_comp_appl_sd/ ]
    #r <list_append_rcons_dx #H0
    elim (eq_inv_list_rcons_bi ????? H0) -H0 #H1 #H2 destruct
  | * *
    [ #q #Hq #H1 destruct
      /3 width=3 by ex2_intro, or_introl/
    | #H1s #H2s destruct
      @or_intror @conj
      [ /2 width=1 by in_comp_appl_hd/ ]
      #s0 <list_append_rcons_dx #Hs0
      elim (eq_inv_list_rcons_bi ????? Hs0) -Hs0 #H1 #H2 destruct
      /2 width=2 by/
    ]
  ]
| * *
  [ #q #Hq #H0 destruct
    /4 width=3 by in_comp_appl_hd, ex2_intro, or_introl/
  | #H1r #H2r
    elim (in_comp_inv_appl … H1r) -H1r * #s #H0 #Hs destruct
    /5 width=2 by in_comp_appl_hd, in_comp_appl_sd, or_intror, conj/
  ]
]
qed.

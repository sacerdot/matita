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

include "static_2/syntax/sh_props.ma".

(* SORT HIERARCHY ***********************************************************)

(* strict monotonicity condition *)
record sh_lt (h): Prop ≝
{
  next_lt: ∀s. s < ⫯[h]s
}.

(* Basic properties *********************************************************)

lemma nexts_le (h): sh_lt h → ∀s,n. s ≤ (next h)^n s.
#h #Hh #s #n elim n -n [ // ] normalize #n #IH
lapply (next_lt … Hh ((next h)^n s)) #H
lapply (le_to_lt_to_lt … IH H) -IH -H /2 width=2 by lt_to_le/
qed.

lemma nexts_lt (h): sh_lt h → ∀s,n. s < (next h)^(↑n) s.
#h #Hh #s #n normalize
lapply (nexts_le … Hh s n) #H
@(le_to_lt_to_lt … H) /2 width=1 by next_lt/
qed.

lemma sh_lt_nexts_inv_lt (h): sh_lt h →
      ∀s,n1,n2. (next h)^n1 s < (next h)^n2 s → n1 < n2.
#h #Hh
@pull_2 #n1
elim n1 -n1
[ #s *
  [ #H elim (lt_refl_false … H)
  | #n2 //
  ]
| #n1 #IH #s *
  [ >iter_O #H
    elim (lt_refl_false s)
    /3 width=3 by nexts_lt, transitive_lt/
  | #n2 >iter_S >iter_S <(iter_n_Sm … (next h)) <(iter_n_Sm … (next h)) #H
    /3 width=2 by lt_S_S/
  ]
]
qed-.

lemma sh_lt_acyclic (h): sh_lt h → sh_acyclic h.
#h #Hh
@mk_sh_acyclic
@pull_2 #n1
elim n1 -n1
[ #s * [ // ] #n2 >iter_O #H
  elim (lt_refl_false s) >H in ⊢ (??%); -H
  /2 width=1 by nexts_lt/
| #n1 #IH #s *
  [ >iter_O #H -IH
    elim (lt_refl_false s) <H in ⊢ (??%); -H
    /2 width=1 by nexts_lt/
  | #n2 >iter_S >iter_S <(iter_n_Sm … (next h)) <(iter_n_Sm … (next h)) #H
    /3 width=2 by eq_f/
  ]
]
qed.

lemma sh_lt_dec (h): sh_lt h → sh_decidable h.
#h #Hh
@mk_sh_decidable #s1 #s2
elim (lt_or_ge s2 s1) #Hs
[ @or_intror * #n #H destruct
  @(lt_le_false … Hs) /2 width=1 by nexts_le/ (**) (* full auto too slow *)
| @(nat_elim_le_sn … Hs) -s1 -s2 #s1 #s2 #IH #Hs12
  elim (lt_or_eq_or_gt s2 (⫯[h]s1)) #Hs21 destruct
  [ elim (le_to_or_lt_eq … Hs12) -Hs12 #Hs12 destruct
    [ -IH @or_intror * #n #H destruct
      generalize in match Hs21; -Hs21
      <(iter_O … (next h) s1) in ⊢ (??%→?); <(iter_S … (next h)) #H
      lapply (sh_lt_nexts_inv_lt … Hh … H) -H #H
      <(le_n_O_to_eq n) in Hs12;
      /2 width=2 by lt_refl_false, le_S_S_to_le/
    | /3 width=2 by ex_intro, or_introl/
    ]
  | -IH @or_introl @(ex_intro … 1) // (**) (* auto fails *)
  | lapply (transitive_lt s1 ??? Hs21) [ /2 width=1 by next_lt/ ] -Hs12 #Hs12 
    elim (IH (s2-⫯[h]s1)) -IH
    [3: /3 width=1 by next_lt, monotonic_lt_minus_r/ ]
    >minus_minus_m_m [2,4: /2 width=1 by lt_to_le/ ] -Hs21
    [ * #n #H destruct
      @or_introl @(ex_intro … (↑n)) >iter_S >iter_n_Sm //
    | #H1 @or_intror * #n #H2 @H1 -H1 destruct
      generalize in match Hs12; -Hs12
      <(iter_O … (next h) s1) in ⊢ (?%?→?); #H
      lapply (sh_lt_nexts_inv_lt … Hh … H) -H #H
      <(S_pred … H) -H
      @(ex_intro … (↓n)) >(iter_n_Sm … (next h)) >iter_S //
    ]
  ]
]
qed-.

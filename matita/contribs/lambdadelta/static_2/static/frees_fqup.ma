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

include "static_2/s_computation/fqup_weight.ma".
include "static_2/static/lsubf_lsubr.ma".

(* CONTEXT-SENSITIVE FREE VARIABLES *****************************************)

(* Advanced properties ******************************************************)

(* Note: this replaces lemma 1400 concluding the "big tree" theorem *)
lemma frees_total: âL,T. âf. L â¢ ğ+â¨Tâ© â f.
#L #T @(fqup_wf_ind_eq (â) â¦ (â) L T) -L -T
#G0 #L0 #T0 #IH #G #L * *
[ /3 width=2 by frees_sort, ex_intro/
| cases L -L /3 width=2 by frees_atom, ex_intro/
  #L #I *
  [ cases I -I #I [2: #V ] #HG #HL #HT destruct
    [ elim (IH G L V) -IH
      /3 width=2 by frees_pair, fqu_fqup, fqu_lref_O, ex_intro/
    | -IH /3 width=2 by frees_unit, ex_intro/
    ]
  | #i #HG #HL #HT destruct
    elim (IH G L (#i)) -IH
    /3 width=2 by frees_lref, fqu_fqup, fqu_drop, ex_intro/
  ]
| /3 width=2 by frees_gref, ex_intro/
| #p #I #V #T #HG #HL #HT destruct
  elim (IH G L V) // #f1 #HV
  elim (IH G (L.â[I]V) T) -IH // #f2 #HT
  elim (pr_sor_isf_bi f1 (â«°f2))
  /3 width=6 by frees_fwd_isfin, frees_bind, pr_isf_tl, ex_intro/
| #I #V #T #HG #HL #HT destruct
  elim (IH G L V) // #f1 #HV
  elim (IH G L T) -IH // #f2 #HT
  elim (pr_sor_isf_bi f1 f2)
  /3 width=6 by frees_fwd_isfin, frees_flat, ex_intro/
]
qed-.

(* Advanced main properties *************************************************)

theorem frees_bind_void:
        âf1,L,V. L â¢ ğ+â¨Vâ© â f1 â âf2,T. L.â§ â¢ ğ+â¨Tâ© â f2 â
        âf. f1 â â«°f2 â f â âp,I. L â¢ ğ+â¨â[p,I]V.Tâ© â f.
#f1 #L #V #Hf1 #f2 #T #Hf2 #f #Hf #p #I
elim (frees_total (L.â[I]V) T) #f0 #Hf0
lapply (lsubr_lsubf â¦ Hf2 â¦ Hf0) -Hf2 /2 width=5 by lsubr_unit/ #H02
elim (pr_map_split_tl f2) * #g2 #H destruct
[ elim (lsubf_inv_push2 â¦ H02) -H02 #g0 #Z #Y #H02 #H0 #H destruct
  lapply (lsubf_inv_refl â¦ H02) -H02 #H02
  lapply (pr_sor_eq_repl_fwd_dx â¦ Hf â¦ H02) -g2 #Hf
  /2 width=5 by frees_bind/
| elim (lsubf_inv_unit2 â¦ H02) -H02 * [ #g0 #Y #_ #_ #H destruct ]
  #z1 #g0 #z #Z #Y #X #H02 #Hz1 #Hz #H0 #H destruct
  lapply (lsubf_inv_refl â¦ H02) -H02 #H02
  lapply (frees_mono â¦ Hz1 â¦ Hf1) -Hz1 #H1
  lapply (pr_sor_eq_repl_back_sn â¦ Hz â¦ H02) -g0 #Hz
  lapply (pr_sor_eq_repl_back_dx â¦ Hz â¦ H1) -z1 #Hz
  lapply (pr_sor_comm â¦ Hz) -Hz #Hz
  lapply (pr_sor_mono â¦ f Hz ?) // -Hz #H
  lapply (pr_sor_inv_sle_sn â¦ Hf) -Hf #Hf
  lapply (frees_eq_repl_back â¦ Hf0 (âf) ?) /2 width=5 by pr_eq_next/ -z #Hf0
  @(frees_bind â¦ Hf1 Hf0) -Hf1 -Hf0 (**) (* constructor needed *)
  /2 width=1 by pr_sor_sle_dx/
]
qed-.

(* Advanced inversion lemmas ************************************************)

lemma frees_inv_bind_void:
      âf,p,I,L,V,T. L â¢ ğ+â¨â[p,I]V.Tâ© â f â
      ââf1,f2. L â¢ ğ+â¨Vâ© â f1 & L.â§ â¢ ğ+â¨Tâ© â f2 & f1 â â«°f2 â f.
#f #p #I #L #V #T #H
elim (frees_inv_bind â¦ H) -H #f1 #f2 #Hf1 #Hf2 #Hf
elim (frees_total (L.â§) T) #f0 #Hf0
lapply (lsubr_lsubf â¦ Hf0 â¦ Hf2) -Hf2 /2 width=5 by lsubr_unit/ #H20
elim (pr_map_split_tl f0) * #g0 #H destruct
[ elim (lsubf_inv_push2 â¦ H20) -H20 #g2 #I #Y #H20 #H2 #H destruct
  lapply (lsubf_inv_refl â¦ H20) -H20 #H20
  lapply (pr_sor_eq_repl_back_dx â¦ Hf â¦ H20) -g2 #Hf
  /2 width=5 by ex3_2_intro/
| elim (lsubf_inv_unit2 â¦ H20) -H20 * [ #g2 #Y #_ #_ #H destruct ]
  #z1 #z0 #g2 #Z #Y #X #H20 #Hz1 #Hg2 #H2 #H destruct
  lapply (lsubf_inv_refl â¦ H20) -H20 #H0
  lapply (frees_mono â¦ Hz1 â¦ Hf1) -Hz1 #H1
  lapply (pr_sor_eq_repl_back_sn â¦ Hg2 â¦ H0) -z0 #Hg2
  lapply (pr_sor_eq_repl_back_dx â¦ Hg2 â¦ H1) -z1 #Hg2
  @(ex3_2_intro â¦ Hf1 Hf0) -Hf1 -Hf0 (**) (* constructor needed *)
  /2 width=3 by pr_sor_comm_23_idem/
]
qed-.

lemma frees_ind_void (Q:relation3 â¦):
      (
        âf,L,s. ğâ¨fâ© â  Q L (âs) f
      ) â (
        âf,i. ğâ¨fâ© â  Q (â) (#i) (â«¯*[i]âf)
      ) â (
        âf,I,L,V.
        L â¢ ğ+â¨Vâ© â f â  Q L V fâ Q (L.â[I]V) (#O) (âf)
      ) â (
        âf,I,L. ğâ¨fâ© â  Q (L.â¤[I]) (#O) (âf)
      ) â (
        âf,I,L,i.
        L â¢ ğ+â¨#iâ© â f â  Q L (#i) f â Q (L.â[I]) (#(âi)) (â«¯f)
      ) â (
        âf,L,l. ğâ¨fâ© â  Q L (Â§l) f
      ) â (
        âf1,f2,f,p,I,L,V,T.
        L â¢ ğ+â¨Vâ© â f1 â L.â§ â¢ğ+â¨Tâ©â f2 â f1 â â«°f2 â f â
        Q L V f1 â Q (L.â§) T f2 â Q L (â[p,I]V.T) f
      ) â (
        âf1,f2,f,I,L,V,T.
        L â¢ ğ+â¨Vâ© â f1 â L â¢ğ+â¨Tâ© â f2 â f1 â f2 â f â
        Q L V f1 â Q L T f2 â Q L (â[I]V.T) f
      ) â
      âL,T,f. L â¢ ğ+â¨Tâ© â f â  Q L T f.
#Q #IH1 #IH2 #IH3 #IH4 #IH5 #IH6 #IH7 #IH8 #L #T
@(fqup_wf_ind_eq (â») â¦ (â) L T) -L -T #G0 #L0 #T0 #IH #G #L * *
[ #s #HG #HL #HT #f #H destruct -IH
  lapply (frees_inv_sort â¦ H) -H /2 width=1 by/
| cases L -L
  [ #i #HG #HL #HT #f #H destruct -IH
    elim (frees_inv_atom â¦ H) -H #g #Hg #H destruct /2 width=1 by/
  | #L #I * [ cases I -I #I [ | #V ] | #i ] #HG #HL #HT #f #H destruct
    [ elim (frees_inv_unit â¦ H) -H #g #Hg #H destruct /2 width=1 by/
    | elim (frees_inv_pair â¦ H) -H #g #Hg #H destruct
      /4 width=2 by fqu_fqup, fqu_lref_O/
    | elim (frees_inv_lref â¦ H) -H #g #Hg #H destruct
      /4 width=2 by fqu_fqup/
    ]
  ]
| #l #HG #HL #HT #f #H destruct -IH
  lapply (frees_inv_gref â¦ H) -H /2 width=1 by/
| #p #I #V #T #HG #HL #HT #f #H destruct
  elim (frees_inv_bind_void â¦ H) -H /3 width=7 by/
| #I #V #T #HG #HL #HT #f #H destruct
  elim (frees_inv_flat â¦ H) -H /3 width=7 by/
]
qed-.

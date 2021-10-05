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

include "static_2/static/frees_frees.ma".
include "static_2/static/lsubf.ma".

(* RESTRICTED REFINEMENT FOR CONTEXT-SENSITIVE FREE VARIABLES ***************)

(* Main properties **********************************************************)

theorem lsubf_sor:
        ∀K,L,g1,f1. ❪K,g1❫ ⫃𝐅+ ❪L,f1❫ →
        ∀g2,f2. ❪K,g2❫ ⫃𝐅+ ❪L,f2❫ →
        ∀g. g1 ⋓ g2 ≘ g → ∀f. f1 ⋓ f2 ≘ f → ❪K,g❫ ⫃𝐅+ ❪L,f❫.
#K elim K -K
[ #L #g1 #f1 #H1 #g2 #f2 #H2 #g #Hg #f #Hf
  elim (lsubf_inv_atom1 … H1) -H1 #H1 #H destruct
  lapply (lsubf_inv_atom … H2) -H2 #H2
  /5 width=4 by lsubf_atom, pr_sor_mono, pr_sor_eq_repl_back_dx, pr_sor_eq_repl_back_sn/
| #K #J #IH #L #g1 #f1 #H1 #g2 #f2 #H2 #g #Hg #f #Hf
  elim (pr_map_split_tl g1) * #y1 #H destruct
  elim (pr_map_split_tl g2) * #y2 #H destruct
  [ elim (pr_sor_inv_push_bi … Hg) -Hg [|*: // ] #y #Hy #H destruct
    elim (lsubf_inv_push1 … H1) -H1 #x1 #Z1 #Y1 #H1 #H #H0 destruct
    elim (lsubf_inv_push_sn … H2) -H2 #x2 #H2 #H destruct
    elim (pr_sor_inv_push_bi … Hf) -Hf [|*: // ] #x #Hx #H destruct
    /3 width=8 by lsubf_push/
  | elim (pr_sor_inv_push_next … Hg) -Hg [|*: // ] #y #Hy #H destruct
    elim (lsubf_inv_push1 … H1) -H1 #x1 #Z1 #Y1 #H1 #H #H0 destruct
    generalize in match H2; -H2 cases J -J #J [| #V ] #H2
    [ elim (lsubf_inv_unit1 … H2) -H2 #x2 #Y2 #H2 #H #H0 destruct
    | elim (lsubf_inv_pair1 … H2) -H2 *
      [ #x2 #Z2 #H2 #H #H0 destruct
      | #y3 #y4 #x2 #Y2 #W #U #H2 #Hy3 #Hy2 #H #H0 #H3 #H4 destruct
      | #y3 #y4 #x2 #Z2 #Y2 #H2 #Hy3 #Hy2 #H #H0 destruct
      ]
    ]
    elim (pr_sor_inv_push_next … Hf) -Hf [1,6,11,16:|*: // ] #x #Hx #H destruct
    /3 width=12 by lsubf_unit, lsubf_beta, lsubf_bind, pr_sor_assoc_sn/
  | elim (pr_sor_inv_next_push … Hg) -Hg [|*: // ] #y #Hy #H destruct
    elim (lsubf_inv_push1 … H2) -H2 #x2 #Z2 #Y2 #H2 #H #H0 destruct
    generalize in match H1; -H1 cases J -J #J [| #V ] #H1
    [ elim (lsubf_inv_unit1 … H1) -H1 #x1 #Y1 #H1 #H #H0 destruct
    | elim (lsubf_inv_pair1 … H1) -H1 *
      [ #x1 #Z1 #H1 #H #H0 destruct
      | #y3 #y4 #x1 #Y1 #W #U #H1 #Hy3 #Hy1 #H #H0 #H3 #H4 destruct
      | #y3 #y4 #x1 #Z1 #Y1 #H1 #Hy3 #Hy1 #H #H0 destruct
      ]
    ]
    elim (pr_sor_inv_next_push … Hf) -Hf [1,6,11,16:|*: // ] #x #Hx #H destruct
    /3 width=12 by lsubf_unit, lsubf_beta, lsubf_bind, pr_sor_comm_23/
  | elim (pr_sor_inv_next_bi … Hg) -Hg [|*: // ] #y #Hy #H destruct
    generalize in match H2; generalize in match H1; -H1 -H2 cases J -J #J [| #V ] #H1 #H2
    [ elim (lsubf_inv_unit1 … H1) -H1 #x1 #Y1 #H1 #H #H0 destruct
      elim (lsubf_inv_bind_sn … H2) -H2 #x2 #H2 #H destruct
    | elim (lsubf_inv_pair1 … H1) -H1 *
      [ #x1 #Z1 #H1 #H #H0 destruct
        elim (lsubf_inv_bind_sn … H2) -H2 #x2 #H2 #H destruct
      | #y3 #y4 #x1 #Y1 #W #U #H1 #Hy3 #Hy1 #H #H0 #H3 #H4 destruct
        elim (lsubf_inv_beta_sn … H2) -H2 #z3 #z4 #x2 #H2 #Hz3 #Hy2 #H destruct
        lapply (frees_mono … Hz3 … Hy3) -Hz3 #H3
        lapply (pr_sor_eq_repl_back_dx … Hy2 … H3) -z3 #Hy2
      | #y3 #y4 #x1 #Z1 #Y1 #H1 #Hy3 #Hy1 #H #H0 destruct
        elim (lsubf_inv_unit_sn … H2) -H2 #z3 #z4 #x2 #H2 #Hz3 #Hy2 #H destruct
        lapply (frees_mono … Hz3 … Hy3) -Hz3 #H3
        lapply (pr_sor_eq_repl_back_dx … Hy2 … H3) -z3 #Hy2
      ]
    ]
    elim (pr_sor_inv_next_bi … Hf) -Hf [1,6,11,16:|*: // ] #x #Hx #H destruct
    /3 width=12 by lsubf_unit, lsubf_beta, lsubf_bind, pr_sor_coll_dx/
  ]
]
qed-.

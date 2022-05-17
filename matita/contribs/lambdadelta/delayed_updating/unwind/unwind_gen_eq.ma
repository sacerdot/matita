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

include "delayed_updating/unwind/unwind_gen.ma".
include "ground/relocation/tr_pap_eq.ma".

(* GENERIC UNWIND FOR PATH **************************************************)

(* Constructions with stream_eq *********************************************)

lemma unwind_gen_eq_repl (p) (f1) (f2):
      (∀n. f1 n ≗ f2 n) → ◆[f1]p = ◆[f2]p.
#p @(path_ind_unwind … p) -p // [ #n | #n #l #p |*: #p ] #IH #f1 #f2 #Hf
[ <unwind_gen_d_empty <unwind_gen_d_empty
  <(tr_pap_eq_repl … (Hf n)) -f2 -IH //
| <unwind_gen_d_lcons <unwind_gen_d_lcons
  <(IH … Hf) -f2 -IH //
| <unwind_gen_m_sn <unwind_gen_m_sn
  <(IH … Hf) -f2 -IH //
| <unwind_gen_L_sn <unwind_gen_L_sn
  <(IH … Hf) -f2 -IH //
| <unwind_gen_A_sn <unwind_gen_A_sn
  <(IH … Hf) -f2 -IH //
| <unwind_gen_S_sn <unwind_gen_S_sn
  <(IH … Hf) -f2 -IH //
]
qed-.

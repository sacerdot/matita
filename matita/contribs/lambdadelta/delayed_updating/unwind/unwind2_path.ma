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
include "delayed_updating/unwind/unwind2_rmap.ma".
include "delayed_updating/syntax/path_reverse.ma".
include "delayed_updating/notation/functions/black_downtriangle_2.ma".
include "ground/lib/list_tl.ma".

(* UNWIND FOR PATH **********************************************************)

definition unwind2_path (f) (p): path ≝
           ◆[▶[f]⇂(pᴿ)]p
.

interpretation
  "unwind (path)"
  'BlackDownTriangle f p = (unwind2_path f p).

(* Basic constructions ******************************************************)

lemma unwind2_path_unfold (f) (p):
      ◆[▶[f]⇂(pᴿ)]p = ▼[f]p.
// qed.

lemma unwind2_path_empty (f):
      (𝐞) = ▼[f]𝐞.
// qed.

lemma unwind2_path_d_empty (f) (n):
      (𝗱(f＠⧣❨n❩)◗𝐞) = ▼[f](𝗱n◗𝐞).
// qed.

lemma unwind2_path_d_lcons (f) (p) (l) (n:pnat):
      ▼[f∘𝐮❨n❩](l◗p) = ▼[f](𝗱n◗l◗p).
#f #p #l #n <unwind2_path_unfold <unwind2_path_unfold
<unwind_gen_d_lcons <reverse_lcons
@(list_ind_rcons … p) -p // #p #l0 #_
<reverse_rcons <reverse_lcons <reverse_lcons <reverse_rcons
<list_tl_lcons <list_tl_lcons //
qed.

lemma unwind2_path_m_sn (f) (p):
      ▼[f]p = ▼[f](𝗺◗p).
#f #p <unwind2_path_unfold <unwind2_path_unfold
<unwind_gen_m_sn <reverse_lcons
@(list_ind_rcons … p) -p // #p #l #_
<reverse_rcons <list_tl_lcons <list_tl_lcons //
qed.

lemma unwind2_path_L_sn (f) (p):
      (𝗟◗▼[⫯f]p) = ▼[f](𝗟◗p).
#f #p <unwind2_path_unfold <unwind2_path_unfold
<unwind_gen_L_sn <reverse_lcons
@(list_ind_rcons … p) -p // #p #l #_
<reverse_rcons <list_tl_lcons <list_tl_lcons //
qed.

lemma unwind2_path_A_sn (f) (p):
      (𝗔◗▼[f]p) = ▼[f](𝗔◗p).
#f #p <unwind2_path_unfold <unwind2_path_unfold
<unwind_gen_A_sn <reverse_lcons
@(list_ind_rcons … p) -p // #p #l #_
<reverse_rcons <list_tl_lcons <list_tl_lcons //
qed.

lemma unwind2_path_S_sn (f) (p):
      (𝗦◗▼[f]p) = ▼[f](𝗦◗p).
#f #p <unwind2_path_unfold <unwind2_path_unfold
<unwind_gen_S_sn <reverse_lcons
@(list_ind_rcons … p) -p // #p #l #_
<reverse_rcons <list_tl_lcons <list_tl_lcons //
qed.

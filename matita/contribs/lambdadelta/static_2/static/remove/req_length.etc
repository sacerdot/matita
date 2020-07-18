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

include "static_2/static/rex_length.ma".
include "static_2/static/rex_fsle.ma".
include "static_2/static/req.ma".

(* SYNTACTIC EQUIVALENCE FOR LOCAL ENVIRONMENTS ON REFERRED ENTRIES *********)

(* Advanved properties with free variables inclusion ************************)

lemma req_fsge_comp:
      rex_fsge_compatible ceq.
#L1 #L2 #T #H elim H #f1 #Hf1 #HL12
lapply (frees_req_conf … Hf1 … H) -H
lapply (sex_fwd_length … HL12)
/3 width=8 by lveq_length_eq, ex4_4_intro/ (**) (* full auto fails *)
qed-.

(* Advanced properties ******************************************************)

(* Basic_2A1: uses: lleq_sym *)
lemma req_sym (T):
      symmetric … (req T).
/3 width=1 by req_fsge_comp, rex_sym/ qed-.

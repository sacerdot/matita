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

set "baseuri" "cic:/matita/LOGIC/Track/props".

include "Insert/props.ma".
include "Track/inv.ma".

theorem track_weak: \forall R,p,P,Q,S,i. 
                    Track P p S \to Insert R i P Q \to 
                    \exists q. Track Q q S.
 intros 2. elim p; clear p;
 [ lapply linear track_inv_lref to H as H0; decompose;
   lapply linear insert_trans to H, H1; decompose; autobatch
 | lapply linear track_inv_parx to H. subst. autobatch
 | lapply linear track_inv_impw to H1. decompose. subst.
   lapply linear H to H4, H2. decompose. autobatch
 | lapply linear track_inv_impi to H1. decompose. subst.
   lapply linear H to H4, H2. decompose. autobatch
 | lapply linear track_inv_impe to H1. decompose. subst.
   lapply linear insert_conf to H2, H4. decompose.
   lapply linear H to H5, H3. decompose. autobatch
 ]
qed.

theorem track_comp: \forall R,q,p,P,Q,S,i. 
                    Track P p R \to Track Q q S \to Insert R i P Q \to
                    \exists r. Track P r S.
 intros 2. elim q; clear q;
 [ lapply linear track_inv_lref to H1 as H0; decompose;
   lapply linear insert_conf_rev_full to H1,H2; decompose; subst; autobatch
 | lapply linear track_inv_parx to H1. subst. autobatch
 | lapply linear track_inv_impw to H2. decompose. subst.
   lapply linear H to H1, H5, H3. decompose. autobatch
 | lapply linear track_inv_impi to H2. decompose. subst.
   lapply linear H to H1, H5, H3. decompose. autobatch
 | lapply linear track_inv_impe to H2. decompose. subst.
   lapply linear insert_trans to H3, H5. decompose.
   lapply track_weak to H1, H3. clear H1. decompose.
   lapply linear H to H1, H6, H4. decompose. autobatch
 ].
qed.

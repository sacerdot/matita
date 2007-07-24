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

set "baseuri" "cic:/matita/LOGIC/Track/order".

include "Track/props.ma".

(* Order properties *********************************************************)

theorem track_refl: \forall P. \forall c:Formula. \exists r. 
                    Track P r (pair c c).
 intros. elim c; clear c;
 [ autobatch
 | lapply (insert_total (pair f f1) zero P); [2:autobatch];
   decompose. autobatch depth = 5 
 ].
qed.

theorem track_trans: \forall p,q,A,B. \forall c:Formula.
                     Track leaf p (pair A c) \to Track leaf q (pair c B) \to
                     \exists r. Track leaf r (pair A B).
 intros 1; elim p names 0; clear p;
 [ intros. clear H1.
   lapply linear track_inv_lref to H. decompose.
   lapply insert_inv_leaf_2 to H. decompose
 | intros.
   lapply linear track_inv_parx to H. subst. autobatch.
 | intros.
   lapply linear track_inv_impw to H1.
   decompose. subst.
   lapply linear H to H4, H2. decompose. autobatch
 | intros 3. elim q; clear q;
   [ clear H H1.
     lapply linear track_inv_lref to H2. decompose.
     lapply insert_inv_leaf_2 to H. decompose
   | lapply linear track_inv_parx to H2. subst. autobatch
   | clear H H1.
     lapply linear track_inv_impi to H2.
     lapply linear track_inv_impw to H3.
     decompose. subst. autobatch
   | clear H H1 H2.
     lapply linear track_inv_impi to H3.
     decompose. subst
   | clear H H1.
     lapply linear track_inv_impi to H2.
     lapply linear track_inv_impe to H3.
     decompose. subst. autobatch
   ]
 | intros 3. elim q; clear q;
   [ clear H H1.
     lapply linear track_inv_lref to H2. decompose.
     lapply insert_inv_leaf_2 to H. decompose 
   | clear H.
     lapply linear track_inv_parx to H2.
     subst. autobatch
   | clear H H1.
     lapply linear track_inv_impe to H2.
     lapply linear track_inv_impw to H3.
     decompose. subst. autobatch
   | clear H H1 H2.
     lapply linear track_inv_impi to H3. decompose. subst
   | clear H H1.
     lapply linear track_inv_impe to H2.
     lapply linear track_inv_impe to H3.
     decompose. subst.
     lapply linear track_inv_lleaf_impl to H5. decompose; subst;
     [ clear H4 H6.
       lapply linear insert_inv_leaf_1 to H3. decompose. subst.
       lapply linear insert_inv_abst_2 to H2. decompose. subst
     | lapply insert_conf to H3, H4. clear H4. decompose.
       lapply linear track_weak to H6, H4. decompose.
       lapply linear track_comp to H2, H, H1. decompose. autobatch
     ]
   ]
 ].
qed.    
(*   
   | lapply linear track_inv_impi to H4.
     lapply linear track_inv_impe to H5.
     decompose. subst.
     destruct H4. destruct H5. clear H4 H5. subst.
     unfold linj in Hcut. unfold rinj in Hcut3. destruct Hcut. destruct Hcut3. clear Hcut Hcut3. subst.
     destruct Hcut2. clear Hcut2. subst.
*)

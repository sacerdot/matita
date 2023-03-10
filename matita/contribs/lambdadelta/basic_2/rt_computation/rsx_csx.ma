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

include "basic_2/rt_computation/csx_lsubr.ma".
include "basic_2/rt_computation/csx_cpxs.ma".
include "basic_2/rt_computation/jsx_rsx.ma".

(* STRONGLY NORMALIZING REFERRED LOCAL ENVS FOR EXTENDED RT-TRANSITION ******)

(* Forward lemmas with strongly rt-normalizing terms ************************)

fact rsx_fwd_lref_pair_csx_aux (G):
     âL. G â¢ â¬*ğ[#0] L â
     âI,K,V. L = K.â[I]V â â¨G,Kâ© â¢ â¬*ğ V.
#G #L #H
@(rsx_ind â¦ H) -L #L #_ #IH #I #K #V1 #H destruct
@csx_intro #V2 #HV12 #HnV12
@(IH â¦ I) -IH [1,4: // | -HnV12 | -G #H ]
[ /2 width=1 by lpx_pair/
| elim (reqg_inv_zero_pair_sn â¦ H) -H #Y #X #_ #H1 #H2 destruct -I
  /2 width=1 by/
]
qed-.

lemma rsx_fwd_lref_pair_csx (G):
      âI,K,V. G â¢ â¬*ğ[#0] K.â[I]V â â¨G,Kâ© â¢ â¬*ğ V.
/2 width=4 by rsx_fwd_lref_pair_csx_aux/ qed-.

lemma rsx_fwd_lref_pair_csx_drops (G):
      âI,K,V,i,L. â©[i] L â K.â[I]V â G â¢ â¬*ğ[#i] L â â¨G,Kâ© â¢ â¬*ğ V.
#G #I #K #V #i elim i -i
[ #L #H >(drops_fwd_isid â¦ H) -H
  /2 width=2 by rsx_fwd_lref_pair_csx/
| #i #IH #L #H1 #H2
  elim (drops_inv_bind2_isuni_next â¦ H1) -H1 // #J #Y #HY #H destruct
  lapply (rsx_inv_lifts â¦ H2 â¦ (ğâ¨1â©) ?????) -H2
  /3 width=6 by drops_refl, drops_drop/
]
qed-.

(* Inversion lemmas with strongly rt-normalizing terms **********************)

lemma rsx_inv_lref_pair (G):
      âI,K,V. G â¢ â¬*ğ[#0] K.â[I]V â
      â§â§ â¨G,Kâ© â¢ â¬*ğ V & G â¢ â¬*ğ[V] K.
/3 width=2 by rsx_fwd_lref_pair_csx, rsx_fwd_pair, conj/ qed-.

lemma rsx_inv_lref_pair_drops (G):
      âI,K,V,i,L. â©[i] L â K.â[I]V â G â¢ â¬*ğ[#i] L â
      â§â§ â¨G,Kâ© â¢ â¬*ğ V & G â¢ â¬*ğ[V] K.
/3 width=5 by rsx_fwd_lref_pair_csx_drops, rsx_fwd_lref_pair_drops, conj/ qed-.

lemma rsx_inv_lref_drops (G):
      âL,i. G â¢ â¬*ğ[#i] L â
      â¨â¨ â©*[â»,ğâ¨iâ©] L â â
       | ââI,K. â©[i] L â K.â¤[I]
       | ââI,K,V. â©[i] L â K.â[I]V & â¨G,Kâ© â¢ â¬*ğ V & G â¢ â¬*ğ[V] K.
#G #L #i #H elim (drops_F_uni L i)
[ /2 width=1 by or3_intro0/
| * * /4 width=10 by rsx_fwd_lref_pair_csx_drops, rsx_fwd_lref_pair_drops, ex3_3_intro, ex1_2_intro, or3_intro2, or3_intro1/
]
qed-.

(* Properties with strongly rt-normalizing terms ****************************)

(* Note: swapping the eliminations to avoid rsx_cpx_trans: no solution found *)
(* Basic_2A1: uses: lsx_lref_be_lpxs *)
lemma rsx_lref_pair_lpxs (G):
      âK1,V. â¨G,K1â© â¢ â¬*ğ V â
      âK2. G â¢ â¬*ğ[V] K2 â â¨G,K1â© â¢ â¬* K2 â
      âI. G â¢ â¬*ğ[#0] K2.â[I]V.
#G #K1 #V #H
@(csx_ind_cpxs â¦ H) -V #V0 #_ #IHV0 #K2 #H
@(rsx_ind â¦ H) -K2 #K0 #HK0 #IHK0 #HK10 #I
@rsx_intro #Y #HY #HnY
elim (lpx_inv_pair_sn â¦ HY) -HY #K2 #V2 #HK02 #HV02 #H destruct
elim (teqx_dec V0 V2) #HnV02 destruct [ -IHV0 -HV02 -HK0 | -IHK0 -HnY ]
[ /5 width=5 by rsx_reqx_trans, lpxs_step_dx, reqg_pair, reqg_refl/
| @(IHV0 â¦ HnV02) -IHV0 -HnV02
  [ /2 width=3 by lpxs_cpx_trans/
  | /3 width=3 by rsx_lpx_trans, rsx_cpx_trans/
  | /2 width=3 by lpxs_step_dx/
  ]
]
qed.

lemma rsx_lref_pair (G):
      âK,V. â¨G,Kâ© â¢ â¬*ğ V â G â¢ â¬*ğ[V] K â âI. G â¢ â¬*ğ[#0] K.â[I]V.
/2 width=3 by rsx_lref_pair_lpxs/ qed.

(* Basic_2A1: uses: lsx_lref_be *)
lemma rsx_lref_pair_drops (G):
      âK,V. â¨G,Kâ© â¢ â¬*ğ V â G â¢ â¬*ğ[V] K â
      âI,i,L. â©[i] L â K.â[I]V â G â¢ â¬*ğ[#i] L.
#G #K #V #HV #HK #I #i elim i -i
[ #L #H >(drops_fwd_isid â¦ H) -H /2 width=1 by rsx_lref_pair/
| #i #IH #L #H
  elim (drops_inv_bind2_isuni_next â¦ H) -H // #J #Y #HY #H destruct
  @(rsx_lifts â¦ (ğâ¨1â©)) /3 width=6 by drops_refl, drops_drop/ (**) (* full auto fails *)
]
qed.

(* Main properties with strongly rt-normalizing terms ***********************)

(* Basic_2A1: uses: csx_lsx *)
theorem csx_rsx (G):
        âL,T. â¨G,Lâ© â¢ â¬*ğ T â G â¢ â¬*ğ[T] L.
#G #L #T @(fqup_wf_ind_eq (â) â¦ G L T) -G -L -T
#Z #Y #X #IH #G #L * *
[ //
| #i #HG #HL #HT #H destruct
  elim (csx_inv_lref_drops â¦ H) -H [ |*: * ]
  [ /2 width=1 by rsx_lref_atom_drops/
  | /2 width=3 by rsx_lref_unit_drops/
  | /4 width=6 by rsx_lref_pair_drops, fqup_lref/
  ]
| //
| #p #I #V #T #HG #HL #HT #H destruct
  elim (csx_fwd_bind â¦ H) -H /3 width=1 by rsx_bind/
| #I #V #T #HG #HL #HT #H destruct
  elim (csx_fwd_flat â¦ H) -H /3 width=1 by rsx_flat/
]
qed.

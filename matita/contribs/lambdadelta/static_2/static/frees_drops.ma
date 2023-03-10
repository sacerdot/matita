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

include "ground/relocation/nstream_coafter.ma".
include "static_2/relocation/drops_drops.ma".
include "static_2/static/frees_fqup.ma".

(* CONTEXT-SENSITIVE FREE VARIABLES *****************************************)

(* Advanced properties ******************************************************)

lemma frees_atom_drops:
      āb,L,i. ā©*[b,šāØiā©] L ā ā ā
      āf. šāØfā© ā L ā¢ š+āØ#iā© ā ā«Æ*[i]āf.
#b #L elim L -L /2 width=1 by frees_atom/
#L #I #IH *
[ #H lapply (drops_fwd_isid ā¦ H ?) -H // #H destruct
| /4 width=3 by frees_lref, drops_inv_drop1/
]
qed.

lemma frees_pair_drops:
      āf,K,V. K ā¢ š+āØVā© ā f ā
      āi,I,L. ā©[i] L ā K.ā[I]V ā L ā¢ š+āØ#iā© ā ā«Æ*[i] āf.
#f #K #V #Hf #i elim i -i
[ #I #L #H lapply (drops_fwd_isid ā¦ H ?) -H /2 width=1 by frees_pair/
| #i #IH #I #L #H elim (drops_inv_succ ā¦ H) -H /3 width=2 by frees_lref/
]
qed.

lemma frees_unit_drops:
      āf.  šāØfā© ā āI,K,i,L. ā©[i] L ā K.ā¤[I] ā
      L ā¢ š+āØ#iā© ā ā«Æ*[i] āf.
#f #Hf #I #K #i elim i -i
[ #L #H lapply (drops_fwd_isid ā¦ H ?) -H /2 width=1 by frees_unit/
| #i #IH #Y #H elim (drops_inv_succ ā¦ H) -H
  #J #L #HLK #H destruct /3 width=1 by frees_lref/
]
qed.

lemma frees_lref_pushs:
      āf,K,j. K ā¢ š+āØ#jā© ā f ā
      āi,L. ā©[i] L ā K ā L ā¢ š+āØ#(i+j)ā© ā ā«Æ*[i] f.
#f #K #j #Hf #i elim i -i
[ #L #H lapply (drops_fwd_isid ā¦ H ?) -H //
| #i #IH #L #H elim (drops_inv_succ ā¦ H) -H
  #I #Y #HYK #H destruct /3 width=1 by frees_lref/
]
qed.

(* Advanced inversion lemmas ************************************************)

lemma frees_inv_lref_drops:
      āL,i,f. L ā¢ š+āØ#iā© ā f ā
      āØāØ āāg. ā©*[ā»,šāØiā©] L ā ā & šāØgā© & f = ā«Æ*[i] āg
       | āāg,I,K,V. K ā¢ š+āØVā© ā g & ā©[i] L ā K.ā[I]V & f = ā«Æ*[i] āg
       | āāg,I,K. ā©[i] L ā K.ā¤[I] & šāØgā© & f = ā«Æ*[i] āg.
#L elim L -L
[ #i #g | #L #I #IH * [ #g cases I -I [ #I | #I #V ] -IH | #i #g ] ] #H
[ elim (frees_inv_atom ā¦ H) -H #f #Hf #H destruct
  /3 width=3 by or3_intro0, ex3_intro/
| elim (frees_inv_unit ā¦ H) -H #f #Hf #H destruct
  /4 width=3 by drops_refl, or3_intro2, ex3_3_intro/
| elim (frees_inv_pair ā¦ H) -H #f #Hf #H destruct
  /4 width=7 by drops_refl, or3_intro1, ex3_4_intro/
| elim (frees_inv_lref ā¦ H) -H #f #Hf #H destruct
  elim (IH ā¦ Hf) -IH -Hf *
  [ /4 width=3 by drops_drop, or3_intro0, ex3_intro/
  | /4 width=7 by drops_drop, or3_intro1, ex3_4_intro/
  | /4 width=3 by drops_drop, or3_intro2, ex3_3_intro/
  ]
]
qed-.

(* Properties with generic slicing for local environments *******************)

lemma frees_lifts:
      āb,f1,K,T. K ā¢ š+āØTā© ā f1 ā
      āf,L. ā©*[b,f] L ā K ā āU. ā§*[f] T ā U ā
      āf2. f ~ā f1 ā f2 ā L ā¢ š+āØUā© ā f2.
#b #f1 #K #T #H lapply (frees_fwd_isfin ā¦ H) elim H -f1 -K -T
[ #f1 #K #s #Hf1 #_ #f #L #HLK #U #H2 #f2 #H3
  lapply (pr_coafter_isi_inv_dx ā¦ H3 ā¦ Hf1) -f1 #Hf2
  >(lifts_inv_sort1 ā¦ H2) -U /2 width=1 by frees_sort/
| #f1 #i #Hf1 #_ #f #L #H1 #U #H2 #f2 #H3
  elim (lifts_inv_lref1 ā¦ H2) -H2 #j #Hij #H destruct
  elim (coafter_fwd_xnx_pushs ā¦ Hij H3) -H3 #g2 #Hg2 #H2 destruct
  lapply (pr_coafter_isi_inv_dx ā¦ Hg2 ā¦ Hf1) -f1 #Hf2
  elim (drops_inv_atom2 ā¦ H1) -H1 #n #g #H1 #Hf
  elim (pr_after_pat_des ā¦ Hij ā¦ Hf) -f #x #_ #Hj -g -i
  lapply (pr_pat_inv_uni ā¦ Hj) -Hj #H destruct
  /3 width=8 by frees_atom_drops, drops_trans/
| #f1 #I #K #V #_ #IH #Hf1 #f #L #H1 #U #H2 #f2 #H3
  lapply (pr_isf_inv_next ā¦ Hf1 ??) -Hf1 [3: |*: // ] #Hf1
  lapply (lifts_inv_lref1 ā¦ H2) -H2 * #j #Hf #H destruct
  elim (drops_split_trans_bind2 ā¦ H1) -H1 [ |*: // ] #Z #Y #HLY #HYK #H
  elim (liftsb_inv_pair_sn ā¦ H) -H #W #HVW #H destruct
  elim (coafter_fwd_xnx_pushs ā¦ Hf H3) -H3 #g2 #H3 #H2 destruct
  lapply (IH ā¦ HYK ā¦ HVW ā¦ H3) -IH -H3 -HYK -HVW //
  /2 width=5 by frees_pair_drops/
| #f1 #I #K #Hf1 #_ #f #L #H1 #U #H2 #f2 #H3
  lapply (lifts_inv_lref1 ā¦ H2) -H2 * #j #Hf #H destruct
  elim (coafter_fwd_xnx_pushs ā¦ Hf H3) -H3 #g2 #H3 #H2 destruct
  lapply (pr_coafter_isi_inv_dx ā¦ H3 ā¦ Hf1) -f1 #Hg2
  elim (drops_split_trans_bind2 ā¦ H1 ā¦ Hf) -H1 -Hf #Z #Y #HLY #_ #H
  lapply (liftsb_inv_unit_sn ā¦ H) -H #H destruct
  /2 width=3 by frees_unit_drops/
| #f1 #I #K #i #_ #IH #Hf1 #f #L #H1 #U #H2 #f2 #H3
  lapply (pr_isf_inv_push ā¦ Hf1 ??) -Hf1 [3: |*: // ] #Hf1
  lapply (lifts_inv_lref1 ā¦ H2) -H2 * #x #Hf #H destruct
  elim (pr_pat_inv_succ_sn ā¦ Hf) -Hf [ |*: // ] #j #Hf #H destruct
  elim (drops_split_trans_bind2 ā¦ H1) -H1 [ |*: // ] #Z #Y #HLY #HYK #_
  elim (coafter_fwd_xpx_pushs ā¦ 0 ā¦ H3) [ |*: // ] #g2 #H3 #H2 destruct
  lapply (drops_isuni_fwd_drop2 ā¦ HLY) -HLY // #HLY
  lapply (IH ā¦ HYK ā¦ H3) -IH -H3 -HYK [4: |*: /2 width=2 by lifts_lref/ ]
  >nplus_succ_sn /2 width=3 by frees_lref_pushs/ (**) (* full auto fails *)
| #f1 #K #l #Hf1 #_ #f #L #HLK #U #H2 #f2 #H3
  lapply (pr_coafter_isi_inv_dx ā¦ H3 ā¦ Hf1) -f1 #Hf2
  >(lifts_inv_gref1 ā¦ H2) -U /2 width=1 by frees_gref/
| #f1V #f1T #f1 #p #I #K #V #T #_ #_ #H1f1 #IHV #IHT #H2f1 #f #L #H1 #Y #H2 #f2 #H3
  elim (pr_sor_inv_isf ā¦ H1f1) // #Hf1V #H
  lapply (pr_isf_inv_tl ā¦ H) -H
  elim (lifts_inv_bind1 ā¦ H2) -H2 #W #U #HVW #HTU #H destruct
  elim (pr_sor_coafter_dx_tans ā¦ H3 ā¦ H1f1) /2 width=5 by pr_coafter_des_ist_isf/ -H3 -H1f1 #f2V #f2T #Hf2V #H
  elim (pr_coafter_inv_tl_dx ā¦ H) -H
  /5 width=5 by frees_bind, drops_skip, ext2_pair/
| #f1V #f1T #f1 #I #K #V #T #_ #_ #H1f1 #IHV #IHT #H2f1 #f #L #H1 #Y #H2 #f2 #H3
  elim (pr_sor_inv_isf ā¦ H1f1) //
  elim (lifts_inv_flat1 ā¦ H2) -H2 #W #U #HVW #HTU #H destruct
  elim (pr_sor_coafter_dx_tans ā¦ H3 ā¦ H1f1)
  /3 width=5 by pr_coafter_des_ist_isf, frees_flat/
]
qed-.

lemma frees_lifts_SO:
      āb,L,K. ā©*[b,šāØ1ā©] L ā K ā āT,U. ā§[1] T ā U ā
      āf. K ā¢ š+āØTā© ā f ā L ā¢ š+āØUā© ā ā«Æf.
#b #L #K #HLK #T #U #HTU #f #Hf
@(frees_lifts b ā¦ Hf ā¦ HTU) //  (**) (* auto fails *)
qed.

(* Forward lemmas with generic slicing for local environments ***************)

lemma frees_fwd_coafter:
      āb,f2,L,U. L ā¢ š+āØUā© ā f2 ā
      āf,K. ā©*[b,f] L ā K ā āT. ā§*[f] T ā U ā
      āf1. K ā¢ š+āØTā© ā f1 ā f ~ā f1 ā f2.
/4 width=11 by frees_lifts, frees_mono, pr_coafter_eq_repl_back/ qed-.

(* Inversion lemmas with generic slicing for local environments *************)

lemma frees_inv_lifts_ex:
      āb,f2,L,U. L ā¢ š+āØUā© ā f2 ā
      āf,K. ā©*[b,f] L ā K ā āT. ā§*[f] T ā U ā
      āāf1. f ~ā f1 ā f2 & K ā¢ š+āØTā© ā f1.
#b #f2 #L #U #Hf2 #f #K #HLK #T elim (frees_total K T)
/3 width=9 by frees_fwd_coafter, ex2_intro/
qed-.

lemma frees_inv_lifts_SO:
      āb,f,L,U. L ā¢ š+āØUā© ā f ā
      āK. ā©*[b,šāØ1ā©] L ā K ā āT. ā§[1] T ā U ā
      K ā¢ š+āØTā© ā ā«°f.
#b #f #L #U #H #K #HLK #T #HTU elim(frees_inv_lifts_ex ā¦ H ā¦ HLK ā¦ HTU) -b -L -U
#f1 #Hf #Hf1 elim (pr_coafter_inv_next_sn ā¦ Hf) -Hf
/3 width=5 by frees_eq_repl_back, pr_coafter_isi_inv_sn/
qed-.

lemma frees_inv_lifts:
      āb,f2,L,U. L ā¢ š+āØUā© ā f2 ā
      āf,K. ā©*[b,f] L ā K ā āT. ā§*[f] T ā U ā
      āf1. f ~ā f1 ā f2 ā K ā¢ š+āØTā© ā f1.
#b #f2 #L #U #H #f #K #HLK #T #HTU #f1 #Hf2 elim (frees_inv_lifts_ex ā¦ H ā¦ HLK ā¦ HTU) -b -L -U
/3 width=7 by frees_eq_repl_back, pr_coafter_inj/
qed-.

(* Note: this is used by rex_conf and might be modified *)
lemma frees_inv_drops_next:
      āf1,L1,T1. L1 ā¢ š+āØT1ā© ā f1 ā
      āI2,L2,V2,i. ā©[i] L1 ā L2.ā[I2]V2 ā
      āg1. āg1 = ā«°*[i] f1 ā
      āāg2. L2 ā¢ š+āØV2ā© ā g2 & g2 ā g1.
#f1 #L1 #T1 #H elim H -f1 -L1 -T1
[ #f1 #L1 #s #Hf1 #I2 #L2 #V2 #j #_ #g1 #H1 -I2 -L1 -s
  lapply (pr_isi_tls j ā¦ Hf1) -Hf1 <H1 -f1 #Hf1
  elim (pr_isi_inv_next ā¦ Hf1) -Hf1 //
| #f1 #i #_ #I2 #L2 #V2 #j #H
  elim (drops_inv_atom1 ā¦ H) -H #H destruct
| #f1 #I1 #L1 #V1 #Hf1 #IH #I2 #L2 #V2 *
  [ -IH #HL12 lapply (drops_fwd_isid ā¦ HL12 ?) -HL12 //
    #H destruct #g1 #Hgf1 >(eq_inv_pr_next_bi ā¦ Hgf1) -g1
    /2 width=3 by ex2_intro/
  | -Hf1 #j #HL12 lapply (drops_inv_drop1 ā¦ HL12) -HL12
    #HL12 #g1 <pr_tls_swap <pr_tl_next #Hgf1 elim (IH ā¦ HL12 ā¦ Hgf1) -IH -HL12 -Hgf1
    /2 width=3 by ex2_intro/
  ]
| #f1 #I1 #L1 #Hf1 #I2 #L2 #V2 *
  [ #HL12 lapply (drops_fwd_isid ā¦ HL12 ?) -HL12 // #H destruct
  | #j #_ #g1 #Hgf1 elim (pr_isi_inv_next ā¦ Hgf1) -Hgf1 <pr_tls_swap /2 width=1 by pr_isi_tls/
  ]
| #f1 #I1 #L1 #i #_ #IH #I2 #L2 #V2 *
  [ -IH #_ #g1 #Hgf1 elim (eq_inv_pr_next_push ā¦ Hgf1)
  | #j #HL12 lapply (drops_inv_drop1 ā¦ HL12) -HL12
    #HL12 #g1 <pr_tls_swap #Hgf1 elim (IH ā¦ HL12 ā¦ Hgf1) -IH -HL12 -Hgf1
    /2 width=3 by ex2_intro/
  ]
| #f1 #L1 #l #Hf1 #I2 #L2 #V2 #j #_ #g1 #H1 -I2 -L1 -l
  lapply (pr_isi_tls j ā¦ Hf1) -Hf1 <H1 -f1 #Hf1
  elim (pr_isi_inv_next ā¦ Hf1) -Hf1 //
| #fV1 #fT1 #f1 #p #I1 #L1 #V1 #T1 #_ #_ #Hf1 #IHV1 #IHT1 #I2 #L2 #V2 #j #HL12 #g1 #Hgf1
  lapply (pr_sor_tls ā¦ Hf1 j) -Hf1 <Hgf1 -Hgf1 #Hf1
  elim (pr_sor_next_tl ā¦ Hf1) [1,2: * |*: // ] -Hf1
  #gV1 #gT1 #Hg1
  [ -IHT1 #H1 #_ elim (IHV1 ā¦ HL12 ā¦ H1) -IHV1 -HL12 -H1
    /3 width=6 by pr_sor_inv_sle_sn_trans, ex2_intro/
  | -IHV1 #_ >pr_tls_swap #H2 elim (IHT1 ā¦ H2) -IHT1 -H2
    /3 width=6 by drops_drop, pr_sor_inv_sle_dx_trans, ex2_intro/
  ]
| #fV1 #fT1 #f1 #I1 #L1 #V1 #T1 #_ #_ #Hf1 #IHV1 #IHT1 #I2 #L2 #V2 #j #HL12 #g1 #Hgf1
  lapply (pr_sor_tls ā¦ Hf1 j) -Hf1 <Hgf1 -Hgf1 #Hf1
  elim (pr_sor_next_tl ā¦ Hf1) [1,2: * |*: // ] -Hf1
  #gV1 #gT1 #Hg1
  [ -IHT1 #H1 #_ elim (IHV1 ā¦ HL12 ā¦ H1) -IHV1 -HL12 -H1
    /3 width=6 by pr_sor_inv_sle_sn_trans, ex2_intro/
  | -IHV1 #_ #H2 elim (IHT1 ā¦ HL12 ā¦ H2) -IHT1 -HL12 -H2
    /3 width=6 by pr_sor_inv_sle_dx_trans, ex2_intro/
  ]
]
qed-.

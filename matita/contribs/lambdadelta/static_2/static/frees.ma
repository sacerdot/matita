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

include "ground/relocation/rtmap_sor.ma".
include "static_2/notation/relations/freeplus_3.ma".
include "static_2/syntax/lenv.ma".

(* CONTEXT-SENSITIVE FREE VARIABLES *****************************************)

inductive frees: relation3 lenv term pr_map โ
| frees_sort: โf,L,s. ๐โจfโฉ โ frees L (โs) f
| frees_atom: โf,i. ๐โจfโฉ โ frees (โ) (#i) (โซฏ*[i]โf)
| frees_pair: โf,I,L,V. frees L V f โ
              frees (L.โ[I]V) (#0) (โf)
| frees_unit: โf,I,L. ๐โจfโฉ โ frees (L.โค[I]) (#0) (โf)
| frees_lref: โf,I,L,i. frees L (#i) f โ
              frees (L.โ[I]) (#โi) (โซฏf)
| frees_gref: โf,L,l. ๐โจfโฉ โ frees L (ยงl) f
| frees_bind: โf1,f2,f,p,I,L,V,T. frees L V f1 โ frees (L.โ[I]V) T f2 โ
              f1 โ โซฐf2 โ f โ frees L (โ[p,I]V.T) f
| frees_flat: โf1,f2,f,I,L,V,T. frees L V f1 โ frees L T f2 โ
              f1 โ f2 โ f โ frees L (โ[I]V.T) f
.

interpretation
   "context-sensitive free variables (term)"
   'FreePlus L T f = (frees L T f).

(* Basic inversion lemmas ***************************************************)

fact frees_inv_sort_aux: โf,L,X. L โข ๐+โจXโฉ โ f โ โx. X = โx โ ๐โจfโฉ.
#L #X #f #H elim H -f -L -X //
[ #f #i #_ #x #H destruct
| #f #_ #L #V #_ #_ #x #H destruct
| #f #_ #L #_ #x #H destruct
| #f #_ #L #i #_ #_ #x #H destruct
| #f1 #f2 #f #p #I #L #V #T #_ #_ #_ #_ #_ #x #H destruct
| #f1 #f2 #f #I #L #V #T #_ #_ #_ #_ #_ #x #H destruct
]
qed-.

lemma frees_inv_sort: โf,L,s. L โข ๐+โจโsโฉ โ f โ ๐โจfโฉ.
/2 width=5 by frees_inv_sort_aux/ qed-.

fact frees_inv_atom_aux:
     โf,L,X. L โข ๐+โจXโฉ โ f โ โi. L = โ โ X = #i โ
     โโg. ๐โจgโฉ & f = โซฏ*[i]โg.
#f #L #X #H elim H -f -L -X
[ #f #L #s #_ #j #_ #H destruct
| #f #i #Hf #j #_ #H destruct /2 width=3 by ex2_intro/
| #f #I #L #V #_ #_ #j #H destruct
| #f #I #L #_ #j #H destruct
| #f #I #L #i #_ #_ #j #H destruct
| #f #L #l #_ #j #_ #H destruct
| #f1 #f2 #f #p #I #L #V #T #_ #_ #_ #_ #_ #j #_ #H destruct
| #f1 #f2 #f #I #L #V #T #_ #_ #_ #_ #_ #j #_ #H destruct
]
qed-.

lemma frees_inv_atom: โf,i. โ โข ๐+โจ#iโฉ โ f โ โโg. ๐โจgโฉ & f = โซฏ*[i]โg.
/2 width=5 by frees_inv_atom_aux/ qed-.

fact frees_inv_pair_aux:
     โf,L,X. L โข ๐+โจXโฉ โ f โ โI,K,V. L = K.โ[I]V โ X = #0 โ
     โโg. K โข ๐+โจVโฉ โ g & f = โg.
#f #L #X * -f -L -X
[ #f #L #s #_ #Z #Y #X #_ #H destruct
| #f #i #_ #Z #Y #X #H destruct
| #f #I #L #V #Hf #Z #Y #X #H #_ destruct /2 width=3 by ex2_intro/
| #f #I #L #_ #Z #Y #X #H destruct
| #f #I #L #i #_ #Z #Y #X #_ #H destruct
| #f #L #l #_ #Z #Y #X #_ #H destruct
| #f1 #f2 #f #p #I #L #V #T #_ #_ #_ #Z #Y #X #_ #H destruct
| #f1 #f2 #f #I #L #V #T #_ #_ #_ #Z #Y #X #_ #H destruct
]
qed-.

lemma frees_inv_pair: โf,I,K,V. K.โ[I]V โข ๐+โจ#0โฉ โ f โ โโg. K โข ๐+โจVโฉ โ g & f = โg.
/2 width=6 by frees_inv_pair_aux/ qed-.

fact frees_inv_unit_aux:
     โf,L,X. L โข ๐+โจXโฉ โ f โ โI,K. L = K.โค[I] โ X = #0 โ
     โโg. ๐โจgโฉ & f = โg.
#f #L #X * -f -L -X
[ #f #L #s #_ #Z #Y #_ #H destruct
| #f #i #_ #Z #Y #H destruct
| #f #I #L #V #_ #Z #Y #H destruct
| #f #I #L #Hf #Z #Y #H destruct /2 width=3 by ex2_intro/
| #f #I #L #i #_ #Z #Y #_ #H destruct
| #f #L #l #_ #Z #Y #_ #H destruct
| #f1 #f2 #f #p #I #L #V #T #_ #_ #_ #Z #Y #_ #H destruct
| #f1 #f2 #f #I #L #V #T #_ #_ #_ #Z #Y #_ #H destruct
]
qed-.

lemma frees_inv_unit: โf,I,K. K.โค[I] โข ๐+โจ#0โฉ โ f โ โโg. ๐โจgโฉ & f = โg.
/2 width=7 by frees_inv_unit_aux/ qed-.

fact frees_inv_lref_aux:
     โf,L,X. L โข ๐+โจXโฉ โ f โ โI,K,j. L = K.โ[I] โ X = #(โj) โ
     โโg. K โข ๐+โจ#jโฉ โ g & f = โซฏg.
#f #L #X * -f -L -X
[ #f #L #s #_ #Z #Y #j #_ #H destruct
| #f #i #_ #Z #Y #j #H destruct
| #f #I #L #V #_ #Z #Y #j #_ #H destruct
| #f #I #L #_ #Z #Y #j #_ #H destruct
| #f #I #L #i #Hf #Z #Y #j #H1 #H2 destruct /2 width=3 by ex2_intro/
| #f #L #l #_ #Z #Y #j #_ #H destruct
| #f1 #f2 #f #p #I #L #V #T #_ #_ #_ #Z #Y #j #_ #H destruct
| #f1 #f2 #f #I #L #V #T #_ #_ #_ #Z #Y #j #_ #H destruct
]
qed-.

lemma frees_inv_lref:
      โf,I,K,i. K.โ[I] โข ๐+โจ#(โi)โฉ โ f โ
      โโg. K โข ๐+โจ#iโฉ โ g & f = โซฏg.
/2 width=6 by frees_inv_lref_aux/ qed-.

fact frees_inv_gref_aux: โf,L,X. L โข ๐+โจXโฉ โ f โ โx. X = ยงx โ ๐โจfโฉ.
#f #L #X #H elim H -f -L -X //
[ #f #i #_ #x #H destruct
| #f #_ #L #V #_ #_ #x #H destruct
| #f #_ #L #_ #x #H destruct
| #f #_ #L #i #_ #_ #x #H destruct
| #f1 #f2 #f #p #I #L #V #T #_ #_ #_ #_ #_ #x #H destruct
| #f1 #f2 #f #I #L #V #T #_ #_ #_ #_ #_ #x #H destruct
]
qed-.

lemma frees_inv_gref: โf,L,l. L โข ๐+โจยงlโฉ โ f โ ๐โจfโฉ.
/2 width=5 by frees_inv_gref_aux/ qed-.

fact frees_inv_bind_aux:
     โf,L,X. L โข ๐+โจXโฉ โ f โ โp,I,V,T. X = โ[p,I]V.T โ
     โโf1,f2. L โข ๐+โจVโฉ โ f1 & L.โ[I]V โข ๐+โจTโฉ โ f2 & f1 โ โซฐf2 โ f.
#f #L #X * -f -L -X
[ #f #L #s #_ #q #J #W #U #H destruct
| #f #i #_ #q #J #W #U #H destruct
| #f #I #L #V #_ #q #J #W #U #H destruct
| #f #I #L #_ #q #J #W #U #H destruct
| #f #I #L #i #_ #q #J #W #U #H destruct
| #f #L #l #_ #q #J #W #U #H destruct
| #f1 #f2 #f #p #I #L #V #T #HV #HT #Hf #q #J #W #U #H destruct /2 width=5 by ex3_2_intro/
| #f1 #f2 #f #I #L #V #T #_ #_ #_ #q #J #W #U #H destruct
]
qed-.

lemma frees_inv_bind:
      โf,p,I,L,V,T. L โข ๐+โจโ[p,I]V.Tโฉ โ f โ
      โโf1,f2. L โข ๐+โจVโฉ โ f1 & L.โ[I]V โข ๐+โจTโฉ โ f2 & f1 โ โซฐf2 โ f.
/2 width=4 by frees_inv_bind_aux/ qed-.

fact frees_inv_flat_aux: โf,L,X. L โข ๐+โจXโฉ โ f โ โI,V,T. X = โ[I]V.T โ
                         โโf1,f2. L โข ๐+โจVโฉ โ f1 & L โข ๐+โจTโฉ โ f2 & f1 โ f2 โ f.
#f #L #X * -f -L -X
[ #f #L #s #_ #J #W #U #H destruct
| #f #i #_ #J #W #U #H destruct
| #f #I #L #V #_ #J #W #U #H destruct
| #f #I #L #_ #J #W #U #H destruct
| #f #I #L #i #_ #J #W #U #H destruct
| #f #L #l #_ #J #W #U #H destruct
| #f1 #f2 #f #p #I #L #V #T #_ #_ #_ #J #W #U #H destruct
| #f1 #f2 #f #I #L #V #T #HV #HT #Hf #J #W #U #H destruct /2 width=5 by ex3_2_intro/
]
qed-.

lemma frees_inv_flat:
      โf,I,L,V,T. L โข ๐+โจโ[I]V.Tโฉ โ f โ
      โโf1,f2. L โข ๐+โจVโฉ โ f1 & L โข ๐+โจTโฉ โ f2 & f1 โ f2 โ f.
/2 width=4 by frees_inv_flat_aux/ qed-.

(* Basic properties ********************************************************)

lemma frees_eq_repl_back: โL,T. pr_eq_repl_back โฆ (ฮปf. L โข ๐+โจTโฉ โ f).
#L #T #f1 #H elim H -f1 -L -T
[ /3 width=3 by frees_sort, pr_isi_eq_repl_back/
| #f1 #i #Hf1 #g2 #H
  elim (pr_eq_inv_pushs_sn โฆ H) -H #g #Hg #H destruct
  elim (eq_inv_nx โฆ Hg) -Hg
  /3 width=3 by frees_atom, pr_isi_eq_repl_back/
| #f1 #I #L #V #_ #IH #g2 #H
  elim (eq_inv_nx โฆ H) -H
  /3 width=3 by frees_pair/
| #f1 #I #L #Hf1 #g2 #H
  elim (eq_inv_nx โฆ H) -H
  /3 width=3 by frees_unit, pr_isi_eq_repl_back/
| #f1 #I #L #i #_ #IH #g2 #H
  elim (eq_inv_px โฆ H) -H /3 width=3 by frees_lref/
| /3 width=3 by frees_gref, pr_isi_eq_repl_back/
| /3 width=7 by frees_bind, pr_sor_eq_repl_back/
| /3 width=7 by frees_flat, pr_sor_eq_repl_back/
]
qed-.

lemma frees_eq_repl_fwd: โL,T. pr_eq_repl_fwd โฆ (ฮปf. L โข ๐+โจTโฉ โ f).
#L #T @pr_eq_repl_sym /2 width=3 by frees_eq_repl_back/
qed-.

lemma frees_lref_push: โf,i. โ โข ๐+โจ#iโฉ โ f โ โ โข ๐+โจ#โiโฉ โ โซฏf.
#f #i #H
elim (frees_inv_atom โฆ H) -H #g #Hg #H destruct
/2 width=1 by frees_atom/
qed.

(* Forward lemmas with test for finite colength *****************************)

lemma frees_fwd_isfin: โf,L,T. L โข ๐+โจTโฉ โ f โ ๐โจfโฉ.
#f #L #T #H elim H -f -L -T
/4 width=5 by pr_sor_inv_isf_bi, pr_isf_isi, pr_isf_tl, pr_isf_pushs, pr_isf_push, pr_isf_next/
qed-.

(* Basic_2A1: removed theorems 30:
              frees_eq frees_be frees_inv
              frees_inv_sort frees_inv_gref frees_inv_lref frees_inv_lref_free
              frees_inv_lref_skip frees_inv_lref_ge frees_inv_lref_lt
              frees_inv_bind frees_inv_flat frees_inv_bind_O
              frees_lref_eq frees_lref_be frees_weak
              frees_bind_sn frees_bind_dx frees_flat_sn frees_flat_dx
              frees_lift_ge frees_inv_lift_be frees_inv_lift_ge
              lreq_frees_trans frees_lreq_conf
              llor_atom llor_skip llor_total
              llor_tail_frees llor_tail_cofrees
*)

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

include "projdat/tuples.ma".

(* Computazione dello schema come proiezione (S pos)-esima *)
lemma schemais2:
∀t,ldt,dc,ldc,t2,pos.
Schema (proj_t2 (mk_tuple_cast (t::ldt) «dc::ldc,t2») (S pos)) = 
Schema (proj_t2 (mk_tuple_cast (ldt) «ldc,?») ( pos)).
 [ 2: @(proj_t2_tl_deq_Type t ldt dc ldc t2)
 | 1: #t #l #d #c #t2 #p >(proj_t2_tl) // 
 ] 
qed.

(******************************************************************************)

(* Rappresentazione dell'ottenimento di uno schema di una proiezione su tupla
   come la selezione del pos-esimo elemento dalla lista
*)
lemma coerc4:
∀ldt,ldc,t2,pos.
 (Schema (proj_t2 (mk_tuple_cast (ldt) «ldc,t2») ( pos))
  =optScheme (nth_opt DeqCoer pos ldc)).

#ldt elim ldt -ldt
  [ #ldc elim ldc -ldc
    [ //
    | #c #ld #IH #prop #i
      elim i -i
      [ //
      | #i #IH2 >coerc2
        >coerc2 in IH2;
        #IH2
        lapply (gSchema_void2 … prop)
        #IH3 >IH3 normalize @refl
      ]
    ]
  | #dt #ldt #IH
    #ldc elim ldc -ldc
    [ //
    | #c #lc #IH2 -IH2
      #prop #pos elim pos -pos
        [ //
        | #i #IH3 -IH3
          lapply (gSchema_rest … prop)
          #prop2
          lapply (IH lc prop2 i)
          #IH3 
          >optScheme1
          <IH3 
          >schemais2 //
      ]
    ]
  ]
qed.



(* A questo punto debbo prima dimostrare che le tuple generate hanno lo stesso
   schema, e quindi hanno lo stesso tipo di dato.
 *)
lemma coercition2:
∀t,i.
(Schema (proj_t2 t i))=(optScheme
  (nth_opt DeqCoer i
   (Sig_fst tup_Inst (λ c:tup_Inst.Schema t=getSchema c) (tc_to_t t)))).
* #ts elim ts -ts #t
  [ #pos >coerc2 >tctt_void_preservation  >voidopt_lemma normalize @refl
  | #ldt #IH -IH * #ins elim ins -ins
    [ #prop #pos 
      >coerc3 normalize //
    | #dc #ldc #IH2 -IH2 #t2 #pos 
      elim pos -pos
      [ normalize @refl
      | #pos  #IH3  -IH3
        >nthopt_S2
        lapply (gSchema_rest … t2)
        #ct2 destruct 
        >coerc4 //
      ]
    ]
  ]
qed.


lemma coercition2_tuple: ∀t,i.

(tuple (Schema (proj_t2 t i)))
               =
(tuple (optScheme (nth_opt DeqCoer i
      (Sig_fst tup_Inst (λ c:tup_Inst.Schema t=getSchema c) (tc_to_t t))))).
      
#t #i @eq_f @coercition2
qed.



lemma coercition2_tuple_transform:  ∀t,i.
(tuple (Schema (proj_t2 t i)))→
  (tuple (optScheme
    (nth_opt DeqCoer i
     (Sig_fst tup_Inst (λ c:tup_Inst.Schema t=getSchema c) (tc_to_t t))))).
     
#t #i #Hp <coercition2_tuple @Hp qed.


lemma coercition2_tuple_transform2:  ∀t,i.
(tuple (optScheme
  (nth_opt DeqCoer i
   (Sig_fst tup_Inst (λ c:tup_Inst.Schema t=getSchema c) (tc_to_t t)))))
   →
      (tuple (Schema (proj_t2 t i))).
#t #i #Hp >coercition2_tuple @Hp qed.

lemma eqTup:
∀t.
tc_to_t t = Tuple t.
#t elim t -t
 #s #ts normalize // qed.

lemma coercition2_tuple_transform_T:  ∀t,i.
(tuple (Schema (proj_t2 t i)))→
  (tuple (optScheme
    (nth_opt DeqCoer i
     (Sig_fst tup_Inst (λ c:tup_Inst.Schema t=getSchema c) (Tuple t))))).
     
//  qed.


lemma coercition2_tuple_transform2_T:  ∀t,i.
(tuple (optScheme
  (nth_opt DeqCoer i
   (Sig_fst tup_Inst (λ c:tup_Inst.Schema t=getSchema c) (Tuple t)))))
   →
      (tuple (Schema (proj_t2 t i))).
//  qed.


(*

theorem preservation2:
∀t,i.
proj_t1 (Schema t) (Tuple t) i = (tc_to_t (proj_t2 t i)).
…

********** DISAMBIGUATION ERRORS: **********
***** Errors obtained during phases 1: *****
*Error at 70-91: The term
(tc_to_t (proj_t2 t i))
has type
(tuple (Schema (proj_t2 t i)))
but is here used with type
(tuple
 (optScheme
  (nth_opt DeqCoer i
   (Sig_fst tup_Inst (\lambda c:tup_Inst.Schema t=getSchema c) (tc_to_t t)))))

In quanto aver dimostrato l'uguaglianza dei tipi come già dimostrato non consente
di poter confrontare questi due elementi, allora è necessario mostrare d'ora in
poi una forma d'uguaglianza più debole.
       
*)   


theorem preservation2: ∀t,i.
 coercition2_tuple_transform2_T t i(proj_t1 (Schema t) (Tuple t) i) = (tc_to_t (proj_t2 t i)).
#t #i normalize @refl qed.

theorem preservation2bis: ∀t,i.
 (proj_t1 (Schema t) (Tuple t) i) = coercition2_tuple_transform_T t i (tc_to_t (proj_t2 t i)).
normalize #t #i @refl qed.

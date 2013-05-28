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

include "projdat/coerc.ma".

(**************************************************************************)
(*                Definizione di alcuni lemmi sulle liste                 *)
(**************************************************************************)
lemma list_tail: ∀A:DeqSet. ∀a:A. ∀b:DeqList A. (tail A (a::b))=b. // qed.
lemma list_head: ∀A:DeqSet. ∀a,c:A. ∀b:DeqList A. (hd A (a::b) c)=a. // qed.
lemma list_lhdtl: ∀A:DeqSet. ∀a:A. ∀b,l:DeqList A. l=a::b → (a=hd ? l a)∧(b=tail ? l).
#A #a #b #l #Hp destruct normalize /2/ qed.  
lemma list_hdtll: ∀A:DeqSet. ∀a:A. ∀b,l:DeqList A. a::b=l → (a=hd ? l a)∧(b=tail ? l).
#A #a #b #l #Hp destruct normalize /2/ qed.  
(***************************************************************************)

(* Definizione di istanza di una tupla *)
definition tup_Inst ≝ DeqList DeqCoer.
(* Definizione di uno schema di tupla *)
definition tup_Sche ≝ DeqList DeqType.

(* Dato un'istanza di tupla, riottiene il suo schema *)
definition getSchema : tup_Inst → tup_Sche ≝ 
  λl. map DeqCoer DeqType getType l.

(* PRIMA DEFINIZIONE DI UNA TUPLA:
   1) Data una lista di schemi ed uno d'istanze, quest'ultimo rispetta i tipi
      della prima
 *)
definition tuple ≝ λt. DeqSig tup_Inst (λc. t=(getSchema c)).
    (* Funzione di creazione di una tupla di primo tipo *)
definition mk_tuple : ∀s:tup_Sche. tup_Inst → ? → tuple s ≝ 
λs:tup_Sche.λt:tup_Inst.λp. mk_Sig tup_Inst (λc. s=(getSchema c)) t p.

(* Funzioni di equivalenza da getSchema nulla *)
lemma gSchema_void: ∀tup. tup= [] → []=getSchema tup.
#t elim t -t //
  #Coer #ld #IH #Hp >Hp normalize @refl
  qed.


lemma gSchema_hd: ∀a,b. getSchema(a::b)=(getType a)::(getSchema b).
#a elim a -a #el #l // qed. 
  
lemma gSchema_void2: ∀tup. []=getSchema tup→tup=[].
#t elim t -t //
  #Coer elim Coer -Coer #C #LD #IH #Hp >gSchema_hd in Hp; #Hp
  @False_ind 
  destruct qed.

lemma gSchema_hdtl: ∀a,b,c,d. a::b=getSchema(c::d)→a::b=(getType c)::(getSchema d).
#a #b #c #d >gSchema_hd #hp @hp qed.










(* SECONDA DEFINIZIONE DI UNA TUPLA:
    2) È un tipo, dove la prima definizione viene inglobata assieme allo schema,
       ed incorporata in un unico dato
 *)  
record tuple_cast : Type[0] ≝ {
  Schema : tup_Sche;
  Tuple  : tuple Schema
}.

(* Lo schema di una tuple_cast è esattamente quello di parametro del suo tipo Σ *)
lemma schemais:
∀t,ldt,dc,ldc,t2.
Schema ( (mk_tuple_cast (t::ldt) «dc::ldc,t2») )=t::ldt. // qed.

(* Conversione 2 ⇒ 1 *)
definition tc_to_t : ∀s:tuple_cast.  (tuple (Schema s)).
* #s #u @u qed.

(* Conversione 1 ⇒ 2 *)
definition t_to_tc : ∀S. tuple S → tuple_cast ≝ λS,x. mk_tuple_cast S x.

(* Lemmi di preservazione della struttura dati: 2 ⇒ 1 ⇒ 2 *)
lemma tc_t_tc : ∀x. t_to_tc (Schema x) (tc_to_t x) =x.
* #s #t normalize // qed.
(* Lemmi di preservazione della struttura dati: 1 ⇒ 2 ⇒ 1 *)
lemma t_tc_t: ∀s,t. tc_to_t (t_to_tc s t) = t.
#s #t normalize // qed.

lemma base_coerc1: ∀x. (getType (CNat x))=Nat. // qed.
lemma base_coerc2: ∀x. (getType (CBool x))=Bool. // qed.

(* Definizione di una tupla con un singolo elemento: questa può essere effettuata
   fornendo unicamente il valore del dato (1)
 *)
definition singleton: ∀c:DeqCoer. tuple [getType c].
* #V
  [ >base_coerc1 @(mk_tuple [Nat] [CNat V] (refl ? [Nat]))
  | >base_coerc2 @(mk_tuple [Bool] [CBool V] (refl ? [Bool]))]. qed.

(* Definizione di tuple vuote rispettivamente di tipo 1 e 2 *)
definition voideton: tuple []. @(mk_tuple [] [] (refl ? [])) qed.
definition voideton2 ≝ mk_tuple_cast [] voideton.

lemma voideton_eq: ∀t:tuple[]. mk_tuple_cast [] t = voideton2.
* #inst elim inst
  [ #prop normalize @eq_f destruct //
  | #dc #ldc #IH #AI lapply (gSchema_void2 … AI) #AI2 destruct 
  ]
qed.

(******************************************************************************)






(**************************************************)
(* Definizione della funzione di proiezione per 1 *)
(**************************************************)
(* Funzione per la restituzione del tipo di dato opportuno dato un valore opzionale *)
definition optScheme : option DeqCoer→tup_Sche ≝  λu.
 match u with
 [ None ⇒ [ ]
 | Some a ⇒ [getType a]].
 
(* Funzione per l'istanziazione della tupla dal risultato della coercizione *)
definition proj_5t: ∀x:option DeqCoer. tuple (optScheme x).
* [ @voideton
  | #arg @(singleton arg)] qed.

(* Funzione di proiezione per 1 *)
definition proj_t1: ∀s:tup_Sche.∀t:tuple s. ℕ→tuple ?.
[ #s #t #i @(proj_5t (nth_opt ? i (Sig_fst ? ? t) )) ] skip qed.

(* Definizione della proiezione in posizione (S n)-esima *)
lemma optScheme1:
  ∀n,dc,ld.
  optScheme (nth_opt DeqCoer (S n) (dc::ld))=optScheme (nth_opt DeqCoer n ld).

#n #dc #ld normalize // qed.





(**************************************************)
(* Definizione della funzione di proiezione per 2 *)
(**************************************************)
definition proj_t2 ≝ λtc,i.
match nth_opt ? i (Sig_fst ? ? (Tuple tc)) with
[ None ⇒ mk_tuple_cast [] voideton
| Some a ⇒ mk_tuple_cast [getType a] (singleton a)].

(* Lemmi sulla funzione di proiezione *)
lemma proj_t2_null: ∀i. proj_t2 voideton2 i = voideton2.
#i normalize // qed.
lemma proj_t2_head: ∀a. proj_t2 (mk_tuple_cast [getType a] (singleton a)) O = mk_tuple_cast [getType a] (singleton a).
#a elim a -a // qed.
lemma proj_t2_head_N: ∀a,i. proj_t2 (mk_tuple_cast [getType a] (singleton a)) (S i)=voideton2.
#a elim a -a // qed.


(******************************************************************************)

(* Definizione di proiezione dell'elemento (S x)-esimo elemento per ogni tipo di
tupla *)
theorem proj_t1_tl: ∀dt,ldt,ld,IH,prop,pos.

    (proj_t1 (dt::ldt) «ld::IH,prop» (S pos)) = (proj_t1 (ldt) «IH,?» (pos)).

[ #d #ld #dc #ldl #prop #pos //
| lapply (list_hdtll … prop) * >list_tail >list_head
  #h @(rewrite_r … (getSchema IH)) //
] qed.



(* Rappresentazione di una lista di "tipi" dalla rappresentazione del valore *)
lemma proj_t2_tl_deq_Type: 
∀dt:DeqType. ∀ldt:list DeqType. ∀ld:DeqCoer. 
∀IH:list DeqCoer.∀prop: dt::ldt=getSchema (ld::IH).

     (ldt=getSchema IH).

#d #ld #dc #ldl #prop  
lapply (list_hdtll … prop) * >list_tail >list_head
  #h @(rewrite_r … (getSchema ldl)) // qed.



(* Definizione della proiezione sul secondo tipo di tupla *)
theorem proj_t2_tl :  ∀dt,ldt,ld,IH,prop,pos.

    proj_t2 (t_to_tc (dt::ldt) «ld::IH,prop») (S pos) 
      = proj_t2 (t_to_tc ldt «IH,?») pos.

[ #d #ld #dc #ldl #prop #pos //
| @(proj_t2_tl_deq_Type dt ldt ld IH prop)
] qed.



(******************************************************************************)

(* Una tupla vuota per 1) è un voideton 2) *)
lemma t_to_tc_void_as_voideton2 : ∀t: tuple [].        t_to_tc [] t = voideton2.
  #t elim t 
  #tup #prop 
  normalize lapply (gSchema_void2 … prop) #Hp 
  destruct normalize 
  // 
qed.


 
(* Una qualunque proiezione di un tipo di tupla 1) restituirà nessun elemento *)
lemma voidopt_lemma: ∀t,pos.
 (nth_opt DeqCoer pos (Sig_fst tup_Inst (λc:tup_Inst.[]=getSchema c) t)) 
    = None DeqCoer.
#t elim t -t #is #prop #n lapply (gSchema_void2 … prop) #Hp destruct
   normalize // qed.



lemma void_optS:             (optScheme (None DeqCoer)) = [].            // qed.
lemma void_tup: (tuple (optScheme (None DeqCoer)))= tuple []. >void_optS // qed. 



(* Valutazione di una proiezione di tupla vuota 1) come eq_rect_Type0_r  *)
lemma proj_nothing_void : ∀t:tuple []. ∀pos. (proj_t1 [] t pos)= ?.
[ 2: >voidopt_lemma  >void_tup @t
| #t elim t -t #s #prop lapply (gSchema_void2 … prop) #Hp #pos
  destruct normalize // qed.
(* check proj_nothing_void *)
lemma proj_nothing_voideton: ∀pos. proj_t2 voideton2 pos = voideton2.
#n elim n -n normalize // qed.

(* Valutazione di una proiezione di una tupla vuota 2) come voideton2 
lemma t_to_c_proj1_void:
∀dt, ldt, s1,n. proj_t2 (t_to_tc (dt::ldt) «[],s1») n = voideton2. // qed.
*)




(* Se la restituzione di uno schema per una istanza l è a::b, allora 
   b sarà pari allo schema ottenibile dal resto di l *)
lemma gSchema_tl: ∀a,b,l.     a::b=getSchema l → b = getSchema (tail DeqCoer l).

#a @listD_elim2 
  [ #n #l elim l -l
    [ #Hp normalize in Hp; normalize destruct
    | #dc #ldc #IH #Hp >list_tail lapply (list_lhdtl …Hp)  * 
      >list_head #oH1 >list_tail @(rewrite_l … (getSchema ldc)) //]
  | #ldt #el1 -el1 #l elim l -l
    [ #Hp //
    | #DC #ldc #IH #hp >list_tail lapply (list_hdtll … hp) -hp 
      >list_head >list_tail * #oh1 @(rewrite_r … (getSchema ldc)) //
    ]
  | #ldt #m #d -d -ldt #u #IH  #l elim l 
    [ #Hp lapply (IH … []) normalize #banal normalize in Hp; destruct
    | #dc #ldc #IH #e1 >list_tail lapply (list_hdtll … e1) >list_head
      * #oh1 >list_tail @(rewrite_r … (getSchema ldc)) //
    ]
  | @([a])
  ]
qed.


lemma gSchema_tltl: ∀b,l.     b=getSchema l → tail DeqType b = getSchema (tail DeqCoer l).
#b elim b -b
  [ #l #prop lapply(gSchema_void2 … prop) #lP >lP normalize //
  | #dT #ldT #IH #tI #Hp whd in ⊢ (?? % ?); lapply (gSchema_tl … Hp) -Hp
    #Hp //
  ]
qed. 
  
  

lemma gSchema_rest: ∀a,b,e,l.         a::b=getSchema (e::l) → b = getSchema (l).
#a #b #e #l @gSchema_tl qed.

(* "Coercizione" per eq_rect_Type0_r *)
theorem coerc1:
∀ t,pos.t_to_tc
   (optScheme
    (nth_opt DeqCoer pos (Sig_fst tup_Inst (λc:tup_Inst.[]=getSchema c) t)))
   (proj_t1 [] t pos)
   =
   mk_tuple_cast [] t.
   
#t #pos>proj_nothing_void >voidopt_lemma normalize // qed.




(******************************************************************************)

(* Equivalenza tra schemi nell'elemento (S pos)-esimo *)
lemma nthopt_S: ∀pos,t,ldt,dc,ldc,t2.

  (nth_opt DeqCoer (S pos)
      (Sig_fst tup_Inst (λc:tup_Inst.t::ldt=getSchema c)
       (tc_to_t (mk_tuple_cast (t::ldt) «dc::ldc,t2»))))  =
  (nth_opt DeqCoer ( pos)
      (Sig_fst tup_Inst (λc:tup_Inst.ldt=getSchema c)
       (tc_to_t (mk_tuple_cast (ldt) «ldc,?»)))).
     
[ #p #dt #ldt #dc #ldc #hp normalize //
| lapply (gSchema_tl … t2)  #t3 normalize in t3;
  normalize @t3
] qed.


(* Specializzazione del caso precedente, tramite estrazione diretta della 
   componente dello schema *)
lemma nthopt_S2: ∀pos,t,ldt,dc,ldc,t2.

  (nth_opt DeqCoer (S pos)
      (Sig_fst tup_Inst (λc:tup_Inst.t::ldt=getSchema c)
       (tc_to_t (mk_tuple_cast (t::ldt) «dc::ldc,t2»))))=
  (nth_opt DeqCoer pos ldc).
  
#pos #dt #ldt #dc #ldc #p >nthopt_S normalize // qed.

(******************************************************************************)





(* Qualsiasi proiezione di uno schema vuoto è esso stesso uno schema vuoto *)
lemma coerc2: ∀t:tuple [].∀pos.  (Schema (proj_t2 (mk_tuple_cast [] t) pos))=[].
  
* #ti #prop #p >voideton_eq normalize @refl qed.



lemma coerc3 :  ∀t,ldt,ins,prop.

(Sig_fst tup_Inst (λc:tup_Inst.t::ldt=getSchema c)
         (tc_to_t (mk_tuple_cast (t::ldt) «ins,prop»)))=ins.

#dt #ldt #ti #p normalize @refl qed.




(* Le due definizioni di proiezione di tupla preservano la proiezione per il 
   tipo 1) lungo le funzioni di conversione per 2) *)
theorem preservation1:
∀s,t,i. proj_t2 (t_to_tc s t) i = (t_to_tc ? (proj_t1 s t i)).
#s elim s -s
  [ #t #pos >t_to_tc_void_as_voideton2 
            >proj_nothing_voideton
            >coerc1
            normalize elim t
            #p #prop
            lapply (gSchema_void2 … prop)
            #Hp destruct //
  | #dt #ldt #IH
    #t elim t -t
       #el1 elim el1 -el1 
    [ #prop #pos normalize //
    | #ld #IH #Hp #prop #pos elim pos -pos
      [ normalize //
      | #pos #Hp2 >proj_t1_tl >proj_t2_tl //
      ]
    ]
  ] 
qed.




(* Equivalenza tra schemi di tuple cast *)
lemma eqSchema: ∀a,b:tuple_cast.                    a=b → (Schema a)=(Schema b).
* #ts1 #t1 * #ts2 #t2 #Hp destruct @refl qed.




(* Data una tuple_schema a ed uno schema b, se i due schemi sono uguali,
   allora posso restituire una tupla di schema b *)
lemma tTupleSchema: ∀a,b.                                (Schema a)=b → tuple b.
* #schema #inst #bschema #ref <ref @inst qed.



(* Data una tupla a di schema s ed uno schema b, se s=b allora restituisco 
   la tupla come di schema b *)
lemma tTuple: ∀s,b. ∀a:tuple s.                                   s=b → tuple b.
#a #b #inp #ref <ref @inp qed.



(* Identità di t tra funzioni *)
lemma tctt_void_preservation: ∀t:tuple [].   (tc_to_t (mk_tuple_cast [] t)) = t.
* #p #pr normalize @refl qed.

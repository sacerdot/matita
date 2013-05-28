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

include "projdat/nth_proj.ma".

(* Definizione della funzione di proiezione n-esima su valori *)
let rec selection (l:DeqList DeqNat) s (t:DeqList s) ≝ 
  match l with
  [ nil ⇒ []
  | cons a b ⇒ match (nth_opt ? a t ) with
            [None ⇒  selection b s t
            |Some w ⇒ w::(selection b s t)]
  ].


(* Data una lista di associazioni ID-Valori ed una lista di id, restituisce una
   tupla *)
definition ValueMap_tuple : ∀a. ∀b:(DeqList DeqNat). tuple (getSchema ( selection b ? (a))).
#a #b %
  [@( ( selection b ? ( a)))
  | //
  ]
qed.


(* NOTA: tutte le mappe debbono essere riconvertite in liste, dove gli elementi
  si ottengono non per id k *)

(* Definizione di un campo della tabella *)
record table_record (schema: DeqList DeqType) (Tvaluemap: DeqList DeqCoer) (id:ℕ) : Type[0] ≝ {
  
  (* Lista di id dei valori *)
  Rids   : DeqList DeqNat;
  
  (* Preservazione dello schema *)
  Rprop  : (getSchema (selection  Rids ? Tvaluemap)) = schema;
  Rtuple : tuple schema;
  RLen   : length ? Rids = length ? schema;
  
  (* Corrispondenza tra <chiavi,valoritupla>∈Tvaluemap *)
  Rvalprop: getSchema (selection Rids ? (Sig_fst ? ? Rtuple)) =schema           (*All ? 
           (λp. nth_opt ? (fst ?? p) (Tvaluemap)=Some ? (snd ?? p))
           (compose DeqNat DeqCoer (DeqProd DeqNat DeqCoer) (λx,y. 〈x,y〉) ) *)          

}.

(* Definizione di una tabella, contraddistinta da una particolare mappa di 
   associazione di tipi-etichette *)
record table (Tlabelmap: DeqList DeqType) (Tvaluemap: DeqList DeqCoer) : Type[0] ≝ {
  Tid    : ℕ;                                   (* ID della tabella *)
  Tschema: DeqList DeqType;                     (* Schema della tabella *)
  Tids   : DeqList DeqNat;                      (* Elenco di identificativi dei tipi *)
  cLen   : (length ? Tschema)=(length ? Tids);  (* Le liste hanno stessa lunghezza *)
  
  (* Impongo che le coppie di Tschema-Tids appartengano alla mappa di etichette *)
  cAss   : All ? 
            (λp. nth_opt ? (fst ?? p) (getSchema Tvaluemap)=Some ? (snd ?? p) )
            (compose DeqNat DeqType (DeqProd DeqNat DeqType) (λx,y. 〈x,y〉) Tids Tschema)
           ;
   (* Le tuple devono avere lo stesso schema*)
  Ttuples: list (table_record Tschema Tvaluemap Tid);
  
  
  
  (* Ed in particolare il loro schema *)
  Preserv1: (Tschema=selection Tids DeqType Tlabelmap)
  
  
                 
}.


(* Un database può essere visto come una lista di tabelle descritte come
   sopra *)
record database (Tlabelmap: DeqList DeqType) ( Dvaluemap: DeqList DeqCoer) : Type[0] ≝ {
  DB : list (table Tlabelmap Dvaluemap);
  
  (* Ogni tabella del DB deve avere  ID unico *)          
  DTabUnique : uniqueb ? (map ? DeqNat (λx. Tid ?? x) DB)=true;
  
  (* Per poter riuscire a garantire la unicità delle assoc....*)
  DBTables:  All ? (λp. length ? (Ttuples ?? p) > O) DB
                                                
}.
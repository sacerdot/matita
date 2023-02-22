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

include "projdat/database.ma".

definition eqbD ≝ λD:DeqSet.λa,b:D. eqb D a b.

let rec nomismatch_id (A,B:DeqSet) (l:DeqList (DeqProd A B)) on l ≝
  match l with
  [ nil ⇒ true
  | cons a b ⇒ andb (notb (exists ? (λp. andb (eqbD A (fst ?? a) (fst ?? p)) 
                                              (notb (eqbD ? (snd ?? a) (snd ?? p)))) 
                                  l)) 
                    (nomismatch_id A B b)].


(* Definizione dell'insieme degli archi *)
record HyperEdge (Tlabelmap: DeqList DeqType) (Tvaluemap: DeqList DeqCoer)  : Type[0] ≝ {
  Hid    : ℕ;
  Hids   : DeqList DeqNat;                    (* Lista di id dei valori *)
  HTids  : DeqList DeqNat;                    (* Lista di id dei tipi   *)
  HLen   : (length ? Hids)=(length ? HTids);  (* Le tabelle hanno stessa lunghezza *)
  HPTypes: (getSchema (selection  Hids  ? Tvaluemap))=
           (selection HTids  ? Tlabelmap);
           (* Impongo che agli identificativi di valori corrispondano gli stessi
              tipi *)
  Htuple : tuple (getSchema (selection Hids  ? Tvaluemap))
}.

(* XXX: riscrivibile come Σ-Type *)
(* Definizione dell'insieme degli archi *)
record HyperEdge_SET (Tlabelmap: DeqList DeqType) (Tvaluemap: DeqList DeqCoer) 
                     (HSet: list (HyperEdge Tlabelmap Tvaluemap)) : Type[0] ≝ {
  
  (* XXX: Controllo che ad uno stesso ID corrisponda un unico schema. Garantisce
  l'unicità degli schemi per quello stesso ID ad ogni arco *)
  CheckID_to_Schema: nomismatch_id ?? (map ? ( (DeqProd DeqNat (DeqList DeqType))) 
                              (λx. 〈(Hid ?? x), (selection  (HTids ?? x)?  Tlabelmap)〉) 
                              HSet)
                               =true

}.

(*
definition is_HyperEdge_SET ≝
 (λTlabelmap: DeqList DeqType) (λTvaluemap: DeqList DeqCoer) 
 (λHSet: list (HyperEdge Tlabelmap Tvaluemap)).
  nomismatch_id ?? (map ? ( (DeqProd DeqNat (DeqList DeqType))) 
     (λx. 〈(Hid ?? x), (selection  (HTids ?? x)?  Tlabelmap)〉)  HSet).
*)

(* Definizione dell'ipergrafo *)
record HyperGraph (Tlabelmap : DeqList DeqType) (Nodes : DeqList DeqCoer) : Type[0] ≝ {
   GSet: list (HyperEdge Tlabelmap Nodes);
    (* Lista delle associazioni di tipo *)
    (* Lista delle associazioni di valore *)
   Edges  : HyperEdge_SET Tlabelmap Nodes GSet
}.
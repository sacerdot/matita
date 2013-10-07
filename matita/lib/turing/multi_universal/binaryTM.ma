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

include "turing/mono.ma".

(* given a FinSet F:
   - get its cardinality
   - return its nth element
   - return the index of a given element
 *)
axiom FS_crd : FinSet → nat.
axiom FS_nth : ∀F:FinSet.nat → option F.
axiom index_of_FS : ∀F:FinSet.F → nat.

(* unary bit representation (with a given length) of a certain number *)
axiom unary_of_nat : nat → nat → nat.

axiom FinVector : Type[0] → nat → FinSet.

definition binary_base_states ≝ initN 7.

definition bin0 : binary_base_states ≝ mk_Sig ?? 0 (leb_true_to_le 1 7 (refl …)).
definition bin1 : binary_base_states ≝ mk_Sig ?? 1 (leb_true_to_le 2 7 (refl …)).
definition bin2 : binary_base_states ≝ mk_Sig ?? 2 (leb_true_to_le 3 7 (refl …)).
definition bin3 : binary_base_states ≝ mk_Sig ?? 3 (leb_true_to_le 4 7 (refl …)).
definition bin4 : binary_base_states ≝ mk_Sig ?? 4 (leb_true_to_le 5 7 (refl …)).
definition bin5 : binary_base_states ≝ mk_Sig ?? 5 (leb_true_to_le 6 7 (refl …)).
definition bin6 : binary_base_states ≝ mk_Sig ?? 6 (leb_true_to_le 7 7 (refl …)).

definition states_binaryTM : FinSet → FinSet → FinSet ≝ λsig,states.
 FinProd (FinProd states binary_base_states) 
         (FinProd (FinOption sig) (initN (2 * (FS_crd sig)))).

axiom daemon : ∀T:Type[0].T.
definition initN_pred ≝ λn.λm:initN n.(pred (pi1 … m) : initN n).

(* controllare i contatori, molti andranno incrementati di uno *)
definition trans_binaryTM : ∀sig,states:FinSet.
  (states × (option sig) → states × (option sig) × move) → 
  ((states_binaryTM sig states) × (option bool) → 
   (states_binaryTM sig states) × (option bool) × move) 
≝ λsig,states,trans,p.
  let 〈s,a〉 ≝ p in
  let 〈s0,phase,ch,count〉 ≝ s in
  match pi1 … phase with
  [ O ⇒ (*** PHASE 0: read ***)
      match a with
      [ Some a0 ⇒ 
        match count with
        [ O ⇒ 〈〈s0,1,ch,FS_crd sig〉,None ?,N〉
        | S k ⇒ if (a0 == true) 
                then 〈〈s0,0,FS_nth sig k,k〉, None ?,R〉
                else 〈〈s0,0,ch,k〉,None ?,R〉 ]
      | None ⇒ (* Overflow position! *)
          〈〈s0,4,None ?,0〉,None ?,R〉 ]
  | S phase ⇒ match phase with
  [ O ⇒ (*** PHASE 1: restart ***)
      match count with
      [ O ⇒ 〈〈s0,2,ch,FS_crd sig〉,None ?,N〉
      | S k ⇒ 〈〈s0,1,ch,k〉,None ?,L〉 ]
  | S phase ⇒ match phase with
  [ O ⇒ (*** PHASE 2: write ***)
      let 〈s',a',mv〉 ≝ trans 〈s0,ch〉 in
      match count with
      [ O ⇒ let mv' ≝ match mv with [ R ⇒ N | _ ⇒ L ] in
            let count' ≝ match mv with [ R ⇒ 0 | N ⇒ FS_crd sig | L ⇒ 2*(FS_crd sig) ] in
             〈〈s',3,ch,count'〉,None ?,mv'〉
      | S k ⇒ match a' with
         [ None ⇒ 〈〈s0,2,ch,k〉,None ?,R〉
         | Some a0' ⇒ let out ≝ (FS_nth k == a') in
                      〈〈s0,2,ch,k〉,Some ? out,R〉 ]
      ]
  | S phase ⇒ match phase with
  [ O ⇒ (*** PHASE 3: move head left ***)
      match count with
      [ O ⇒ 〈〈s0,6,ch,O〉, None ?,N〉
      | S k ⇒ 〈〈s0,3,ch,k〉, None ?,L〉 ]
  | S phase ⇒ match phase with
  [ O ⇒ (*** PHASE 4: check position ***)
      match a with
      [ None ⇒ (* niltape/rightof: we can write *) 〈〈s0,2,ch,FS_crd sig〉,None ?,N〉
      | Some _ ⇒ (* leftof *)
        let 〈s',a',mv〉 ≝ trans 〈s0,ch〉 in
        match a' with
        [ None ⇒ (* we don't write anything: go to end of 2 *) 〈〈s0,2,ch,0〉,None ?,N〉
        | Some _ ⇒ (* extend tape *) 〈〈s0,5,ch,FS_crd sig〉,None ?,L〉 ]
      ]
  | S phase ⇒ match phase with
  [ O ⇒ (*** PHASE 5: left extension ***)
      match pi1 … count with
      [ O ⇒ 〈〈s0,bin2,ch,FS_crd sig〉,None ?,N〉
      | S k ⇒ 〈〈s0,bin5,ch,k〉,Some ? false,L〉 ]
  | S _ ⇒ (*** PHASE 6: stop ***) 〈s,None ?,N〉 ]]]]]].  

(*
 * Una mk_binaryTM prende in input una macchina M e produce una macchina che:
 * - ha per alfabeto FinBool
 * - ha stati di tipo (states … M) × (initN 3) × (initN (dimensione dell'alfabeto di M))
 *   dove il primo elemento corrisponde allo stato della macchina input,
 *   il secondo identifica la fase (lettura, scrittura, spostamento)
 *   il terzo è un contatore
 * - (la funzione di transizione è complessa al punto di rendere discutibile 
 *)
definition mk_binaryTM ≝ 
  λsig.λM:TM sig.mk_TM FinBool (FinProd (states … M) (FinProd (initN 3) (initN
{ no_states : nat;
  pos_no_states : (0 < no_states); 
  ntrans : trans_source no_states → trans_target no_states;
  nhalt : initN no_states → bool
}.
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
axiom unary_of_nat : nat → nat → (list bool).

axiom FinVector : Type[0] → nat → FinSet.

definition binary_base_states ≝ initN 6.

definition bin0 : binary_base_states ≝ mk_Sig ?? 0 (leb_true_to_le 1 6 (refl …)).
definition bin1 : binary_base_states ≝ mk_Sig ?? 1 (leb_true_to_le 2 6 (refl …)).
definition bin2 : binary_base_states ≝ mk_Sig ?? 2 (leb_true_to_le 3 6 (refl …)).
definition bin3 : binary_base_states ≝ mk_Sig ?? 3 (leb_true_to_le 4 6 (refl …)).
definition bin4 : binary_base_states ≝ mk_Sig ?? 4 (leb_true_to_le 5 6 (refl …)).
definition bin5 : binary_base_states ≝ mk_Sig ?? 5 (leb_true_to_le 6 6 (refl …)).

definition states_binaryTM : FinSet → FinSet → FinSet ≝ λsig,states.
 FinProd (FinProd states binary_base_states) 
         (FinProd (FinOption sig) (initN (S (2 * (FS_crd sig))))).

axiom daemon : ∀T:Type[0].T.

definition to_initN : ∀n,m.n < m → initN m ≝ λn,m,Hn.mk_Sig … n ….// qed.

definition initN_pred : ∀n.∀m:initN n.initN n ≝ λn,m.mk_Sig … (pred (pi1 … m)) …. 
cases m #m0 /2 by le_to_lt_to_lt/ qed.

(* controllare i contatori, molti andranno incrementati di uno *)
definition trans_binaryTM : ∀sig,states:FinSet.
  (states × (option sig) → states × (option sig) × move) → 
  ((states_binaryTM sig states) × (option bool) → 
   (states_binaryTM sig states) × (option bool) × move) 
≝ λsig,states,trans,p.
  let 〈s,a〉 ≝ p in
  let 〈s0,phase,ch,count〉 ≝ s in
  let (H1 : O < S (2*FS_crd sig)) ≝ ? in
  let (H2 : FS_crd sig < S (2*FS_crd sig)) ≝ ? in
  match pi1 … phase with
  [ O ⇒ (*** PHASE 0: read ***)
      match a with
      [ Some a0 ⇒ 
        match pi1 … count with
        [ O ⇒ 〈〈s0,bin1,ch,to_initN (FS_crd sig) ? H2〉,None ?,N〉
        | S k ⇒ if (a0 == true) 
                then 〈〈s0,bin0,FS_nth sig k,initN_pred … count〉, None ?,R〉
                else 〈〈s0,bin0,ch,initN_pred … count〉,None ?,R〉 ]
      | None ⇒ (* Overflow position! *)
          〈〈s0,bin4,None ?,to_initN 0 ? H1〉,None ?,R〉 ]
  | S phase ⇒ match phase with
  [ O ⇒ (*** PHASE 1: restart ***)
      match pi1 … count with
      [ O ⇒ 〈〈s0,bin2,ch,to_initN (FS_crd sig) ? H2〉,None ?,N〉
      | S k ⇒ 〈〈s0,bin1,ch,initN_pred … count〉,None ?,L〉 ]
  | S phase ⇒ match phase with
  [ O ⇒ (*** PHASE 2: write ***)
      let 〈s',a',mv〉 ≝ trans 〈s0,ch〉 in
      match pi1 … count with
      [ O ⇒ let mv' ≝ match mv with [ R ⇒ N | _ ⇒ L ] in
            let count' ≝ match mv with [ R ⇒ 0 | N ⇒ FS_crd sig | L ⇒ 2*(FS_crd sig) ] in
             〈〈s',bin3,ch,to_initN count' ??〉,None ?,mv'〉
      | S k ⇒ match a' with
         [ None ⇒ 〈〈s0,bin2,ch,initN_pred … count〉,None ?,R〉
         | Some a0' ⇒ let out ≝ (FS_nth ? k == a') in
                      〈〈s0,bin2,ch,initN_pred … count〉,Some ? out,R〉 ]
      ]
  | S phase ⇒ match phase with
  [ O ⇒ (*** PHASE 3: move head left ***)
      match pi1 … count with
      [ O ⇒ 〈〈s0,bin0,None ?,to_initN (FS_crd sig) ? H2〉, None ?,N〉 (* the end: restart *)
      | S k ⇒ 〈〈s0,bin3,ch,initN_pred … count〉, None ?,L〉 ]
  | S phase ⇒ match phase with
  [ O ⇒ (*** PHASE 4: check position ***)
      match a with
      [ None ⇒ (* niltape/rightof: we can write *) 〈〈s0,bin2,ch,to_initN (FS_crd sig) ? H2〉,None ?,N〉
      | Some _ ⇒ (* leftof *)
        let 〈s',a',mv〉 ≝ trans 〈s0,ch〉 in
        match a' with
        [ None ⇒ (* we don't write anything: go to end of 2 *) 〈〈s0,bin2,ch,to_initN 0 ? H1〉,None ?,N〉
        | Some _ ⇒ (* extend tape *) 〈〈s0,bin5,ch,to_initN (FS_crd sig) ? H2〉,None ?,L〉 ]
      ]
  | S _ ⇒ (*** PHASE 5: left extension ***)
      match pi1 … count with
      [ O ⇒ 〈〈s0,bin2,ch,to_initN (FS_crd sig) ? H2〉,None ?,N〉
      | S k ⇒ 〈〈s0,bin5,ch,initN_pred … count〉,Some ? false,L〉 ]]]]]].
[2,3: //]
whd in match count'; cases mv whd in ⊢ (?%?); //
qed.

definition halt_binaryTM : ∀sig,M.states_binaryTM sig (states sig M) → bool ≝ 
  λsig,M,s.let 〈s0,phase,ch,count〉 ≝ s in
  pi1 … phase == O ∧ halt sig M s0.

(*
 * Una mk_binaryTM prende in input una macchina M e produce una macchina che:
 * - ha per alfabeto FinBool
 * - ha stati di tipo ((states … M) × (initN 7)) × 
       ((option sig) × (initN (2*dimensione dell'alfabeto di M + 1))
 *   dove il primo elemento corrisponde allo stato della macchina input,
 *   il secondo identifica la fase (lettura, scrittura, spostamento)
 *   il terzo identifica il carattere oggetto letto
 *   il quarto è un contatore
 * - la funzione di transizione viene prodotta da trans_binaryTM
 * - la funzione di arresto viene prodotta da halt_binaryTM
 *)
definition mk_binaryTM ≝ 
  λsig.λM:TM sig.
  mk_TM FinBool (states_binaryTM sig (states sig M)) 
    (trans_binaryTM sig (states sig M) (trans sig M)) 
    (〈start sig M,bin0,None ?,FS_crd sig〉) (halt_binaryTM sig M).// qed.

definition bin_current ≝ λsig,t.match current ? t with
[ None ⇒ [ ] | Some c ⇒ unary_of_nat (FS_crd sig) (index_of_FS sig c) ].

definition tape_bin_lift ≝ λsig,t.
let ls' ≝ flatten ? (map ?? (unary_of_nat (FS_crd sig) ∘ (index_of_FS sig)) (left ? t)) in
let c' ≝ option_hd ? (bin_current sig t) in
let rs' ≝ tail ? (bin_current sig t)@flatten ? (map ?? (unary_of_nat (FS_crd sig) ∘ (index_of_FS sig)) (right ? t)) in
 mk_tape ? ls' c' rs'.

definition R_bin_lift ≝ λsig,R,t1,t2.
  ∃u1.t1 = tape_bin_lift sig u1 → 
  ∃u2.t2 = tape_bin_lift sig u2 ∧ R u1 u2.
  
definition state_bin_lift :
  ∀sig.∀M:TM sig.states sig M → states ? (mk_binaryTM ? M)
 ≝ λsig,M,q.〈q,bin0,None ?,FS_crd sig〉.// qed.

lemma binaryTM_loop :
 ∀sig,M,i,t,q,tf,qf.
 loopM sig M i (mk_config ?? q t) = Some ? (mk_config ?? qf tf) →
 ∃k.loopM ? (mk_binaryTM sig M) k 
  (mk_config ?? (state_bin_lift ? M q) (tape_bin_lift ? t)) = 
  Some ? (mk_config ?? (state_bin_lift ? M qf) (tape_bin_lift ? tf)).
#sig #M #i elim i
[ #t #q #qf #tf change with (None ?) in ⊢ (??%?→?); #H destruct (H)
| -i #i #IH #t #q #tf #qf


(*
theorem sem_binaryTM : ∀sig,M.
  mk_binaryTM sig M ⊫ R_bin_lift ? (R_TM ? M (start ? M)).
#sig #M #t #i generalize in match t; -t
@(nat_elim1 … i) #m #IH #intape #outc #Hloop

*)
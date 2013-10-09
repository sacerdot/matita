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
      match pi1 … count with
      [ O ⇒ 〈〈s0,bin1,ch,to_initN (FS_crd sig) ? H2〉,None ?,N〉
      | S k ⇒ match a with
        [ Some a0 ⇒ if (a0 == true) 
                    then 〈〈s0,bin0,FS_nth sig k,initN_pred … count〉, None ?,R〉
                    else 〈〈s0,bin0,ch,initN_pred … count〉,None ?,R〉 
        | None ⇒ (* Overflow position! *)
          〈〈s0,bin4,None ?,to_initN 0 ? H1〉,None ?,R〉 ] ]
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

definition bin_char ≝ λsig,ch.unary_of_nat (FS_crd sig) (index_of_FS sig ch).

definition bin_current ≝ λsig,t.match current ? t with
[ None ⇒ [ ] | Some c ⇒ bin_char sig c ].

definition tape_bin_lift ≝ λsig,t.
let ls' ≝ flatten ? (map ?? (bin_char sig) (left ? t)) in
let c' ≝ option_hd ? (bin_current sig t) in
let rs' ≝ tail ? (bin_current sig t)@flatten ? (map ?? (bin_char sig) (right ? t)) in
 mk_tape ? ls' c' rs'.

definition R_bin_lift ≝ λsig,R,t1,t2.
  ∃u1.t1 = tape_bin_lift sig u1 → 
  ∃u2.t2 = tape_bin_lift sig u2 ∧ R u1 u2.
  
definition state_bin_lift :
  ∀sig.∀M:TM sig.states sig M → states ? (mk_binaryTM ? M)
 ≝ λsig,M,q.〈q,bin0,None ?,FS_crd sig〉.// qed.

lemma lift_halt_binaryTM : 
  ∀sig,M,q.halt sig M q = halt ? (mk_binaryTM sig M) (state_bin_lift ? M q).
// qed.

lemma binaryTM_bin0_bin1 :
  ∀sig,M,t,q,ch.
  step ? (mk_binaryTM sig M) (mk_config ?? (〈q,bin0,ch,O〉) t) 
  = mk_config ?? (〈q,bin1,ch,to_initN (FS_crd sig) ??〉) t. //
qed.

lemma binaryTM_bin0_bin4 :
  ∀sig,M,t,q,ch,k.
  current ? t = None ? → S k <S (2*FS_crd sig) → 
  step ? (mk_binaryTM sig M) (mk_config ?? (〈q,bin0,ch,S k〉) t) 
  = mk_config ?? (〈q,bin4,None ?,to_initN 0 ??〉) (tape_move ? t R). [2,3://]
#sig #M #t #q #ch #k #Hcur #Hk
whd in match (step ???); whd in match (trans ???);
>Hcur %
qed.

lemma binaryTM_bin0_true :
  ∀sig,M,t,q,ch,k.
  current ? t = Some ? true → S k <S (2*FS_crd sig) → 
  step ? (mk_binaryTM sig M) (mk_config ?? (〈q,bin0,ch,S k〉) t) 
  = mk_config ?? (〈q,bin0,FS_nth sig k,to_initN k ??〉) (tape_move ? t R).[2,3:/2 by lt_S_to_lt/]
#sig #M #t #q #ch #k #Hcur #Hk
whd in match (step ???); whd in match (trans ???);
>Hcur %
qed.

lemma binaryTM_bin0_false :
  ∀sig,M,t,q,ch,k.
  current ? t = Some ? false → S k <S (2*FS_crd sig) → 
  step ? (mk_binaryTM sig M) (mk_config ?? (〈q,bin0,ch,S k〉) t) 
  = mk_config ?? (〈q,bin0,ch,to_initN k ??〉) (tape_move ? t R).[2,3:/2 by lt_S_to_lt/]
#sig #M #t #q #ch #k #Hcur #Hk
whd in match (step ???); whd in match (trans ???);
>Hcur %
qed.

(* to be checked *)
axiom binary_to_bin_char :∀sig,csl,csr,a.
  csl@true::csr=bin_char sig a → FS_nth ? (length ? csr) = Some ? a.

lemma binaryTM_phase1_midtape_aux :
  ∀sig,M,q,ls,a,rs,k.
  halt sig M q=false → 
  ∀csr,csl,t,ch.length ? csr < S (2*FS_crd sig) → 
  t = mk_tape ? (reverse ? csl@ls) (option_hd ? (csr@rs)) (tail ? (csr@rs)) → 
  csl@csr = bin_char sig a → 
  loopM ? (mk_binaryTM sig M) (S (length ? csr) + k)
    (mk_config ?? (〈q,bin0,ch,length ? csr〉) t) 
  = loopM ? (mk_binaryTM sig M) k 
      (mk_config ?? (〈q,bin1,Some ? a,FS_crd sig〉) 
        (mk_tape ? (reverse ? (bin_char ? a)@ls) (option_hd ? rs) (tail ? rs))). [2,3://]
#sig #M #q #ls #a #rs #k #Hhalt #csr elim csr
[ #csl #t #ch #Hlen #Ht >append_nil #Hcsl >loopM_unfold >loop_S_false [|normalize //]
  <loopM_unfold @eq_f >binaryTM_bin0_bin1 @eq_f >Ht 
  whd in match (step ???); whd in match (trans ???); <Hcsl %
| #c cases c
  [ #csr0 #IH #csl #t #ch #Hlen #Ht #Heq >loopM_unfold >loop_S_false [|normalize //]
    <loopM_unfold lapply (binary_to_bin_char … Heq) #Ha >binaryTM_bin0_true 
    [| >Ht % ]
    lapply (IH (csl@[true]) (tape_move FinBool t R) ????)
    [ //
    | >Ht whd in match (option_hd ??) in ⊢ (??%?); whd in match (tail ??) in ⊢ (??%?);
      cases csr0
      [ cases rs
        [ normalize >rev_append_def >rev_append_def >reverse_append %
        | #r1 #rs1 normalize >rev_append_def >rev_append_def >reverse_append % ]
      | #c1 #csr1 normalize >rev_append_def >rev_append_def >reverse_append % ]
    | /2/
    | @(Some ? a) ]
    #H whd in match (plus ??); >Ha >H @eq_f @eq_f2 //
    
qed.


lemma binaryTM_phase1_midtape :
  ∀sig,M,t,q,ls,a,rs,ch.
  t = mk_tape ? ls (option_hd ? (bin_char ? a)) (tail ? (bin_char sig a@rs)) →
  step ? (mk_binaryTM sig M) (mk_config ?? (〈q,bin0,ch,FS_crd sig〉) t) 
  = mk_config ?? (〈q,bin1,ch,to_initN (FS_crd sig) ??〉) 
      (mk_tape ? (reverse ? (bin_char ? a)@ls) (option_hd ? rs) (tail ? rs)). [2,3://]
#sig #M #t #q #ls #a #rs #ch #Ht
whd in match (step ???); whd in match (trans ???);
>Hcur %
qed.


lemma binaryTM_loop :
 ∀sig,M,i,t,q,tf,qf.
 loopM sig M i (mk_config ?? q t) = Some ? (mk_config ?? qf tf) →
 ∃k.loopM ? (mk_binaryTM sig M) k 
  (mk_config ?? (state_bin_lift ? M q) (tape_bin_lift ? t)) = 
  Some ? (mk_config ?? (state_bin_lift ? M qf) (tape_bin_lift ? tf)).
#sig #M #i elim i
[ #t #q #qf #tf change with (None ?) in ⊢ (??%?→?); #H destruct (H)
| -i #i #IH #t #q #tf #qf
  >loopM_unfold 
  lapply (refl ? (halt sig M (cstate ?? (mk_config ?? q t))))
  cases (halt ?? q) in ⊢ (???%→?); #Hhalt
  [ >(loop_S_true ??? (λc.halt ?? (cstate ?? c)) (mk_config ?? q t) Hhalt)
    #H destruct (H) %{1} >loopM_unfold >loop_S_true // ]
  (* interesting case: more than one step *)
  >(loop_S_false ??? (λc.halt ?? (cstate ?? c)) (mk_config ?? q t) Hhalt)
  <loopM_unfold >(config_expand ?? (step ???)) #Hloop 
  lapply (IH … Hloop) -IH * #k0 #IH <config_expand in Hloop; #Hloop
  %{(S k0)}
  


(*
theorem sem_binaryTM : ∀sig,M.
  mk_binaryTM sig M ⊫ R_bin_lift ? (R_TM ? M (start ? M)).
#sig #M #t #i generalize in match t; -t
@(nat_elim1 … i) #m #IH #intape #outc #Hloop

*)
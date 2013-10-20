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

lemma binaryTM_phase0_midtape_aux :
  ∀sig,M,q,ls,a,rs,k.
  halt sig M q=false → 
  ∀csr,csl,t,ch.length ? csr < S (2*FS_crd sig) → 
  t = mk_tape ? (reverse ? csl@ls) (option_hd ? (csr@rs)) (tail ? (csr@rs)) → 
  csl@csr = bin_char sig a → 
  |csl@csr| = FS_crd sig → 
  (index_of_FS ? a < |csl| → ch = Some ? a) → 
  loopM ? (mk_binaryTM sig M) (S (length ? csr) + k)
    (mk_config ?? (〈q,bin0,ch,length ? csr〉) t) 
  = loopM ? (mk_binaryTM sig M) k 
      (mk_config ?? (〈q,bin1,Some ? a,FS_crd sig〉) 
        (mk_tape ? (reverse ? (bin_char ? a)@ls) (option_hd ? rs) (tail ? rs))). [2,3:/2 by O/]
#sig #M #q #ls #a #rs #k #Hhalt #csr elim csr
[ #csl #t #ch #Hlen #Ht >append_nil #Hcsl #Hlencsl #Hch >loopM_unfold >loop_S_false [|normalize //]
  >Hch [| >Hlencsl (* lemmatize *) @daemon]
  <loopM_unfold @eq_f >binaryTM_bin0_bin1 @eq_f >Ht 
  whd in match (step ???); whd in match (trans ???); <Hcsl %
| #c cases c
  [ #csr0 #IH #csl #t #ch #Hlen #Ht #Heq #Hcrd #Hch >loopM_unfold >loop_S_false [|normalize //]
    <loopM_unfold lapply (binary_to_bin_char … Heq) #Ha >binaryTM_bin0_true 
    [| >Ht % ]
    lapply (IH (csl@[true]) (tape_move FinBool t R) ??????)
    [ //
    | >associative_append @Hcrd
    | >associative_append @Heq
    | >Ht whd in match (option_hd ??) in ⊢ (??%?); whd in match (tail ??) in ⊢ (??%?);
      cases csr0
      [ cases rs
        [ normalize >rev_append_def >rev_append_def >reverse_append %
        | #r1 #rs1 normalize >rev_append_def >rev_append_def >reverse_append % ]
      | #c1 #csr1 normalize >rev_append_def >rev_append_def >reverse_append % ]
    | /2 by lt_S_to_lt/
    |]
    #H whd in match (plus ??); >H @eq_f @eq_f2 %
  | #csr0 #IH #csl #t #ch #Hlen #Ht #Heq #Hcrd #Hch >loopM_unfold >loop_S_false [|normalize //]
    <loopM_unfold >binaryTM_bin0_false [| >Ht % ]
    lapply (IH (csl@[false]) (tape_move FinBool t R) ??????)
    [6: @ch
    | (* by cases: if index < |csl|, then Hch, else False *)
       @daemon
    | >associative_append @Hcrd
    | >associative_append @Heq
    | >Ht whd in match (option_hd ??) in ⊢ (??%?); whd in match (tail ??) in ⊢ (??%?);
      cases csr0
      [ cases rs
        [ normalize >rev_append_def >rev_append_def >reverse_append %
        | #r1 #rs1 normalize >rev_append_def >rev_append_def >reverse_append % ]
      | #c1 #csr1 normalize >rev_append_def >rev_append_def >reverse_append % ]
    | /2 by lt_S_to_lt/
    |]
    #H whd in match (plus ??); >H @eq_f @eq_f2 %
  ]
]
qed.

lemma binaryTM_phase0_midtape :
  ∀sig,M,t,q,ls,a,rs,ch,k.
  halt sig M q=false → 
  t = mk_tape ? ls (option_hd ? (bin_char ? a)) (tail ? (bin_char sig a@rs)) →
  loopM ? (mk_binaryTM sig M) (S (length ? (bin_char ? a)) + k)
    (mk_config ?? (〈q,bin0,ch,length ? (bin_char ? a)〉) t) 
  = loopM ? (mk_binaryTM sig M) k 
      (mk_config ?? (〈q,bin1,Some ? a,FS_crd sig〉) 
        (mk_tape ? (reverse ? (bin_char ? a)@ls) (option_hd ? rs) (tail ? rs))). [|@daemon|//]
#sig #M #t #q #ls #a #rs #ch #k #Hhalt #Ht
cut (∃c,cl.bin_char sig a = c::cl) [@daemon] * #c * #cl #Ha >Ha
>(binaryTM_phase0_midtape_aux ? M q ls a rs ? ? (c::cl) [ ] t ch) //
[| normalize #Hfalse @False_ind cases (not_le_Sn_O ?) /2/
| <Ha (* |bin_char sig ?| = FS_crd sig *) @daemon
| >Ha %
| >Ht >Ha % ]
<Ha %
qed.

lemma binaryTM_phase0_None :
  ∀sig,M,t,q,ch,k,n.
  n < 2*FS_crd sig → 
  halt sig M q=false → 
  current ? t = None ? →
  loopM ? (mk_binaryTM sig M) (S k) (mk_config ?? (〈q,bin0,ch,S n〉) t) 
  = loopM ? (mk_binaryTM sig M) k 
      (mk_config ?? (〈q,bin4,None ?,to_initN O ??〉) (tape_move ? t R)). [2,3: /2 by le_to_lt_to_lt/ ]  
#sig #M #t #q #ch #k #n #Hn #Hhalt cases t
[ >loopM_unfold >loop_S_false [|@Hhalt] //
| #r0 #rs0 >loopM_unfold >loop_S_false [|@Hhalt] //
| #l0 #ls0 >loopM_unfold >loop_S_false [|@Hhalt] //
| #ls #cur #rs normalize in ⊢ (%→?); #H destruct (H) ]
qed.

lemma binaryTM_bin1_O :
  ∀sig,M,t,q,ch.
  step ? (mk_binaryTM sig M) (mk_config ?? (〈q,bin1,ch,O〉) t) 
  = mk_config ?? (〈q,bin2,ch,to_initN (FS_crd sig) ??〉) t. [2,3://]
#sig #M #t #q #ch %
qed.

lemma binaryTM_bin1_S :
  ∀sig,M,t,q,ch,k. S k <S (2*FS_crd sig) → 
  step ? (mk_binaryTM sig M) (mk_config ?? (〈q,bin1,ch,S k〉) t) 
  = mk_config ?? (〈q,bin1,ch,to_initN k ??〉) (tape_move ? t L). [2,3:/2 by lt_S_to_lt/]
#sig #M #t #q #ch #k #HSk %
qed.

lemma binaryTM_phase1 :
  ∀sig,M,q,ls1,ls2,cur,rs,ch,k.
  |ls1| = FS_crd sig → (cur = None ? → rs = [ ]) → 
  loopM ? (mk_binaryTM sig M) (S (FS_crd sig) + k)
    (mk_config ?? (〈q,bin1,ch,FS_crd sig〉) (mk_tape ? (ls1@ls2) cur rs)) 
  = loopM ? (mk_binaryTM sig M) k 
      (mk_config ?? (〈q,bin2,ch,FS_crd sig〉) 
        (mk_tape ? ls2 (option_hd ? (reverse ? ls1@option_cons ? cur rs)) 
          (tail ? (reverse ? ls1@option_cons ? cur rs)))). [2,3:/2 by O/]
cut (∀sig,M,q,ls1,ls2,ch,k,n,cur,rs.
  |ls1| = n →  n<S (2*FS_crd sig) → (cur = None ? → rs = [ ]) → 
  loopM ? (mk_binaryTM sig M) (S n + k)
    (mk_config ?? (〈q,bin1,ch,n〉) (mk_tape ? (ls1@ls2) cur rs)) 
  = loopM ? (mk_binaryTM sig M) k 
      (mk_config ?? (〈q,bin2,ch,FS_crd sig〉) 
        (mk_tape ? ls2 (option_hd ? (reverse ? ls1@option_cons ? cur rs)) 
          (tail ? (reverse ? ls1@option_cons ? cur rs))))) [1,2://]
[ #sig #M #q #ls1 #ls2 #ch #k elim ls1
  [ #n normalize in ⊢ (%→?); #cur #rs #Hn <Hn #Hcrd #Hcur >loopM_unfold >loop_S_false [| % ]
    >binaryTM_bin1_O cases cur in Hcur;
    [ #H >(H (refl ??)) -H %
    | #cur' #_ % ]
  | #l0 #ls0 #IH * [ #cur #rs normalize in ⊢ (%→?); #H destruct (H) ]
    #n #cur #rs normalize in ⊢ (%→?); #H destruct (H) #Hlt #Hcur
    >loopM_unfold >loop_S_false [|%] >binaryTM_bin1_S
    <(?:mk_tape ? (ls0@ls2) (Some ? l0) (option_cons ? cur rs) =
        tape_move FinBool (mk_tape FinBool ((l0::ls0)@ls2) cur rs) L) 
    [| cases cur in Hcur; [ #H >(H ?) // | #cur' #_ % ] ]
    >(?:loop (config FinBool (states FinBool (mk_binaryTM sig M))) (S (|ls0|)+k)
      (step FinBool (mk_binaryTM sig M))
      (λc:config FinBool (states FinBool (mk_binaryTM sig M))
       .halt FinBool (mk_binaryTM sig M)
       (cstate FinBool (states FinBool (mk_binaryTM sig M)) c))
      (mk_config FinBool (states FinBool (mk_binaryTM sig M))
       〈q,bin1,ch,to_initN (|ls0|) (S (2*FS_crd sig))
        (lt_S_to_lt (|ls0|) (S (2*FS_crd sig)) Hlt)〉
       (mk_tape FinBool (ls0@ls2) (Some FinBool l0) (option_cons FinBool cur rs)))
      = loopM FinBool (mk_binaryTM sig M) k
         (mk_config FinBool (states FinBool (mk_binaryTM sig M))
          〈q,bin2,〈ch,FS_crd sig〉〉
          (mk_tape FinBool ls2
           (option_hd FinBool (reverse FinBool ls0@l0::option_cons FinBool cur rs))
           (tail FinBool (reverse FinBool ls0@l0::option_cons FinBool cur rs)))))
    [| /2/
    | >(?: l0::option_cons ? cur rs = option_cons ? (Some ? l0) (option_cons ? cur rs)) [| % ]
      @trans_eq [|| @(IH ??? (refl ??)) [ /2 by lt_S_to_lt/ | #H destruct (H) ] ]
      %
    ]
   >reverse_cons >associative_append %
 ]
| #Hcut #sig #M #q #ls1 #ls2 #cur #rs #ch #k #Hlen @Hcut // ]
qed.

lemma binaryTM_bin2_O_L :
  ∀sig,M,t,q,qn,ch,chn.
  〈qn,chn,L〉 = trans sig M 〈q,ch〉 → 
  step ? (mk_binaryTM sig M) (mk_config ?? (〈q,bin2,ch,O〉) t)
  = mk_config ?? (〈qn,bin3,ch,to_initN (2*(FS_crd sig)) ??〉) (tape_move ? t L).[2,3:/2 by lt_S_to_lt/]
#sig #M #t #q #qn #ch #chn #Htrans
whd in match (step ???); whd in match (trans ???); <Htrans %
qed.

lemma binaryTM_bin2_O_R :
  ∀sig,M,t,q,qn,ch,chn.
  〈qn,chn,R〉 = trans sig M 〈q,ch〉 → 
  step ? (mk_binaryTM sig M) (mk_config ?? (〈q,bin2,ch,O〉) t)
  = mk_config ?? (〈qn,bin3,ch,to_initN O ??〉) t.[2,3://]
#sig #M #t #q #qn #ch #chn #Htrans
whd in match (step ???); whd in match (trans ???); <Htrans %
qed.

lemma binaryTM_bin2_O_N :
  ∀sig,M,t,q,qn,ch,chn.
  〈qn,chn,N〉 = trans sig M 〈q,ch〉 → 
  step ? (mk_binaryTM sig M) (mk_config ?? (〈q,bin2,ch,O〉) t)
  = mk_config ?? (〈qn,bin3,ch,to_initN (FS_crd sig) ??〉) (tape_move ? t L).[2,3:/2 by lt_S_to_lt/]
#sig #M #t #q #qn #ch #chn #Htrans
whd in match (step ???); whd in match (trans ???); <Htrans %
qed.

lemma binaryTM_bin2_S_None :
  ∀sig,M,t,q,qn,ch,mv,k.
  k< 2*FS_crd sig → 
  〈qn,None ?,mv〉 = trans sig M 〈q,ch〉 → 
  step ? (mk_binaryTM sig M) (mk_config ?? (〈q,bin2,ch,S k〉) t)
  = mk_config ?? (〈q,bin2,ch,k〉) (tape_move ? t R).
[2,3:/2 by le_to_lt_to_lt, transitive_lt/]
#sig #M #t #q #qn #ch #mv #k #Hk #Htrans
whd in match (step ???); whd in match (trans ???); <Htrans %
qed.

lemma binaryTM_bin2_S_Some :
  ∀sig,M,t,q,qn,ch,chn,mv,k.
  k< 2*FS_crd sig → 
  〈qn,Some ? chn,mv〉 = trans sig M 〈q,ch〉 → 
  step ? (mk_binaryTM sig M) (mk_config ?? (〈q,bin2,ch,S k〉) t)
  = mk_config ?? (〈q,bin2,ch,k〉) (tape_move ? (tape_write ? t (Some ? (FS_nth ? k == Some ? chn))) R).
[2,3:/2 by le_to_lt_to_lt, transitive_lt/]
#sig #M #t #q #qn #ch #chn #mv #k #Hk #Htrans
whd in match (step ???); whd in match (trans ???); <Htrans %
qed.

lemma binaryTM_phase2_Some_R :∀sig,M,q,ch,qn,chn,ls,rs,k,csr.
  〈qn,Some ? chn,R〉 = trans sig M 〈q,ch〉 → 
  ∀cur,csl. |cur::csr|<S (2*FS_crd sig) → 
  |csl@cur::csr| = FS_crd sig →
  (∃fs.bin_char sig chn = reverse ? csl@fs) → 
  loopM ? (mk_binaryTM sig M) (S (|cur::csr|) + k)
    (mk_config ?? (〈q,bin2,ch,|cur::csr|〉) (midtape ? (csl@ls) cur (csr@rs))) 
  = loopM ? (mk_binaryTM sig M) k 
      (mk_config ?? (〈qn,bin3,ch,O〉) 
        (mk_tape ? (reverse ? (bin_char sig chn)@ls) (option_hd ? rs) (tail ? rs))). [2,3://]
#sig #M #q #ch #qn #chn #ls #rs #k #csr #Htrans elim csr
[ #cur #csl #Hcount #Hcrd * #fs #Hfs >loopM_unfold >loop_S_false // normalize in match (length ? [cur]);
  >(binaryTM_bin2_S_Some … Htrans) [| /2 by monotonic_pred/ ]
  >loop_S_false // @eq_f >(binaryTM_bin2_O_R … Htrans)
  @eq_f change with (midtape ? (csl@ls) (FS_nth sig O == Some ? chn) rs) in match (tape_write ???);
  cut (bin_char sig chn = reverse ? csl@[FS_nth sig O == Some sig chn]) [@daemon] #Hfs' >Hfs'
  >reverse_append >reverse_single >reverse_reverse >associative_append
  cases rs //
| #b0 #bs0 #IH #cur #csl #Hcount #Hcrd * #fs #Hfs
  >loopM_unfold >loop_S_false // >(binaryTM_bin2_S_Some … Htrans) [| @le_S_S_to_le @Hcount ]
  change with (midtape ? (((FS_nth ? (|b0::bs0|)==Some sig chn)::csl)@ls) b0 (bs0@rs)) 
    in match (tape_move ? (tape_write ???) ?); @IH
  [ <Hcrd >length_append >length_append normalize //
  | cases fs in Hfs;
    [ #Hfalse cut (|bin_char ? chn| = |csl|) [ >Hfalse >length_append >length_reverse // ]
      -Hfalse >(?:|bin_char sig chn| = FS_crd sig) [|@daemon]
      <Hcrd >length_append normalize >(?:|csl| = |csl|+ O) in ⊢ (???%→?); //
      #Hfalse cut (S (S (|bs0|)) = O) /2 by injective_plus_r/ #H destruct (H)
    | #f0 #fs0 #Hbinchar 
      cut (bin_char ? chn = reverse ? csl@(FS_nth ? (|b0::bs0|) == Some ? chn)::fs0) [@daemon]
      -Hbinchar #Hbinchar >Hbinchar %{fs0} >reverse_cons >associative_append %
    ]
  ]
]
qed.

lemma binaryTM_phase2_Some_L :∀sig,M,q,ch,qn,chn,ls,rs,k,csr.
  〈qn,Some ? chn,L〉 = trans sig M 〈q,ch〉 → 
  ∀cur,csl. |cur::csr|<S (2*FS_crd sig) → 
  |csl@cur::csr| = FS_crd sig →
  (∃fs.bin_char sig chn = reverse ? csl@fs) → 
  loopM ? (mk_binaryTM sig M) (S (|cur::csr|) + k)
    (mk_config ?? (〈q,bin2,ch,|cur::csr|〉) (midtape ? (csl@ls) cur (csr@rs))) 
  = loopM ? (mk_binaryTM sig M) k 
      (mk_config ?? (〈qn,bin3,ch,to_initN (2*FS_crd sig) ??〉) 
        (tape_move ? (mk_tape ? (reverse ? (bin_char sig chn)@ls) (option_hd ? rs) (tail ? rs)) L)). [2,3://]
#sig #M #q #ch #qn #chn #ls #rs #k #csr #Htrans elim csr
[ #cur #csl #Hcount #Hcrd * #fs #Hfs >loopM_unfold >loop_S_false // normalize in match (length ? [cur]);
  >(binaryTM_bin2_S_Some … Htrans) [| /2 by monotonic_pred/ ]
  >loop_S_false // @eq_f >(binaryTM_bin2_O_L … Htrans)
  @eq_f change with (midtape ? (csl@ls) (FS_nth sig O == Some ? chn) rs) in match (tape_write ???);
  cut (bin_char sig chn = reverse ? csl@[FS_nth sig O == Some sig chn]) [@daemon] #Hfs' >Hfs'
  >reverse_append >reverse_single >reverse_reverse >associative_append @eq_f2 //
  cases rs //
| #b0 #bs0 #IH #cur #csl #Hcount #Hcrd * #fs #Hfs
  >loopM_unfold >loop_S_false // >(binaryTM_bin2_S_Some … Htrans) [| @le_S_S_to_le @Hcount ]
  change with (midtape ? (((FS_nth ? (|b0::bs0|)==Some sig chn)::csl)@ls) b0 (bs0@rs)) 
    in match (tape_move ? (tape_write ???) ?); @IH
  [ <Hcrd >length_append >length_append normalize //
  | cases fs in Hfs;
    [ #Hfalse cut (|bin_char ? chn| = |csl|) [ >Hfalse >length_append >length_reverse // ]
      -Hfalse >(?:|bin_char sig chn| = FS_crd sig) [|@daemon]
      <Hcrd >length_append normalize >(?:|csl| = |csl|+ O) in ⊢ (???%→?); //
      #Hfalse cut (S (S (|bs0|)) = O) /2 by injective_plus_r/ #H destruct (H)
    | #f0 #fs0 #Hbinchar 
      cut (bin_char ? chn = reverse ? csl@(FS_nth ? (|b0::bs0|) == Some ? chn)::fs0) [@daemon]
      -Hbinchar #Hbinchar >Hbinchar %{fs0} >reverse_cons >associative_append %
    ]
  ]
]
qed.

lemma binaryTM_phase2_Some_N :∀sig,M,q,ch,qn,chn,ls,rs,k,csr.
  〈qn,Some ? chn,N〉 = trans sig M 〈q,ch〉 → 
  ∀cur,csl. |cur::csr|<S (2*FS_crd sig) → 
  |csl@cur::csr| = FS_crd sig →
  (∃fs.bin_char sig chn = reverse ? csl@fs) → 
  loopM ? (mk_binaryTM sig M) (S (|cur::csr|) + k)
    (mk_config ?? (〈q,bin2,ch,|cur::csr|〉) (midtape ? (csl@ls) cur (csr@rs))) 
  = loopM ? (mk_binaryTM sig M) k 
      (mk_config ?? (〈qn,bin3,ch,to_initN (FS_crd sig) ??〉) 
        (tape_move ? (mk_tape ? (reverse ? (bin_char sig chn)@ls) (option_hd ? rs) (tail ? rs)) L)). [2,3://]
#sig #M #q #ch #qn #chn #ls #rs #k #csr #Htrans elim csr
[ #cur #csl #Hcount #Hcrd * #fs #Hfs >loopM_unfold >loop_S_false // normalize in match (length ? [cur]);
  >(binaryTM_bin2_S_Some … Htrans) [| /2 by monotonic_pred/ ]
  >loop_S_false // @eq_f >(binaryTM_bin2_O_N … Htrans)
  @eq_f change with (midtape ? (csl@ls) (FS_nth sig O == Some ? chn) rs) in match (tape_write ???);
  cut (bin_char sig chn = reverse ? csl@[FS_nth sig O == Some sig chn]) [@daemon] #Hfs' >Hfs'
  >reverse_append >reverse_single >reverse_reverse >associative_append @eq_f2 //
  cases rs //
| #b0 #bs0 #IH #cur #csl #Hcount #Hcrd * #fs #Hfs
  >loopM_unfold >loop_S_false // >(binaryTM_bin2_S_Some … Htrans) [| @le_S_S_to_le @Hcount ]
  change with (midtape ? (((FS_nth ? (|b0::bs0|)==Some sig chn)::csl)@ls) b0 (bs0@rs)) 
    in match (tape_move ? (tape_write ???) ?); @IH
  [ <Hcrd >length_append >length_append normalize //
  | cases fs in Hfs;
    [ #Hfalse cut (|bin_char ? chn| = |csl|) [ >Hfalse >length_append >length_reverse // ]
      -Hfalse >(?:|bin_char sig chn| = FS_crd sig) [|@daemon]
      <Hcrd >length_append normalize >(?:|csl| = |csl|+ O) in ⊢ (???%→?); //
      #Hfalse cut (S (S (|bs0|)) = O) /2 by injective_plus_r/ #H destruct (H)
    | #f0 #fs0 #Hbinchar 
      cut (bin_char ? chn = reverse ? csl@(FS_nth ? (|b0::bs0|) == Some ? chn)::fs0) [@daemon]
      -Hbinchar #Hbinchar >Hbinchar %{fs0} >reverse_cons >associative_append %
    ]
  ]
]
qed.

lemma binaryTM_phase2_None_R :∀sig,M,q,ch,qn,ls,rs,k,csr.
  〈qn,None ?,R〉 = trans sig M 〈q,ch〉 → 
  ∀cur,csl. |cur::csr|<S (2*FS_crd sig) → 
  |csl@cur::csr| = FS_crd sig →
  loopM ? (mk_binaryTM sig M) (S (|cur::csr|) + k)
    (mk_config ?? (〈q,bin2,ch,|cur::csr|〉) (midtape ? (csl@ls) cur (csr@rs))) 
  = loopM ? (mk_binaryTM sig M) k 
      (mk_config ?? (〈qn,bin3,ch,O〉) 
        (mk_tape ? (reverse ? csr@cur::csl@ls) (option_hd ? rs) (tail ? rs))). [2,3://]
#sig #M #q #ch #qn #ls #rs #k #csr #Htrans elim csr
[ #cur #csl #Hcount #Hcrd >loopM_unfold >loop_S_false // normalize in match (length ? [cur]);
  >(binaryTM_bin2_S_None … Htrans) [| /2 by monotonic_pred/ ]
  >loop_S_false // @eq_f >(binaryTM_bin2_O_R … Htrans)
  @eq_f cases rs //
| #b0 #bs0 #IH #cur #csl #Hcount #Hcrd
  >loopM_unfold >loop_S_false // >(binaryTM_bin2_S_None … Htrans) [| @le_S_S_to_le @Hcount ]
  change with (midtape ? ((cur::csl)@ls) b0 (bs0@rs)) 
    in match (tape_move ???); >reverse_cons >associative_append 
    normalize in match ([b0]@cur::csl@ls); @IH 
  <Hcrd >length_append >length_append normalize //
]
qed.

lemma binaryTM_phase2_None_L : ∀sig,M,q,ch,qn,ls,rs,k,csr.
  〈qn,None ?,L〉 = trans sig M 〈q,ch〉 → 
  ∀cur,csl. |cur::csr|<S (2*FS_crd sig) → 
  |csl@cur::csr| = FS_crd sig →
  loopM ? (mk_binaryTM sig M) (S (|cur::csr|) + k)
    (mk_config ?? (〈q,bin2,ch,|cur::csr|〉) (midtape ? (csl@ls) cur (csr@rs))) 
  = loopM ? (mk_binaryTM sig M) k 
      (mk_config ?? (〈qn,bin3,ch,to_initN (2*FS_crd sig) ??〉) 
        (tape_move ? (mk_tape ? (reverse ? csr@cur::csl@ls) (option_hd ? rs) (tail ? rs)) L)). [2,3://]
#sig #M #q #ch #qn #ls #rs #k #csr #Htrans elim csr
[ #cur #csl #Hcount #Hcrd >loopM_unfold >loop_S_false // normalize in match (length ? [cur]);
  >(binaryTM_bin2_S_None … Htrans) [| /2 by monotonic_pred/ ]
  >loop_S_false // @eq_f >(binaryTM_bin2_O_L … Htrans)
  @eq_f cases rs //
| #b0 #bs0 #IH #cur #csl #Hcount #Hcrd
  >loopM_unfold >loop_S_false // >(binaryTM_bin2_S_None … Htrans) [| @le_S_S_to_le @Hcount ]
  change with (midtape ? ((cur::csl)@ls) b0 (bs0@rs)) 
    in match (tape_move ???); >reverse_cons >associative_append 
    normalize in match ([b0]@cur::csl@ls); @IH 
  <Hcrd >length_append >length_append normalize //
]
qed.

lemma binaryTM_phase2_None_N :∀sig,M,q,ch,qn,ls,rs,k,csr.
  〈qn,None ?,N〉 = trans sig M 〈q,ch〉 → 
  ∀cur,csl. |cur::csr|<S (2*FS_crd sig) → 
  |csl@cur::csr| = FS_crd sig →
  loopM ? (mk_binaryTM sig M) (S (|cur::csr|) + k)
    (mk_config ?? (〈q,bin2,ch,|cur::csr|〉) (midtape ? (csl@ls) cur (csr@rs))) 
  = loopM ? (mk_binaryTM sig M) k 
      (mk_config ?? (〈qn,bin3,ch,to_initN (FS_crd sig) ??〉) 
        (tape_move ? (mk_tape ? (reverse ? csr@cur::csl@ls) (option_hd ? rs) (tail ? rs)) L)). [2,3://]
#sig #M #q #ch #qn #ls #rs #k #csr #Htrans elim csr
[ #cur #csl #Hcount #Hcrd >loopM_unfold >loop_S_false // normalize in match (length ? [cur]);
  >(binaryTM_bin2_S_None … Htrans) [| /2 by monotonic_pred/ ]
  >loop_S_false // @eq_f >(binaryTM_bin2_O_N … Htrans)
  @eq_f cases rs //
| #b0 #bs0 #IH #cur #csl #Hcount #Hcrd
  >loopM_unfold >loop_S_false // >(binaryTM_bin2_S_None … Htrans) [| @le_S_S_to_le @Hcount ]
  change with (midtape ? ((cur::csl)@ls) b0 (bs0@rs)) 
    in match (tape_move ???); >reverse_cons >associative_append 
    normalize in match ([b0]@cur::csl@ls); @IH 
  <Hcrd >length_append >length_append normalize //
]
qed.

lemma binaryTM_bin3_O :
  ∀sig,M,t,q,ch.
  step ? (mk_binaryTM sig M) (mk_config ?? (〈q,bin3,ch,O〉) t) 
  = mk_config ?? (〈q,bin0,None ?,to_initN (FS_crd sig) ??〉) t. [2,3://]
#sig #M #t #q #ch %
qed.

lemma binaryTM_bin3_S :
  ∀sig,M,t,q,ch,k. S k <S (2*FS_crd sig) → 
  step ? (mk_binaryTM sig M) (mk_config ?? (〈q,bin3,ch,S k〉) t) 
  = mk_config ?? (〈q,bin3,ch,to_initN k ??〉) (tape_move ? t L). [2,3:/2 by lt_S_to_lt/]
#sig #M #t #q #ch #k #HSk %
qed.

lemma binaryTM_phase3 :∀sig,M,q,ls1,ls2,ch,k,n,cur,rs.
  |ls1| = n →  n<S (2*FS_crd sig) → (cur = None ? → rs = [ ]) → 
  loopM ? (mk_binaryTM sig M) (S n + k)
    (mk_config ?? (〈q,bin3,ch,n〉) (mk_tape ? (ls1@ls2) cur rs)) 
  = loopM ? (mk_binaryTM sig M) k 
      (mk_config ?? (〈q,bin0,None ?,FS_crd sig〉) 
        (mk_tape ? ls2 (option_hd ? (reverse ? ls1@option_cons ? cur rs)) 
          (tail ? (reverse ? ls1@option_cons ? cur rs)))). [2,3://]
#sig #M #q #ls1 #ls2 #ch #k elim ls1
[ #n normalize in ⊢ (%→?); #cur #rs #Hn <Hn #Hcrd #Hcur >loopM_unfold >loop_S_false [| % ]
  >binaryTM_bin3_O cases cur in Hcur;
  [ #H >(H (refl ??)) -H %
  | #cur' #_ % ]
| #l0 #ls0 #IH * [ #cur #rs normalize in ⊢ (%→?); #H destruct (H) ]
  #n #cur #rs normalize in ⊢ (%→?); #H destruct (H) #Hlt #Hcur
  >loopM_unfold >loop_S_false [|%] >binaryTM_bin3_S
  <(?:mk_tape ? (ls0@ls2) (Some ? l0) (option_cons ? cur rs) =
      tape_move FinBool (mk_tape FinBool ((l0::ls0)@ls2) cur rs) L) 
  [| cases cur in Hcur; [ #H >(H ?) // | #cur' #_ % ] ]
  >(?:loop (config FinBool (states FinBool (mk_binaryTM sig M))) (S (|ls0|)+k)
    (step FinBool (mk_binaryTM sig M))
    (λc:config FinBool (states FinBool (mk_binaryTM sig M))
     .halt FinBool (mk_binaryTM sig M)
     (cstate FinBool (states FinBool (mk_binaryTM sig M)) c))
    (mk_config FinBool (states FinBool (mk_binaryTM sig M))
     〈q,bin3,ch,to_initN (|ls0|) (S (2*FS_crd sig))
      (lt_S_to_lt (|ls0|) (S (2*FS_crd sig)) Hlt)〉
     (mk_tape FinBool (ls0@ls2) (Some FinBool l0) (option_cons FinBool cur rs)))
    = loopM FinBool (mk_binaryTM sig M) k
       (mk_config FinBool (states FinBool (mk_binaryTM sig M))
        〈q,bin0,〈None ?,FS_crd sig〉〉
        (mk_tape FinBool ls2
         (option_hd FinBool (reverse FinBool ls0@l0::option_cons FinBool cur rs))
         (tail FinBool (reverse FinBool ls0@l0::option_cons FinBool cur rs)))))
  [| /2/
  | >(?: l0::option_cons ? cur rs = option_cons ? (Some ? l0) (option_cons ? cur rs)) [| % ]
    @trans_eq [|| @(IH ??? (refl ??)) [ /2 by lt_S_to_lt/ | #H destruct (H) ] ]
    %
  ]
 >reverse_cons >associative_append %
]
qed.

lemma binaryTM_bin4_None :
  ∀sig,M,t,q,ch.
  current ? t = None ? → 
  step ? (mk_binaryTM sig M) (mk_config ?? (〈q,bin4,ch,O〉) t) 
  = mk_config ?? (〈q,bin2,ch,to_initN (FS_crd sig) ??〉) t. [2,3://]
#sig #M #t #q #ch #Hcur whd in ⊢ (??%?); >Hcur %
qed.

lemma binaryTM_bin4_noextend :
  ∀sig,M,t,q,ch,cur,qn,mv.
  current ? t = Some ? cur → 
  〈qn,None ?,mv〉 = trans sig M 〈q,ch〉 → 
  step ? (mk_binaryTM sig M) (mk_config ?? (〈q,bin4,ch,O〉) t) 
  = mk_config ?? (〈q,bin2,ch,to_initN O ??〉) t. [2,3://]
#sig #M #t #q #ch #cur #qn #mv #Hcur #Htrans
whd in ⊢ (??%?); >Hcur whd in ⊢ (??%?);
whd in match (trans FinBool ??); <Htrans %
qed.

lemma binaryTM_bin4_extend :
  ∀sig,M,t,q,ch,cur,qn,an,mv.
  current ? t = Some ? cur → 
  〈qn,Some ? an,mv〉 = trans sig M 〈q,ch〉 → 
  step ? (mk_binaryTM sig M) (mk_config ?? (〈q,bin4,ch,O〉) t) 
  = mk_config ?? (〈q,bin5,ch,to_initN (FS_crd sig) ??〉) (tape_move ? t L). [2,3://]
#sig #M #t #q #ch #cur #qn #an #mv #Hcur #Htrans
whd in ⊢ (??%?); >Hcur whd in ⊢ (??%?);
whd in match (trans FinBool ??); <Htrans %
qed.

lemma binaryTM_bin5_O :
  ∀sig,M,t,q,ch.
  step ? (mk_binaryTM sig M) (mk_config ?? (〈q,bin5,ch,O〉) t) 
  = mk_config ?? (〈q,bin2,ch,to_initN (FS_crd sig) ??〉) t. [2,3://]
#sig #M #t #q #ch %
qed.

lemma binaryTM_bin5_S :
  ∀sig,M,t,q,ch,k. S k <S (2*FS_crd sig) → 
  step ? (mk_binaryTM sig M) (mk_config ?? (〈q,bin5,ch,S k〉) t) 
  = mk_config ?? (〈q,bin5,ch,to_initN k ??〉) (tape_move ? (tape_write ? t (Some ? false)) L). [2,3:/2 by lt_S_to_lt/]
#sig #M #t #q #ch #k #HSk %
qed.

(* extends the tape towards the left with an unimportant sequence that will be
   immediately overwritten *)
lemma binaryTM_phase5 :∀sig,M,q,ch,k,n,rs.
  n<S (2*FS_crd sig) →
  ∃bs.|bs| = n ∧
  loopM ? (mk_binaryTM sig M) (S n + k)
    (mk_config ?? (〈q,bin5,ch,n〉) (mk_tape ? [] (None ?) rs)) 
  = loopM ? (mk_binaryTM sig M) k 
      (mk_config ?? (〈q,bin2,ch,FS_crd sig〉) 
        (mk_tape ? [] (None ?) (bs@rs))). [2,3://]
#sig #M #q #ch #k #n elim n
[ #rs #Hlt %{[]} % %
| #n0 #IH #rs #Hn0 cases (IH (false::rs) ?) [|/2 by lt_S_to_lt/] 
  #bs * #Hbs -IH #IH
  %{(bs@[false])} % [ <Hbs >length_append /2 by plus_to_minus/ ]
  >loopM_unfold >loop_S_false // >binaryTM_bin5_S
  >associative_append normalize in match ([false]@?); <IH
  >loopM_unfold @eq_f @eq_f cases rs //
]
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
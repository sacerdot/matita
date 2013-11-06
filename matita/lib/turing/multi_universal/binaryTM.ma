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
         (FinProd (FinOption sig) (initN (S (S (2 * (FS_crd sig)))))).

axiom daemon : ∀T:Type[0].T.

definition to_initN : ∀n,m.n < m → initN m ≝ λn,m,Hn.mk_Sig … n ….// qed.

definition initN_pred : ∀n.∀m:initN n.initN n ≝ λn,m.mk_Sig … (pred (pi1 … m)) …. 
cases m #m0 /2 by le_to_lt_to_lt/ qed.

definition displ_of_move ≝ λsig,mv.
  match mv with
  [ L ⇒ 2*FS_crd sig
  | N ⇒ FS_crd sig
  | R ⇒ O ].
  
lemma le_displ_of_move : ∀sig,mv.displ_of_move sig mv ≤ S (2*FS_crd sig).
#sig * /2 by le_S/
qed.

definition displ2_of_move ≝ λsig,mv.
  match mv with
  [ L ⇒ FS_crd sig
  | N ⇒ O
  | R ⇒ O ].
  
lemma le_displ2_of_move : ∀sig,mv.displ2_of_move sig mv ≤ S (2*FS_crd sig).
#sig * /2 by lt_to_le/
qed.

definition mv_tech ≝ λmv.match mv with [ N ⇒ N | _ ⇒ R ].

definition trans_binaryTM : ∀sig,states:FinSet.
  (states × (option sig) → states × (option sig) × move) → 
  ((states_binaryTM sig states) × (option bool) → 
   (states_binaryTM sig states) × (option bool) × move) 
≝ λsig,states,trans,p.
  let 〈s,a〉 ≝ p in
  let 〈s0,phase,ch,count〉 ≝ s in
  let (H1 : O < S (S (2*FS_crd sig))) ≝ ? in
  let (H2 : FS_crd sig < S (S (2*FS_crd sig))) ≝ ? in
  match pi1 … phase with
  [ O ⇒ (*** PHASE 0: read ***)
      match pi1 … count with
      [ O ⇒ 〈〈s0,bin1,ch,to_initN (FS_crd sig) ? H2〉,None ?,N〉
      | S k ⇒ match a with
        [ Some a0 ⇒ if (a0 == true) 
                    then 〈〈s0,bin0,FS_nth sig k,initN_pred … count〉, None ?,R〉
                    else 〈〈s0,bin0,ch,initN_pred … count〉,None ?,R〉 
        | None ⇒ (* Overflow position! *)
          let 〈s',a',mv〉 ≝ trans 〈s0,None ?〉 in
          match a' with
          [ None ⇒ (* we don't write anything: go to end of 3 *) 〈〈s',bin3,None ?,to_initN (displ2_of_move sig mv) ??〉,None ?,mv_tech mv〉
          | Some _ ⇒ (* maybe extend tape *) 〈〈s0,bin4,None ?,to_initN O ? H1〉,None ?,R〉 ] ] ]
  | S phase ⇒ match phase with
  [ O ⇒ (*** PHASE 1: restart ***)
      match pi1 … count with
      [ O ⇒ 〈〈s0,bin2,ch,to_initN (FS_crd sig) ? H2〉,None ?,N〉
      | S k ⇒ 〈〈s0,bin1,ch,initN_pred … count〉,None ?,L〉 ]
  | S phase ⇒ match phase with
  [ O ⇒ (*** PHASE 2: write ***)
      let 〈s',a',mv〉 ≝ trans 〈s0,ch〉 in
      match pi1 … count with
      [ O ⇒ 〈〈s',bin3,ch,to_initN (displ_of_move sig mv) ??〉,None ?,N〉
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
        [ None ⇒ (* (vacuous) go to end of 2 *) 〈〈s0,bin2,ch,to_initN 0 ? H1〉,None ?,N〉
        | Some _ ⇒ (* extend tape *) 〈〈s0,bin5,ch,to_initN (FS_crd sig) ? H2〉,None ?,L〉 ]
      ]
  | S _ ⇒ (*** PHASE 5: left extension ***)
      match pi1 … count with
      [ O ⇒ 〈〈s0,bin2,ch,to_initN (FS_crd sig) ? H2〉,None ?,R〉
      | S k ⇒ 〈〈s0,bin5,ch,initN_pred … count〉,Some ? false,L〉 ]]]]]].
[ /2 by le_to_lt_to_lt/ | /2 by le_S_S/ |*: /2 by lt_S_to_lt/]
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
    (〈start sig M,bin0,None ?,FS_crd sig〉) (halt_binaryTM sig M). 
/2 by lt_S_to_lt/ qed.

definition bin_char ≝ λsig,ch.unary_of_nat (FS_crd sig) (index_of_FS sig ch).

definition opt_bin_char ≝ λsig,c.match c with
[ None ⇒ [ ] | Some c0 ⇒ bin_char sig c0 ].

definition bin_list ≝ λsig,l.flatten ? (map ?? (bin_char sig) l).
definition rev_bin_list ≝ λsig,l.flatten ? (map ?? (λc.reverse ? (bin_char sig c)) l).

definition tape_bin_lift ≝ λsig,t.
let ls' ≝ rev_bin_list ? (left ? t) in
let c' ≝ option_hd ? (opt_bin_char sig (current ? t)) in
let rs' ≝ (tail ? (opt_bin_char sig (current ? t))@bin_list ? (right ? t)) in
 mk_tape ? ls' c' rs'.

definition state_bin_lift :
  ∀sig.∀M:TM sig.states sig M → states ? (mk_binaryTM ? M)
 ≝ λsig,M,q.〈q,bin0,None ?,FS_crd sig〉./2 by lt_S_to_lt/ qed.

lemma lift_halt_binaryTM : 
  ∀sig,M,q.halt sig M q = halt ? (mk_binaryTM sig M) (state_bin_lift ? M q).
// qed.

lemma binaryTM_bin0_bin1 :
  ∀sig,M,t,q,ch.
  step ? (mk_binaryTM sig M) (mk_config ?? (〈q,bin0,ch,O〉) t) 
  = mk_config ?? (〈q,bin1,ch,to_initN (FS_crd sig) ??〉) t. //
qed.

lemma binaryTM_bin0_bin3 :
  ∀sig,M,t,q,ch,k,qn,mv.
  current ? t = None ? → S k <S (2*FS_crd sig) → 
  〈qn,None ?,mv〉 = trans sig M 〈q,None ?〉 → 
  step ? (mk_binaryTM sig M) (mk_config ?? (〈q,bin0,ch,S k〉) t) 
  = mk_config ?? (〈qn,bin3,None ?,to_initN (displ2_of_move sig mv) ??〉) (tape_move ? t (mv_tech mv)). [|@le_S //|@le_S_S @le_displ2_of_move]
#sig #M #t #q #ch #k #qn #mv #Hcur #Hk #Htrans
whd in match (step ???); whd in match (trans ???);
>Hcur <Htrans %
qed.

lemma binaryTM_bin0_bin4 :
  ∀sig,M,t,q,ch,k,qn,chn,mv.
  current ? t = None ? → S k <S (2*FS_crd sig) → 
  〈qn,Some ? chn,mv〉 = trans sig M 〈q,None ?〉 → 
  step ? (mk_binaryTM sig M) (mk_config ?? (〈q,bin0,ch,S k〉) t) 
  = mk_config ?? (〈q,bin4,None ?,to_initN 0 ??〉) (tape_move ? t R). [2,3:/2 by transitive_lt/]
#sig #M #t #q #ch #k #qn #chn #mv #Hcur #Hk #Htrans
whd in match (step ???); whd in match (trans ???);
>Hcur <Htrans %
qed.

lemma binaryTM_bin0_true :
  ∀sig,M,t,q,ch,k.
  current ? t = Some ? true → S k <S (2*FS_crd sig) → 
  step ? (mk_binaryTM sig M) (mk_config ?? (〈q,bin0,ch,S k〉) t) 
  = mk_config ?? (〈q,bin0,FS_nth sig k,to_initN k ??〉) (tape_move ? t R).[2,3:@le_S /2 by lt_S_to_lt/]
#sig #M #t #q #ch #k #Hcur #Hk
whd in match (step ???); whd in match (trans ???);
>Hcur %
qed.

lemma binaryTM_bin0_false :
  ∀sig,M,t,q,ch,k.
  current ? t = Some ? false → S k <S (2*FS_crd sig) → 
  step ? (mk_binaryTM sig M) (mk_config ?? (〈q,bin0,ch,S k〉) t) 
  = mk_config ?? (〈q,bin0,ch,to_initN k ??〉) (tape_move ? t R).[2,3:@le_S /2 by lt_S_to_lt/]
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
        (mk_tape ? (reverse ? (bin_char ? a)@ls) (option_hd ? rs) (tail ? rs))). [2,3:@le_S /2 by O/]
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

lemma le_to_eq : ∀m,n.m ≤ n → ∃k. n = m + k. /3 by plus_minus, ex_intro/
qed.

lemma minus_tech : ∀a,b.a + b - a = b. // qed.

lemma binaryTM_phase0_midtape :
  ∀sig,M,t,q,ls,a,rs,ch.
  halt sig M q=false → 
  t = mk_tape ? ls (option_hd ? (bin_char ? a)) (tail ? (bin_char sig a)@rs) →
  ∀k.S (FS_crd sig) ≤ k → 
  loopM ? (mk_binaryTM sig M) k
    (mk_config ?? (〈q,bin0,ch,FS_crd sig〉) t) 
  = loopM ? (mk_binaryTM sig M) (k - S (FS_crd sig))
      (mk_config ?? (〈q,bin1,Some ? a,FS_crd sig〉) 
        (mk_tape ? (reverse ? (bin_char ? a)@ls) (option_hd ? rs) (tail ? rs))). [|*:@le_S //]
#sig #M #t #q #ls #a #rs #ch #Hhalt #Ht #k #Hk
cases (le_to_eq … Hk) #k0 #Hk0 >Hk0 >(minus_tech (S (FS_crd sig)))
cut (∃c,cl.bin_char sig a = c::cl) [@daemon] * #c * #cl #Ha >Ha
cut (FS_crd sig = |bin_char sig a|) [@daemon] #Hlen
@(trans_eq ?? (loopM ? (mk_binaryTM ? M) (S (|c::cl|) + k0)
   (mk_config ?? 〈q,bin0,〈ch,|c::cl|〉〉 t))) 
[ /2 by O/ | @eq_f2 // @eq_f2 // @eq_f <Ha >Hlen % ]
>(binaryTM_phase0_midtape_aux ? M q ls a rs ? ? (c::cl) [ ] t ch) //
[| normalize #Hfalse @False_ind cases (not_le_Sn_O ?) /2/
| <Ha (* |bin_char sig ?| = FS_crd sig *) @daemon
| >Ha %
| >Ht >Ha % 
| <Ha <Hlen // ]
<Ha %
qed.

lemma binaryTM_phase0_None_None :
  ∀sig,M,t,q,ch,n,qn,mv.
  O < n →  n < 2*FS_crd sig → 
  halt sig M q=false → 
  current ? t = None ? →
  〈qn,None ?,mv〉 = trans sig M 〈q,None ?〉 → 
  ∀k.O < k → 
  loopM ? (mk_binaryTM sig M) k (mk_config ?? (〈q,bin0,ch,n〉) t) 
  = loopM ? (mk_binaryTM sig M) (k-1)
      (mk_config ?? (〈qn,bin3,None ?,to_initN (displ2_of_move sig mv) ??〉) (tape_move ? t (mv_tech mv))). [| @le_S @le_S //|@le_S_S @le_displ2_of_move]
#sig #M #t #q #ch #n #qn #mv #HOn #Hn #Hhalt #Hcur #Htrans #k #Hk
cases (le_to_eq … Hk) #k0 #Hk0 >Hk0 >minus_tech
cases (le_to_eq … HOn) #n0 #Hn0 destruct (Hn0)
lapply Htrans lapply Hcur -Htrans -Hcur cases t
[ >loopM_unfold >loop_S_false [|@Hhalt] #Hcur #Htrans >binaryTM_bin0_bin3 //
| #r0 #rs0 >loopM_unfold >loop_S_false [|@Hhalt] #Hcur #Htrans >binaryTM_bin0_bin3 //
| #l0 #ls0 >loopM_unfold >loop_S_false [|@Hhalt] #Hcur #Htrans >binaryTM_bin0_bin3 //
| #ls #cur #rs normalize in ⊢ (%→?); #H destruct (H) ]
qed.

lemma binaryTM_phase0_None_Some :
  ∀sig,M,t,q,ch,n,qn,chn,mv.
  O < n →  n < 2*FS_crd sig →
  halt sig M q=false → 
  current ? t = None ? →
  〈qn,Some ? chn,mv〉 = trans sig M 〈q,None ?〉 → 
  ∀k.O < k → 
  loopM ? (mk_binaryTM sig M) k (mk_config ?? (〈q,bin0,ch,n〉) t) 
  = loopM ? (mk_binaryTM sig M) (k-1) 
      (mk_config ?? (〈q,bin4,None ?,to_initN O ??〉) (tape_move ? t R)). [2,3: /2 by transitive_lt/ ]  
#sig #M #t #q #ch #n #qn #chn #mv #HOn #Hn #Hhalt #Hcur #Htrans #k #Hk
cases (le_to_eq … Hk) #k0 #Hk0 >Hk0 >minus_tech
cases (le_to_eq … HOn) #n0 #Hn0 destruct (Hn0)
lapply Htrans lapply Hcur -Hcur -Htrans cases t
[ >loopM_unfold >loop_S_false [|@Hhalt] #Hcur #Htrans >binaryTM_bin0_bin4 // /2 by refl, transitive_lt/
| #r0 #rs0 >loopM_unfold >loop_S_false [|@Hhalt] #Hcur #Htrans >binaryTM_bin0_bin4 // /2 by refl, transitive_lt/
| #l0 #ls0 >loopM_unfold >loop_S_false [|@Hhalt] #Hcur #Htrans >binaryTM_bin0_bin4 // /2 by refl, transitive_lt/
| #ls #cur #rs normalize in ⊢ (%→?); #H destruct (H) ]
qed.

lemma binaryTM_bin1_O :
  ∀sig,M,t,q,ch.
  step ? (mk_binaryTM sig M) (mk_config ?? (〈q,bin1,ch,O〉) t) 
  = mk_config ?? (〈q,bin2,ch,to_initN (FS_crd sig) ??〉) t. [2,3:/2 by lt_S_to_lt/]
#sig #M #t #q #ch %
qed.

lemma binaryTM_bin1_S :
  ∀sig,M,t,q,ch,k. S k <S (2*FS_crd sig) → 
  step ? (mk_binaryTM sig M) (mk_config ?? (〈q,bin1,ch,S k〉) t) 
  = mk_config ?? (〈q,bin1,ch,to_initN k ??〉) (tape_move ? t L). [2,3:@le_S /2 by lt_S_to_lt/]
#sig #M #t #q #ch #k #HSk %
qed.

lemma binaryTM_phase1 :
  ∀sig,M,q,ls1,ls2,cur,rs,ch.
  |ls1| = FS_crd sig → (cur = None ? → rs = [ ]) → 
  ∀k.S (FS_crd sig) ≤ k → 
  loopM ? (mk_binaryTM sig M) k
    (mk_config ?? (〈q,bin1,ch,FS_crd sig〉) (mk_tape ? (ls1@ls2) cur rs)) 
  = loopM ? (mk_binaryTM sig M) (k - S (FS_crd sig))
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
          (tail ? (reverse ? ls1@option_cons ? cur rs))))) [1,2:@le_S //]
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
       〈q,bin1,ch,to_initN (|ls0|) ?
        (le_S ?? (lt_S_to_lt (|ls0|) (S (2*FS_crd sig)) Hlt))〉
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
| #Hcut #sig #M #q #ls1 #ls2 #cur #rs #ch #Hlen #Hcur #k #Hk
  cases (le_to_eq … Hk) #k0 #Hk0 >Hk0 >minus_tech @Hcut /2/ ]
qed.

lemma binaryTM_bin2_O :
  ∀sig,M,t,q,qn,ch,chn,mv.
  〈qn,chn,mv〉 = trans sig M 〈q,ch〉 → 
  step ? (mk_binaryTM sig M) (mk_config ?? (〈q,bin2,ch,O〉) t)
  = mk_config ?? (〈qn,bin3,ch,to_initN (displ_of_move sig mv) ??〉) t.[2,3:/2 by lt_S_to_lt,le_S_S/]
#sig #M #t #q #qn #ch #chn #mv #Htrans
whd in match (step ???); whd in match (trans ???); <Htrans %
qed.

lemma binaryTM_bin2_S_None :
  ∀sig,M,t,q,qn,ch,mv,k.
  k < S (2*FS_crd sig) → 
  〈qn,None ?,mv〉 = trans sig M 〈q,ch〉 → 
  step ? (mk_binaryTM sig M) (mk_config ?? (〈q,bin2,ch,S k〉) t)
  = mk_config ?? (〈q,bin2,ch,k〉) (tape_move ? t R).
[2,3: @le_S_S /2 by lt_to_le/ ]
#sig #M #t #q #qn #ch #mv #k #Hk #Htrans
whd in match (step ???); whd in match (trans ???); <Htrans %
qed.

lemma binaryTM_bin2_S_Some :
  ∀sig,M,t,q,qn,ch,chn,mv,k.
  k< S (2*FS_crd sig) → 
  〈qn,Some ? chn,mv〉 = trans sig M 〈q,ch〉 → 
  step ? (mk_binaryTM sig M) (mk_config ?? (〈q,bin2,ch,S k〉) t)
  = mk_config ?? (〈q,bin2,ch,k〉) (tape_move ? (tape_write ? t (Some ? (FS_nth ? k == Some ? chn))) R).
[2,3: @le_S_S /2 by lt_to_le/ ]
#sig #M #t #q #qn #ch #chn #mv #k #Hk #Htrans
whd in match (step ???); whd in match (trans ???); <Htrans %
qed.

let rec iter (T:Type[0]) f n (t:T) on n ≝ 
  match n with [ O ⇒ t | S n0 ⇒ iter T f n0 (f t) ].

lemma binaryTM_phase2_None :∀sig,M,q,ch,qn,mv.
  〈qn,None ?,mv〉 = trans sig M 〈q,ch〉 → 
  ∀n.n≤S (2*FS_crd sig) → 
  ∀t,k.S n ≤ k → 
  loopM ? (mk_binaryTM sig M) k
    (mk_config ?? (〈q,bin2,ch,n〉) t)
  = loopM ? (mk_binaryTM sig M) (k - S n)
      (mk_config ?? (〈qn,bin3,ch,to_initN (displ_of_move sig mv) ??〉) 
        (iter ? (λt0.tape_move ? t0 R) n t)). [2,3: @le_S_S /2 by lt_S_to_lt/]
#sig #M #q #ch #qn #mv #Htrans #n #Hn #t #k #Hk
cases (le_to_eq … Hk) #k0 #Hk0 >Hk0 >minus_tech lapply Hn lapply t -Hn -t
elim n
[ #t #Hle >loopM_unfold >loop_S_false //
  >(binaryTM_bin2_O … Htrans) //
| #n0 #IH #t #Hn0 >loopM_unfold >loop_S_false // 
  >(binaryTM_bin2_S_None … Htrans) @(trans_eq ???? (IH …)) //
]
qed.

lemma binaryTM_phase2_Some_of : ∀sig,M,q,ch,qn,chn,mv,ls.
  〈qn,Some ? chn,mv〉 = trans sig M 〈q,ch〉 → 
  ∀k.S (FS_crd sig) ≤ k → 
  loopM ? (mk_binaryTM sig M) k
    (mk_config ?? (〈q,bin2,ch,FS_crd sig〉) (mk_tape ? ls (None ?) [ ])) 
  = loopM ? (mk_binaryTM sig M) (k - S (FS_crd sig))
      (mk_config ?? (〈qn,bin3,ch,displ_of_move sig mv〉) 
        (mk_tape ? (reverse ? (bin_char sig chn)@ls) (None ?) [ ])). [2,3:@le_S_S //]
cut (∀sig,M,q,ch,qn,chn,mv,ls,k,n.
  S n ≤ k → 〈qn,Some ? chn,mv〉 = trans sig M 〈q,ch〉 → 
  ∀csl. n <S (2*FS_crd sig) → 
  |csl| + n = FS_crd sig →
  (∃fs.bin_char sig chn = reverse ? csl@fs) → 
  loopM ? (mk_binaryTM sig M) k
    (mk_config ?? (〈q,bin2,ch,n〉) (mk_tape ? (csl@ls) (None ?) [ ])) 
  = loopM ? (mk_binaryTM sig M) (k - S n)
      (mk_config ?? (〈qn,bin3,ch,displ_of_move sig mv〉) 
        (mk_tape ? (reverse ? (bin_char sig chn)@ls) (None ?) [ ]))) [1,2:@le_S_S //]
[ #sig #M #q #ch #qn #chn #mv #ls #k #n #Hk
  cases (le_to_eq … Hk) #k0 #Hk0 >Hk0 >minus_tech
  #Htrans elim n
  [ #csl #Hcount #Hcrd * #fs #Hfs >loopM_unfold >loop_S_false // <loopM_unfold 
    cut (fs = [ ]) 
    [ cases fs in Hfs; // #f0 #fs0 #H lapply (eq_f ?? (length ?) … H)
      >length_append >(?:|bin_char sig chn| = FS_crd sig) [|@daemon]
      <Hcrd >length_reverse #H1 cut (O = |f0::fs0|) [ /2/ ]
      normalize #H1 destruct (H1) ]
    #H destruct (H) >append_nil in Hfs; #Hfs
    >Hfs >reverse_reverse >(binaryTM_bin2_O … Htrans) //
  | #n0 #IH #csl #Hcount #Hcrd * #fs #Hfs
    >loopM_unfold >loop_S_false // <loopM_unfold
    >(?: step FinBool (mk_binaryTM sig M)
         (mk_config FinBool (states FinBool (mk_binaryTM sig M)) 〈q,bin2,〈ch,S n0〉〉
         (mk_tape FinBool (csl@ls) (None FinBool) [])) 
        = mk_config ?? (〈q,bin2,ch,n0〉) 
          (tape_move ? (tape_write ? 
            (mk_tape ? (csl@ls) (None ?) [ ]) (Some ? (FS_nth ? n0 == Some ? chn))) R))
    [| /2 by lt_S_to_lt/ | @(binaryTM_bin2_S_Some … Htrans) ]
    >(?: tape_move ? (tape_write ???) ? = 
          mk_tape ? (((FS_nth ? n0 == Some sig chn)::csl)@ls) (None ?) [ ])
    [| cases csl // cases ls // ]
    cases fs in Hfs;
    [ #Hfalse cut (|bin_char ? chn| = |csl|) [ >Hfalse >length_append >length_reverse // ]
      -Hfalse >(?:|bin_char sig chn| = FS_crd sig) [|@daemon]
      <Hcrd in ⊢ (%→?); >(?:|csl| = |csl|+ O) in ⊢ (???%→?); //
      #Hfalse cut (S n0 = O) /2 by injective_plus_r/ #H destruct (H)
    | #f0 #fs0 #Hbinchar 
      cut (bin_char ? chn = reverse ? csl@(FS_nth ? n0 == Some ? chn)::fs0) [@daemon]
      -Hbinchar #Hbinchar >Hbinchar @(trans_eq ???? (IH …)) //
      [ %{fs0} >reverse_cons >associative_append @Hbinchar
      | whd in ⊢ (??%?); <Hcrd // ]
      @eq_f @eq_f @eq_f3 //
    ]
  ]
| #Hcut #sig #M #q #ch #qn #chn #mv #ls #Htrans #k #Hk
  @trans_eq 
  [3: @(trans_eq ???? (Hcut ??????? ls ? (FS_crd sig) ? Htrans …)) //
    [3:@([ ]) | %{(bin_char ? chn)} % | % ]
  || % ]
]
qed.

lemma binaryTM_phase2_Some_ow : ∀sig,M,q,ch,qn,chn,mv,ls,cs,rs.
  〈qn,Some ? chn,mv〉 = trans sig M 〈q,ch〉 → 
  |cs| = FS_crd sig → 
  ∀k.S (FS_crd sig) ≤ k →
  loopM ? (mk_binaryTM sig M) k
    (mk_config ?? (〈q,bin2,ch,FS_crd sig〉) 
      (mk_tape ? ls (option_hd ? (cs@rs)) (tail ? (cs@rs))))
  = loopM ? (mk_binaryTM sig M) (k - S (FS_crd sig))
      (mk_config ?? (〈qn,bin3,ch,displ_of_move sig mv〉) 
        (mk_tape ? (reverse ? (bin_char sig chn)@ls) (option_hd ? rs) (tail ? rs))). [2,3:@le_S_S /2 by O/]
cut (∀sig,M,q,ch,qn,chn,mv,ls,rs,k,csr.
     〈qn,Some ? chn,mv〉 = trans sig M 〈q,ch〉 → 
     ∀csl.|csr|<S (2*FS_crd sig) → 
     |csl@csr| = FS_crd sig →
     (∃fs.bin_char sig chn = reverse ? csl@fs) → 
     loopM ? (mk_binaryTM sig M) (S (|csr|) + k)
       (mk_config ?? (〈q,bin2,ch,|csr|〉) 
         (mk_tape ? (csl@ls) (option_hd ? (csr@rs)) (tail ? (csr@rs))))
     = loopM ? (mk_binaryTM sig M) k 
         (mk_config ?? (〈qn,bin3,ch,displ_of_move sig mv〉) 
           (mk_tape ? (reverse ? (bin_char sig chn)@ls) (option_hd ? rs) (tail ? rs)))) [1,2: @le_S_S /2 by le_S/]
[ #sig #M #q #ch #qn #chn #mv #ls #rs #k #csr #Htrans elim csr
  [ #csl #Hcount #Hcrd * #fs #Hfs >loopM_unfold >loop_S_false // normalize in match (length ? [ ]);
    >(binaryTM_bin2_O … Htrans) <loopM_unfold @eq_f @eq_f @eq_f3 //
    cases fs in Hfs; // #f0 #fs0 #H lapply (eq_f ?? (length ?) … H)
    >length_append >(?:|bin_char sig chn| = FS_crd sig) [|@daemon]
    <Hcrd >length_reverse #H1 cut (O = |f0::fs0|) [ /2/ ]
    normalize #H1 destruct (H1) 
  | #b0 #bs0 #IH #csl #Hcount #Hcrd * #fs #Hfs
    >loopM_unfold >loop_S_false // >(binaryTM_bin2_S_Some … Htrans)  
    >(?: tape_move ? (tape_write ???) ? = 
          mk_tape ? (((FS_nth ? (|bs0|)==Some sig chn)::csl)@ls) 
            (option_hd ? (bs0@rs)) (tail ? (bs0@rs)))
      in match (tape_move ? (tape_write ???) ?);
    [| cases bs0 // cases rs // ] @IH
    [ whd in Hcount:(?%?); /2 by lt_S_to_lt/
    | <Hcrd >length_append >length_append normalize //
    | cases fs in Hfs;
      [ #Hfalse cut (|bin_char ? chn| = |csl|) [ >Hfalse >length_append >length_reverse // ]      -Hfalse >(?:|bin_char sig chn| = FS_crd sig) [|@daemon]
        <Hcrd >length_append normalize >(?:|csl| = |csl|+ O) in ⊢ (???%→?); //
        #Hfalse cut (S (|bs0|) = O) /2 by injective_plus_r/ #H destruct (H)
      | #f0 #fs0 #Hbinchar 
        cut (bin_char ? chn = reverse ? csl@(FS_nth ? (|bs0|) == Some ? chn)::fs0) [@daemon]
        -Hbinchar #Hbinchar >Hbinchar %{fs0} >reverse_cons >associative_append %
      ]
    ]
  ]
| #Hcut #sig #M #q #ch #qn #chn #mv #ls #cs #rs #Htrans #Hcrd #k #Hk
  cases (le_to_eq … Hk) #k0 #Hk0 >Hk0 >minus_tech @trans_eq 
  [3: @(trans_eq ???? (Hcut ??????? ls ?? cs Htrans [ ] …)) //
    [ normalize % // | normalize @Hcrd | >Hcrd // ]
  || @eq_f2 [ >Hcrd % | @eq_f2 // @eq_f cases Hcrd // ] ] ]
qed.

lemma binaryTM_bin3_O :
  ∀sig,M,t,q,ch.
  step ? (mk_binaryTM sig M) (mk_config ?? (〈q,bin3,ch,O〉) t) 
  = mk_config ?? (〈q,bin0,None ?,to_initN (FS_crd sig) ??〉) t. [2,3:@le_S //]
#sig #M #t #q #ch %
qed.

lemma binaryTM_bin3_S :
  ∀sig,M,t,q,ch,k. S k ≤ S (2*FS_crd sig) → 
  step ? (mk_binaryTM sig M) (mk_config ?? (〈q,bin3,ch,S k〉) t) 
  = mk_config ?? (〈q,bin3,ch,to_initN k ??〉) (tape_move ? t L). [2,3: @le_S_S /2 by lt_to_le/]
#sig #M #t #q #ch #k #HSk %
qed.

lemma binaryTM_phase3 :∀sig,M,q,ch,n.
  n ≤ S (2*FS_crd sig) →
  ∀t,k.S n ≤ k → 
  loopM ? (mk_binaryTM sig M) k
    (mk_config ?? (〈q,bin3,ch,n〉) t) 
  = loopM ? (mk_binaryTM sig M) (k - S n)
      (mk_config ?? (〈q,bin0,None ?,FS_crd sig〉) 
        (iter ? (λt0.tape_move ? t0 L) n t)). [2,3: /2 by lt_S_to_lt, le_to_lt_to_lt/]
#sig #M #q #ch #n #Hcrd #t #k #Hk
cases (le_to_eq … Hk) #k0 #Hk0 >Hk0 >(minus_tech (S n) k0) 
lapply t lapply Hcrd -t -Hcrd elim n
[ #Hcrd #t >loopM_unfold >loop_S_false [| % ] >binaryTM_bin3_O //
| #n0 #IH #Hlt #t >loopM_unfold >loop_S_false [|%] >binaryTM_bin3_S [|@Hlt]  
  <IH [|@lt_to_le @Hlt ]
  <loopM_unfold % ]
qed.

lemma binaryTM_bin4_None :
  ∀sig,M,t,q,ch.
  current ? t = None ? → 
  step ? (mk_binaryTM sig M) (mk_config ?? (〈q,bin4,ch,O〉) t) 
  = mk_config ?? (〈q,bin2,ch,to_initN (FS_crd sig) ??〉) t. [|@le_S_S @le_O_n | @le_S_S // ]
#sig #M #t #q #ch #Hcur whd in ⊢ (??%?); >Hcur %
qed.

lemma binaryTM_phase4_write : ∀sig,M,q,ch,t.current ? t = None ? →
  ∀k.O < k → 
  loopM ? (mk_binaryTM sig M) k
    (mk_config ?? (〈q,bin4,ch,O〉) t) 
  = loopM ? (mk_binaryTM sig M) (k-1)
      (mk_config ?? (〈q,bin2,ch,to_initN (FS_crd sig) ??〉) t). [|@le_S_S @le_O_n|@le_S_S //]
#sig #M #q #ch #t #Hcur #k #Hk
cases (le_to_eq … Hk) #k0 #Hk0 >Hk0 >minus_tech
>loopM_unfold >loop_S_false // <loopM_unfold >binaryTM_bin4_None [|//] %
qed.

(* we don't get here any more! *
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
*)

lemma binaryTM_bin4_extend :
  ∀sig,M,t,q,ch,cur,qn,an,mv.
  current ? t = Some ? cur → 
  〈qn,Some ? an,mv〉 = trans sig M 〈q,ch〉 → 
  step ? (mk_binaryTM sig M) (mk_config ?? (〈q,bin4,ch,O〉) t) 
  = mk_config ?? (〈q,bin5,ch,to_initN (FS_crd sig) ??〉) (tape_move ? t L). [2,3:@le_S //]
#sig #M #t #q #ch #cur #qn #an #mv #Hcur #Htrans
whd in ⊢ (??%?); >Hcur whd in ⊢ (??%?);
whd in match (trans FinBool ??); <Htrans %
qed.

lemma binaryTM_phase4_extend : ∀sig,M,q,ch,t,cur,qn,an,mv.
  current ? t = Some ? cur → 〈qn,Some ? an,mv〉 = trans sig M 〈q,ch〉 → 
  ∀k.O < k → 
  loopM ? (mk_binaryTM sig M) k
    (mk_config ?? (〈q,bin4,ch,O〉) t) 
  = loopM ? (mk_binaryTM sig M) (k-1)
      (mk_config ?? (〈q,bin5,ch,to_initN (FS_crd sig) ??〉) (tape_move ? t L)). [2,3: @le_S //]
#sig #M #q #ch #t #cur #qn #an #mv #Hcur #Htrans #k #Hk
cases (le_to_eq … Hk) #k0 #Hk0 >Hk0 >minus_tech
>loopM_unfold >loop_S_false // <loopM_unfold >(binaryTM_bin4_extend … Hcur) [|*://] %
qed.

lemma binaryTM_bin5_O :
  ∀sig,M,t,q,ch.
  step ? (mk_binaryTM sig M) (mk_config ?? (〈q,bin5,ch,O〉) t) 
  = mk_config ?? (〈q,bin2,ch,to_initN (FS_crd sig) ??〉) (tape_move ? t R). [2,3:@le_S //]
#sig #M #t #q #ch %
qed.

lemma binaryTM_bin5_S :
  ∀sig,M,t,q,ch,k. S k <S (2*FS_crd sig) → 
  step ? (mk_binaryTM sig M) (mk_config ?? (〈q,bin5,ch,S k〉) t) 
  = mk_config ?? (〈q,bin5,ch,to_initN k ??〉) (tape_move ? (tape_write ? t (Some ? false)) L). [2,3:@le_S /2 by lt_S_to_lt/]
#sig #M #t #q #ch #k #HSk %
qed.

(* extends the tape towards the left with an unimportant sequence that will be
   immediately overwritten *)
lemma binaryTM_phase5 :∀sig,M,q,ch,n. 
  ∀rs.n<S (2*FS_crd sig) →
  ∃bs.|bs| = n ∧
  ∀k.S n ≤ k →   
  loopM ? (mk_binaryTM sig M) k
    (mk_config ?? (〈q,bin5,ch,n〉) (mk_tape ? [] (None ?) rs)) 
  = loopM ? (mk_binaryTM sig M) (k - S n)
      (mk_config ?? (〈q,bin2,ch,FS_crd sig〉) 
        (mk_tape ? [] (option_hd ? (bs@rs)) (tail ? (bs@rs)))). [2,3:@le_S //]
#sig #M #q #ch #n elim n
[ #rs #Hlt %{[]} % // #k #Hk cases (le_to_eq … Hk) #k0 #Hk0 >Hk0 >minus_tech -Hk0
  cases rs //
| #n0 #IH #rs #Hn0 cases (IH (false::rs) ?) [|/2 by lt_S_to_lt/]
  #bs * #Hbs -IH #IH %{(bs@[false])} % [ <Hbs >length_append /2 by increasing_to_injective/ ]
  #k #Hk cases (le_to_eq … Hk) #k0 #Hk0 >Hk0
  >loopM_unfold >loop_S_false // >binaryTM_bin5_S
  >associative_append normalize in match ([false]@?); <(IH (S n0 + k0)) [|//]
  >loopM_unfold @eq_f @eq_f cases rs //
]
qed.

lemma current_None_or_midtape : 
  ∀sig,t.current sig t = None sig ∨ ∃ls,c,rs.t = midtape sig ls c rs.
#sig * normalize /2/ #ls #c #rs %2 /4 by ex_intro/
qed.

lemma state_bin_lift_unfold :
  ∀sig.∀M:TM sig.∀q:states sig M.
  state_bin_lift sig M q = 〈q,bin0,None ?,FS_crd sig〉.// qed.
  
axiom current_tape_bin_list :
 ∀sig,t.current sig t = None ? → current ? (tape_bin_lift sig t) = None ?.

lemma tape_bin_lift_unfold :
 ∀sig,t. tape_bin_lift sig t = 
 mk_tape ? (rev_bin_list ? (left ? t)) (option_hd ? (opt_bin_char sig (current ? t)))
   (tail ? (opt_bin_char sig (current ? t))@bin_list ? (right ? t)). //
qed.

lemma reverse_bin_char_list : ∀sig,c,l.
  reverse ? (bin_char sig c)@rev_bin_list ? l = rev_bin_list ? (c::l). // qed.

lemma left_midtape : ∀sig,ls,c,rs.left ? (midtape sig ls c rs) = ls.// qed.
lemma current_midtape : ∀sig,ls,c,rs.current ? (midtape sig ls c rs) = Some ? c.// qed.
lemma right_midtape : ∀sig,ls,c,rs.right ? (midtape sig ls c rs) = rs.// qed.
lemma opt_bin_char_Some : ∀sig,c.opt_bin_char sig (Some ? c) = bin_char ? c.// qed.

lemma opt_cons_hd_tl : ∀A,l.option_cons A (option_hd ? l) (tail ? l) = l.
#A * // qed.

lemma le_tech : ∀a,b,c.a ≤ b → a * c ≤ b * c.
#a #b #c #H /2 by monotonic_le_times_r/
qed.

lemma iter_split : ∀T,f,m,n,x. 
  iter T f (m+n) x = iter T f m (iter T f n x).
#T #f #m #n elim n /2/
#n0 #IH #x <plus_n_Sm whd in ⊢ (??%(????%)); >IH %
qed.

lemma iter_O : ∀T,f,x.iter T f O x = x.// qed.

lemma iter_tape_move_R : ∀T,n,ls,cs,rs.|cs| = n → 
  iter ? (λt0.tape_move T t0 R) n (mk_tape ? ls (option_hd ? (cs@rs)) (tail ? (cs@rs)))
  = mk_tape ? (reverse ? cs@ls) (option_hd ? rs) (tail ? rs).
#T #n elim n
[ #ls * [| #c0 #cs0 #rs #H normalize in H; destruct (H) ] #rs #_ %
| #n0 #IH #ls * [ #rs #H normalize in H; destruct (H) ] #c #cs #rs #Hlen
  whd in ⊢ (??%?); 
  >(?: (tape_move T (mk_tape T ls (option_hd T ((c::cs)@rs)) (tail T ((c::cs)@rs))) R)
    = mk_tape ? (c::ls) (option_hd ? (cs@rs)) (tail ? (cs@rs))) in ⊢ (??(????%)?);
  [| cases cs // cases rs // ] >IH
  [ >reverse_cons >associative_append %
  | normalize in Hlen; destruct (Hlen) % ]
]
qed.

lemma tail_tech : ∀T,l1,l2.O < |l1| → tail T (l1@l2) = tail ? l1@l2.
#T * normalize // #l2 #Hfalse @False_ind cases (not_le_Sn_O O) /2/
qed.

lemma hd_tech : ∀T,l1,l2.O < |l1| → option_hd T (l1@l2) = option_hd ? l1.
#T * normalize // #l2 #Hfalse @False_ind cases (not_le_Sn_O O) /2/
qed.

lemma iter_tape_move_L_nil : ∀T,n,rs.
  iter ? (λt0.tape_move T t0 L) n (mk_tape ? [ ] (None ?) rs) =
  mk_tape ? [ ] (None ?) rs.
#T #n #rs elim n // #n0 #IH <IH in ⊢ (???%); cases rs //
qed.

lemma iter_tape_move_R_nil : ∀T,n,ls.
  iter ? (λt0.tape_move T t0 R) n (mk_tape ? ls (None ?) [ ]) =
  mk_tape ? ls (None ?) [ ].
#T #n #ls elim n // #n0 #IH <IH in ⊢ (???%); cases ls //
qed.

lemma iter_tape_move_L_left : ∀T,n,cs,rs. O < n →
  iter ? (λt0.tape_move T t0 L) n 
    (mk_tape ? [ ] (option_hd ? cs) (tail ? cs@rs)) =
  mk_tape ? [ ] (None ?) (cs@rs).
#T #n #cs #rs * 
[ cases cs // cases rs //
| #m #_ whd in ⊢ (??%?); <(iter_tape_move_L_nil ? m) cases cs // cases rs // ]
qed.

lemma iter_tape_move_L : ∀T,n,ls,cs,rs.|cs| = n → 
  iter ? (λt0.tape_move T t0 L) n (mk_tape ? (reverse ? cs@ls) (option_hd ? rs) (tail ? rs))
  = mk_tape ? ls (option_hd ? (cs@rs)) (tail ? (cs@rs)).
#T #n elim n
[ #ls * [| #c0 #cs0 #rs #H normalize in H; destruct (H) ] #rs #_ %
| #n0 #IH #ls #cs #rs @(list_elim_left … cs)
  [ #H normalize in H; destruct (H) ] -cs 
  #c #cs #_ #Hlen >reverse_append whd in ⊢ (??%?); 
  >(?: tape_move T (mk_tape T ((reverse T [c]@reverse T cs)@ls) (option_hd T rs) (tail T rs)) L
    = mk_tape ? (reverse T cs@ls) (option_hd ? (c::rs)) (tail ? (c::rs))) in ⊢ (??(????%)?);
  [| cases rs // ] >IH
  [ >associative_append %
  | >length_append in Hlen; normalize // ]
]
qed.

axiom loop_increase : ∀sig,M,m,n,cfg,cfg'.m < n → 
  loopM sig M m cfg = Some ? cfg' → loopM sig M n cfg = Some ? cfg'.

lemma binaryTM_loop :
 ∀sig,M,i,tf,qf. O < FS_crd sig → 
 ∀t,q.∃k.i ≤ k ∧ 
 ((loopM sig M i (mk_config ?? q t) = Some ? (mk_config ?? qf tf) →
  loopM ? (mk_binaryTM sig M) k 
    (mk_config ?? (state_bin_lift ? M q) (tape_bin_lift ? t)) = 
  Some ? (mk_config ?? (state_bin_lift ? M qf) (tape_bin_lift ? tf))) ∧
 (loopM sig M i (mk_config ?? q t) = None ? →
  loopM ? (mk_binaryTM sig M) k 
    (mk_config ?? (state_bin_lift ? M q) (tape_bin_lift ? t)) = None ?)).
#sig #M #i #tf #qf #Hcrd elim i
[ #t #q %{O} % // % // change with (None ?) in ⊢ (??%?→?); #H destruct (H)
| -i #i #IH #t #q >loopM_unfold 
  lapply (refl ? (halt sig M (cstate ?? (mk_config ?? q t))))
  cases (halt ?? q) in ⊢ (???%→?); #Hhalt
  [ %{(S i)} % // 
    >(loop_S_true ??? (λc.halt ?? (cstate ?? c)) (mk_config ?? q t) Hhalt) %
    [| #H destruct (H)]
    #H destruct (H) >loopM_unfold >loop_S_true // ]
  (* interesting case: more than one step *)
  >(loop_S_false ??? (λc.halt ?? (cstate ?? c)) (mk_config ?? q t) Hhalt)cases (current_None_or_midtape ? t)
  (*** current = None ***)
  [ #Hcur lapply (current_tape_bin_list … Hcur) #Hcur'
    cut (∃qn,chn,mv.〈qn,chn,mv〉 = trans ? M 〈q,None ?〉)
    [ cases (trans ? M 〈q,None ?〉) * #qn #chn #mv /4 by ex_intro/ ]
    * #qn * #chn * #mv cases chn -chn
    [ #Htrans lapply (binaryTM_phase0_None_None … (None ?) (FS_crd sig) … Hhalt Hcur' Htrans) // [/2 by monotonic_lt_plus_l/]
      lapply (binaryTM_phase3 ? M qn (None ?) (displ2_of_move sig mv) ? (tape_move FinBool (tape_bin_lift sig t) (mv_tech mv))) [//]
      cases (IH (tape_move ? t mv) qn) -IH #k0 * #Hk0 * #IH #IHNone
      #phase3 #phase0 %{(S (S (displ2_of_move sig mv))+k0)} %
      [ @le_S_S @(le_plus O) // ]
      >state_bin_lift_unfold >phase0 [|//]
      >phase3 [|//] 
      >(?: S (S (displ2_of_move sig mv))+k0-1-S (displ2_of_move sig mv) = k0)
      [| /2 by refl, plus_to_minus/ ]
      cut (tape_move sig t mv=tape_move sig (tape_write sig t (None sig)) mv) [%] #Hcut 
      >(?: iter ? (λt0.tape_move ? t0 L) (displ2_of_move sig mv) (tape_move ? (tape_bin_lift ? t) (mv_tech mv))
           =tape_bin_lift ? (tape_move ? t mv))
      [|cases t in Hcur;
        [4: #ls #c #rs normalize in ⊢ (%→?); #H destruct (H)
        | #_ whd in match (tape_bin_lift ??);
          (* TODO *)
          (* ∀mv.tape_move ? (niltape ?) mv = niltape ? *)
          (* ∀n.iter ? (λt.tape_move ? t ?) n (niltape ?) = niltape ? *)
          @daemon
        | #r0 #rs0 #_ cases mv
          [ >tape_bin_lift_unfold whd in match (mv_tech L); whd in match (displ2_of_move sig L);
            whd in match (rev_bin_list ??); whd in match (option_hd ??); 
            whd in match (right ??); >(?: []@bin_list ? (r0::rs0) = bin_char ? r0@bin_list ? rs0) [|%]
            (* TODO *)
            (* tape_move (mk_tape [ ] (None ?) rs R = ... *)
            (* use iter_tape_move_R *)
            @daemon
          | >tape_bin_lift_unfold whd in match (mv_tech R); whd in match (displ2_of_move sig R);
            whd in match (rev_bin_list ??); whd in match (option_hd ??); 
            whd in match (right ??); >(?: []@bin_list ? (r0::rs0) = bin_char ? r0@bin_list ? rs0) [|%]
            whd in match (tape_move ? (leftof ???) R);
            >tape_bin_lift_unfold >left_midtape >opt_bin_char_Some >right_midtape
            >iter_O
            (* TODO *)
            (* tape_move (mk_tape [ ] (None ?) rs R = ... *)
            @daemon
          | >tape_bin_lift_unfold % ]
        | #l0 #ls0 #_ cases mv
          [ >tape_bin_lift_unfold whd in match (mv_tech L); whd in match (displ2_of_move sig L);
            whd in match (bin_list ??); >append_nil whd in match (option_hd ??); 
            whd in match (left ??); whd in match (tail ??);
            whd in match (tape_move ? (rightof ???) L);
            >(?: rev_bin_list ? (l0::ls0) = reverse ? (bin_char ? l0)@rev_bin_list ? ls0) [|%]
            (* TODO *)
            (* tape_move (mk_tape ls (None ?) [ ] R = ... *)
            (* use iter_tape_move_L *)
            @daemon
          | >tape_bin_lift_unfold whd in match (mv_tech R); whd in match (displ2_of_move sig R);
            whd in match (bin_list ??); >append_nil whd in match (option_hd ??); 
            whd in match (left ??); whd in match (tail ??); >iter_O cases (rev_bin_list ??) //
          | >tape_bin_lift_unfold % ]
        ]
      ]
      %
      [ #Hloop @IH <Hloop @eq_f whd in ⊢ (???%); >Hcur <Htrans @eq_f @Hcut
      | #Hloop @IHNone <Hloop @eq_f whd in ⊢ (???%); >Hcur <Htrans @eq_f @Hcut ]
    | #chn #Htrans 
      lapply (binaryTM_phase0_None_Some … (None ?) (FS_crd sig) … Hhalt Hcur' Htrans) // [/2 by monotonic_lt_plus_l/]
      cases t in Hcur;
      [ 4: #ls #c #rs normalize in ⊢ (%→?); #H destruct (H)
      | 2: #r0 #rs0 #_ cut (∃b,bs.bin_char ? r0 = b::bs) [ @daemon ] * #b * #bs #Hbs 
        lapply (binaryTM_phase4_extend ???? (tape_move ? (tape_bin_lift ? (leftof ? r0 rs0)) R) b … Htrans)
        [ >tape_bin_lift_unfold whd in match (option_hd ??); whd in match (tail ??);
          whd in match (right ??);
          >(?:bin_list ? (r0::rs0) = bin_char ? r0@bin_list ? rs0) [|%]
          >Hbs % ]
        cases (binaryTM_phase5 ? M q (None ?) (FS_crd sig) (bin_list ? (r0::rs0)) ?) [|//]
        #cs * #Hcs
        lapply (binaryTM_phase2_Some_ow ?? q (None ?) … [ ] ? (bin_list ? (r0::rs0)) Htrans Hcs)
        lapply (binaryTM_phase3 ? M qn (None ?) (displ_of_move sig mv) ? 
                 (mk_tape FinBool (reverse bool (bin_char sig chn)@[])
                   (option_hd FinBool (bin_list sig (r0::rs0))) (tail FinBool (bin_list sig (r0::rs0))))) [//]
        cases (IH (tape_move ? (tape_write ? (leftof ? r0 rs0) (Some ? chn)) mv) qn) -IH #k0 * #Hk0 * #IH #IHNone
        #phase3 #phase2 #phase5 #phase4 #phase0 
        %{(1 + 1 + (S (FS_crd sig)) + (S (FS_crd sig)) + S (displ_of_move sig mv) + k0)} %
        [ @le_S_S @(le_plus O) // ]
        >state_bin_lift_unfold >phase0 [|//]
        >phase4 [|//] 
        >(?: loopM ? (mk_binaryTM ??) ? (mk_config ?? 〈q,bin5,None ?,to_initN ???〉 ?) = ?)
        [|| @(trans_eq ????? (phase5 ??)) 
          [ @eq_f @eq_f
            >tape_bin_lift_unfold whd in match (rev_bin_list ??);
            whd in match (right ??); whd in match (bin_list ??);
            cases (bin_char ? r0) // (* bin_char can't be nil *) @daemon
          | @le_S_S >associative_plus >associative_plus >commutative_plus @(le_plus O) //
          |]]
        >phase2 [| (*arith*) @daemon ]
        >phase3 [| (*arith*) @daemon ]
        >(?: 1+1+S (FS_crd sig)+S (FS_crd sig)+S (displ_of_move sig mv)+k0-1-1
              -S (FS_crd sig)-S (FS_crd sig) -S (displ_of_move sig mv) = k0) 
        [| (*arith*) @daemon ]
        -phase0 -phase2 -phase3 -phase4 -phase5 <state_bin_lift_unfold
        >(?: iter ? (λt0.tape_move ? t0 L) (displ_of_move sig mv)
              (mk_tape ? (reverse ? (bin_char sig chn)@[])
                (option_hd FinBool (bin_list sig (r0::rs0)))
                (tail FinBool (bin_list sig (r0::rs0))))
           = tape_bin_lift ? (tape_move ? (tape_write ? (leftof ? r0 rs0) (Some ? chn)) mv))
        [ % #Hloop
          [ @IH <Hloop @eq_f whd in ⊢ (???%); <Htrans %
          | @IHNone <Hloop @eq_f whd in ⊢ (???%); <Htrans % ]
        | >(?:bin_list ? (r0::rs0) = bin_char ? r0@bin_list ? rs0) [|%] 
          cases mv
          [ >(?:displ_of_move sig L = FS_crd sig+FS_crd sig) [|normalize //]
            >iter_split >iter_tape_move_L [| @daemon ]
            >hd_tech [|@daemon] >tail_tech [|@daemon] >iter_tape_move_L_left [|//]
            whd in match (tape_move ???); >tape_bin_lift_unfold %
          | normalize in match (displ_of_move ??); >iter_O
            normalize in match (tape_move ???); 
            >tape_bin_lift_unfold >opt_bin_char_Some
            >hd_tech [|@daemon] >tail_tech [| @daemon ] %
          | normalize in match (displ_of_move ??);
            >iter_tape_move_L [|@daemon]
            normalize in match (tape_move ???); >tape_bin_lift_unfold
            >opt_bin_char_Some >hd_tech [|@daemon] >tail_tech [|@daemon] % ]
        ]
      | #_ lapply (binaryTM_phase4_write ? M q (None ?) (niltape ?) (refl ??))
        lapply (binaryTM_phase2_Some_of ?? q (None ?) … [ ] Htrans)
        lapply (binaryTM_phase3 ? M qn (None ?) (displ_of_move sig mv) ? 
                 (mk_tape FinBool (reverse bool (bin_char sig chn)@[]) (None ?) [ ])) [//]
        cases (IH (tape_move ? (midtape ? [ ] chn [ ]) mv) qn) -IH #k0 * #Hk0 * #IH #IHNone
        #phase3 #phase2 #phase4 #phase0
        %{(1 + 1 + (S (FS_crd sig)) + S (displ_of_move sig mv) + k0)} %
        [ @le_S_S @(le_plus O) // ]
        >state_bin_lift_unfold >phase0 [|//]
        >phase4 [|//]
        >phase2 [|(*arith *) @daemon]
        >phase3 [| (*arith*) @daemon ]
        >(?: 1+1+S (FS_crd sig) + S (displ_of_move sig mv)+k0-1-1
              -S (FS_crd sig)-S (displ_of_move sig mv) = k0) 
        [| (*arith*) @daemon ]
        -phase0 -phase2 -phase3 -phase4 <state_bin_lift_unfold
        >(?: iter ? (λt0.tape_move ? t0 L) (displ_of_move sig mv)
              (mk_tape ? (reverse ? (bin_char sig chn)@[]) (None ?) [ ])
           = tape_bin_lift ? (tape_move ? (tape_write ? (niltape ?) (Some ? chn)) mv))
        [ % #Hloop
          [ @IH <Hloop @eq_f whd in ⊢ (???%); <Htrans %
          | @IHNone <Hloop @eq_f whd in ⊢ (???%); <Htrans % ]
        | cases mv
          [ >(?:displ_of_move sig L = FS_crd sig+FS_crd sig) [|normalize //]
            >iter_split change with (mk_tape ?? (option_hd ? [ ]) (tail ? [ ])) in ⊢ (??(????(????%))?);
            >iter_tape_move_L [| @daemon ]
            >append_nil in ⊢ (??(????(???%?))?); >tail_tech [|@daemon] 
            >iter_tape_move_L_left [|//]
            normalize in match (tape_move ???);
            >tape_bin_lift_unfold %
          | normalize in match (displ_of_move ??); >iter_O
            normalize in match (tape_move ???); 
            >tape_bin_lift_unfold %
          | normalize in match (displ_of_move ??);
            change with (mk_tape ?? (option_hd ? [ ]) (tail ? [ ])) in ⊢ (??(????%)?);
            >iter_tape_move_L [|@daemon]
            normalize in match (tape_move ???); >tape_bin_lift_unfold
            >opt_bin_char_Some >hd_tech [|@daemon] >tail_tech [|@daemon] % ]
        ]
      | #l0 #ls0 #_ lapply (binaryTM_phase4_write ? M q (None ?) (tape_bin_lift ? (rightof ? l0 ls0)) ?) 
        [ >tape_bin_lift_unfold >current_mk_tape % ]
        lapply (binaryTM_phase2_Some_of ?? q (None ?) … (rev_bin_list ? (l0::ls0)) Htrans)
        lapply (binaryTM_phase3 ? M qn (None ?) (displ_of_move sig mv) ? 
                 (mk_tape FinBool (reverse bool (bin_char sig chn)@rev_bin_list ? (l0::ls0)) (None ?) [ ])) [//]
        cases (IH (tape_move ? (midtape ? (l0::ls0) chn [ ]) mv) qn) -IH #k0 * #Hk0 * #IH #IHNone
        #phase3 #phase2 #phase4 #phase0
        %{(1 + 1 + (S (FS_crd sig)) + S (displ_of_move sig mv) + k0)} %
        [ @le_S_S @(le_plus O) // ]
        >state_bin_lift_unfold >phase0 [|//]
        >(?:tape_move ? (tape_bin_lift ? (rightof ? l0 ls0)) R = tape_bin_lift ? (rightof ? l0 ls0))
        [| >tape_bin_lift_unfold normalize in match (option_hd ??); normalize in match (right ??);
           normalize in match (tail ??); normalize in match (left ??);
           >(?:rev_bin_list ? (l0::ls0) = reverse ? (bin_char ? l0)@rev_bin_list ? ls0) [|%]
           cases (reverse ? (bin_char ? l0)) // cases (rev_bin_list ? ls0) // ]
        >phase4 [|//]
        >phase2 [|(*arith *) @daemon]
        >phase3 [| (*arith*) @daemon]
        >(?: 1+1+S (FS_crd sig) + S (displ_of_move sig mv)+k0-1-1
              -S (FS_crd sig)-S (displ_of_move sig mv) = k0) 
        [| (*arith*) @daemon ]
        -phase0 -phase2 -phase3 -phase4 <state_bin_lift_unfold
        >(?: iter ? (λt0.tape_move ? t0 L) (displ_of_move sig mv)
              (mk_tape ? (reverse ? (bin_char sig chn)@rev_bin_list ? (l0::ls0)) (None ?) [ ])
           = tape_bin_lift ? (tape_move ? (tape_write ? (rightof ? l0 ls0) (Some ? chn)) mv))
        [ % #Hloop
          [ @IH <Hloop @eq_f whd in ⊢ (???%); <Htrans %
          | @IHNone <Hloop @eq_f whd in ⊢ (???%); <Htrans % ]
        | cases mv
          [ >(?:displ_of_move sig L = FS_crd sig+FS_crd sig) [|normalize //]
            >iter_split change with (mk_tape ?? (option_hd ? [ ]) (tail ? [ ])) in ⊢ (??(????(????%))?);
            >iter_tape_move_L [| @daemon ]
            >append_nil in ⊢ (??(????(???%?))?); >tail_tech [|@daemon] 
            >(?:rev_bin_list ? (l0::ls0) = reverse ? (bin_char ? l0)@rev_bin_list ? ls0) [|%]
            >append_nil >iter_tape_move_L [|@daemon]
            normalize in match (tape_move ???);
            >tape_bin_lift_unfold @eq_f2
            [ >hd_tech [|@daemon] %
            | >tail_tech [|@daemon] >opt_bin_char_Some normalize in match (bin_list ??); >append_nil %]
          | normalize in match (displ_of_move ??); >iter_O
            normalize in match (tape_move ???); 
            >tape_bin_lift_unfold %
          | normalize in match (displ_of_move ??);
            change with (mk_tape ?? (option_hd ? [ ]) (tail ? [ ])) in ⊢ (??(????%)?);
            >iter_tape_move_L [|@daemon]
            normalize in match (tape_move ???); >tape_bin_lift_unfold
            >opt_bin_char_Some >hd_tech [|@daemon] >tail_tech [|@daemon] % ]
        ]
      ]
    ]
  (*** midtape ***)
  | * #ls * #c * #rs #Ht >Ht     
    cut (∃qn,chn,mv.〈qn,chn,mv〉 = trans ? M 〈q,Some ? c〉)
    [ cases (trans ? M 〈q,Some ? c〉) * #qn #chn #mv /4 by ex_intro/ ]
    * #qn * #chn * #mv #Htrans
    cut (tape_bin_lift ? t = ?) [| >tape_bin_lift_unfold % ] 
    >Ht in ⊢ (???%→?); >opt_bin_char_Some >left_midtape >right_midtape #Ht'
    lapply (binaryTM_phase0_midtape ?? (tape_bin_lift ? t) q … (None ?) Hhalt Ht')
    lapply (binaryTM_phase1 ?? q (reverse ? (bin_char ? c)) (rev_bin_list ? ls) 
             (option_hd ? (bin_list ? rs)) (tail ? (bin_list ? rs)) (Some ? c) ??)
    [ cases (bin_list ? rs) // @daemon | >length_reverse @daemon |]
    >opt_cons_hd_tl >reverse_reverse
    cases chn in Htrans; -chn
    [ #Htrans 
      lapply (binaryTM_phase2_None … Htrans (FS_crd sig) ? 
               (mk_tape FinBool (rev_bin_list sig ls)
                 (option_hd FinBool (bin_char sig c@bin_list sig rs))
                 (tail FinBool (bin_char sig c@bin_list sig rs)))) [//]
      lapply (binaryTM_phase3 ? M qn (Some ? c) (displ_of_move sig mv) ? 
               (mk_tape FinBool (reverse bool (bin_char sig c)@rev_bin_list ? ls)
               (option_hd FinBool (bin_list sig rs)) (tail FinBool (bin_list sig rs)))) [//]
      cases (IH (tape_move ? (tape_write ? (midtape ? ls c rs) (None ?)) mv) qn) -IH #k0 * #Hk0 * #IH #IHNone
      #phase3 #phase2 #phase1 #phase0
      %{(S (FS_crd sig) + S (FS_crd sig) + S (FS_crd sig) + S (displ_of_move sig mv) + k0)} %
      [ @le_S_S @(le_plus O) // ]
      >state_bin_lift_unfold <Ht >phase0 [|//]
      >phase1 [|/2 by monotonic_le_minus_l/]
      >phase2 [|/2 by monotonic_le_minus_l/]
      >iter_tape_move_R [|@daemon]
      >phase3 [|/2 by monotonic_le_minus_l/]
      -phase0 -phase1 -phase2 -phase3
      >(?: S (FS_crd sig) + S (FS_crd sig) + S (FS_crd sig) + S (displ_of_move sig mv) + k0
           - S (FS_crd sig) - S (FS_crd sig) - S (FS_crd sig) - S (displ_of_move sig mv)
         = k0) [| (*arith*) @daemon]
      <state_bin_lift_unfold
      >(?: iter ? (λt0.tape_move ? t0 L) (displ_of_move sig mv)
            (mk_tape ? (reverse ? (bin_char sig c)@rev_bin_list ? ls) 
              (option_hd ? (bin_list ? rs)) (tail ? (bin_list ? rs)))
         = tape_bin_lift ? (tape_move ? (tape_write ? (midtape ? ls c rs) (None ?)) mv))
      [ % #Hloop
        [ @IH <Hloop @eq_f whd in ⊢ (???%); >Ht <Htrans %
        | @IHNone <Hloop @eq_f whd in ⊢ (???%); >Ht <Htrans % ]
      | normalize in match (tape_write ???); cases mv in Htrans; #Htrans
        [ >(?:displ_of_move sig L = FS_crd sig+FS_crd sig) [|normalize //]
          >iter_split >iter_tape_move_L [| @daemon ]
          cases ls
          [ >hd_tech [|@daemon] >tail_tech [|@daemon] >iter_tape_move_L_left [|//]
            >tape_bin_lift_unfold %
          | #l0 #ls0 >(?:rev_bin_list ? (l0::ls0) = reverse ? (bin_char ? l0)@rev_bin_list ? ls0) [|%]
            normalize in match (tape_move ???);
            >iter_tape_move_L [|@daemon]
            >hd_tech [|@daemon] >tail_tech [|@daemon]
            >tape_bin_lift_unfold % ]
        | normalize in match (displ_of_move ??); >iter_O cases rs
          [ normalize in match (tape_move ???); >tape_bin_lift_unfold %
          | #r0 #rs0 normalize in match (tape_move ???);
            >tape_bin_lift_unfold >opt_bin_char_Some
            >left_midtape >right_midtape
            >(?:bin_list ? (r0::rs0) = bin_char ? r0@bin_list ? rs0) [|%]
            >hd_tech [|@daemon] >tail_tech [|@daemon] %
          ]
        | normalize in match (displ_of_move ??); >iter_tape_move_L [|@daemon]
          >hd_tech [|@daemon] >tail_tech [|@daemon] >tape_bin_lift_unfold %
        ]
      ]
    | #chn #Htrans 
      lapply (binaryTM_phase2_Some_ow ?? q (Some ? c) ??? (rev_bin_list ? ls) (bin_char ? c) (bin_list ? rs) Htrans ?)
      [@daemon]
      lapply (binaryTM_phase3 ? M qn (Some ? c) (displ_of_move sig mv) ? 
               (mk_tape FinBool (reverse bool (bin_char sig chn)@rev_bin_list ? ls)
               (option_hd FinBool (bin_list sig rs)) (tail FinBool (bin_list sig rs)))) [//]
      cases (IH (tape_move ? (tape_write ? (midtape ? ls c rs) (Some ? chn)) mv) qn) -IH #k0 * #Hk0 * #IH #IHNone
      #phase3 #phase2 #phase1 #phase0
      %{(S (FS_crd sig) + S (FS_crd sig) + S (FS_crd sig) + S (displ_of_move sig mv) + k0)} %
      [ @le_S_S @(le_plus O) // ]
      >state_bin_lift_unfold <Ht >phase0 [|//]
      >phase1 [|/2 by monotonic_le_minus_l/]
      >phase2 [|/2 by monotonic_le_minus_l/]
      >phase3 [|/2 by monotonic_le_minus_l/]
      -phase0 -phase1 -phase2 -phase3
      >(?: S (FS_crd sig) + S (FS_crd sig) + S (FS_crd sig) + S (displ_of_move sig mv) + k0
           - S (FS_crd sig) - S (FS_crd sig) - S (FS_crd sig) - S (displ_of_move sig mv)
         = k0) [| (*arith*) @daemon]
      <state_bin_lift_unfold
      >(?: iter ? (λt0.tape_move ? t0 L) (displ_of_move sig mv)
            (mk_tape ? (reverse ? (bin_char sig chn)@rev_bin_list ? ls) 
              (option_hd ? (bin_list ? rs)) (tail ? (bin_list ? rs)))
         = tape_bin_lift ? (tape_move ? (tape_write ? (midtape ? ls c rs) (Some ? chn)) mv))
      [ % #Hloop
        [ @IH <Hloop @eq_f whd in ⊢ (???%); >Ht <Htrans %
        | @IHNone <Hloop @eq_f whd in ⊢ (???%); >Ht <Htrans % ]
      | normalize in match (tape_write ???); cases mv in Htrans; #Htrans
        [ >(?:displ_of_move sig L = FS_crd sig+FS_crd sig) [|normalize //]
          >iter_split >iter_tape_move_L [| @daemon ]
          cases ls
          [ >hd_tech [|@daemon] >tail_tech [|@daemon] >iter_tape_move_L_left [|//]
            >tape_bin_lift_unfold %
          | #l0 #ls0 >(?:rev_bin_list ? (l0::ls0) = reverse ? (bin_char ? l0)@rev_bin_list ? ls0) [|%]
            normalize in match (tape_move ???);
            >iter_tape_move_L [|@daemon]
            >hd_tech [|@daemon] >tail_tech [|@daemon]
            >tape_bin_lift_unfold % ]
        | normalize in match (displ_of_move ??); >iter_O cases rs
          [ normalize in match (tape_move ???); >tape_bin_lift_unfold %
          | #r0 #rs0 normalize in match (tape_move ???);
            >tape_bin_lift_unfold >opt_bin_char_Some
            >left_midtape >right_midtape
            >(?:bin_list ? (r0::rs0) = bin_char ? r0@bin_list ? rs0) [|%]
            >hd_tech [|@daemon] >tail_tech [|@daemon] %
          ]
        | normalize in match (displ_of_move ??); >iter_tape_move_L [|@daemon]
          >hd_tech [|@daemon] >tail_tech [|@daemon] >tape_bin_lift_unfold %
        ]
      ]
    ]
  ]
]
qed.

definition R_bin_lift ≝ λsig,R,t1,t2.
  ∀u1.t1 = tape_bin_lift sig u1 → 
  ∃u2.t2 = tape_bin_lift sig u2 ∧ R u1 u2.
  
(*
∀sig,M,i,tf,qf. O < FS_crd sig → 
 ∀t,q.∃k.i ≤ k ∧ 
 ((loopM sig M i (mk_config ?? q t) = Some ? (mk_config ?? qf tf) →
  loopM ? (mk_binaryTM sig M) k 
    (mk_config ?? (state_bin_lift ? M q) (tape_bin_lift ? t)) = 
  Some ? (mk_config ?? (state_bin_lift ? M qf) (tape_bin_lift ? tf))) ∧
 (loopM sig M i (mk_config ?? q t) = None ? →
  loopM ? (mk_binaryTM sig M) k 
    (mk_config ?? (state_bin_lift ? M q) (tape_bin_lift ? t)) = None ?)).
    *)
axiom loop_incr : ∀sig,M,m,n,cfg,cfg'.m ≤ n → 
  loopM sig M m cfg = Some ? cfg' → loopM sig M n cfg = Some ? cfg'.

theorem sem_binaryTM : 
  ∀sig,M,R.O < FS_crd sig → M ⊫ R → mk_binaryTM sig M ⊫ R_bin_lift ? R.
#sig #M #R #Hcrd #HM #t #k #outc #Hloopbin #u #Ht
lapply (refl ? (loopM ? M k (initc ? M u))) cases (loopM ? M k (initc ? M u)) in ⊢ (???%→?);
[ #H cases (binaryTM_loop ? M k u (start ? M) Hcrd u (start ? M))
  #k0 * #Hlt * #_ #H1 lapply (H1 H) -H -H1 <Ht
  whd in match (initc ???) in Hloopbin; whd in match (start ??) in Hloopbin;
  >state_bin_lift_unfold >(loop_incr … Hlt Hloopbin) #H destruct (H)
| * #qf #tf #H cases (binaryTM_loop ? M k tf qf Hcrd u (start ? M))
  #k0 * #Hlt * #H1 #_ lapply (H1 H) -H1 <Ht
  whd in match (initc ???) in Hloopbin; whd in match (start ??) in Hloopbin;
  >state_bin_lift_unfold >(loop_incr … Hlt Hloopbin) #Heq destruct (Heq)
  % [| % [%]] @(HM … H)
qed.
(*
    ||M||  This file is part of HELM, an Hypertextual, Electronic   
    ||A||  Library of Mathematics, developed at the Computer Science 
    ||T||  Department of the University of Bologna, Italy.           
    ||I||                                                            
    ||T||  
    ||A||  
    \   /  This file is distributed under the terms of the       
     \ /   GNU General Public License Version 2   
      V_____________________________________________________________*)

include "turing/turing.ma".

(******************* inject a mono machine into a multi tape one **********************)
definition inject_trans ≝ λsig,states:FinSet.λn,i:nat.
  λtrans:states × (option sig) → states  × (option (sig × move)).
  λp:states × (Vector (option sig) (S n)).
  let 〈q,a〉 ≝ p in
  let 〈nq,na〉 ≝ trans 〈q,nth i ? a (None ?)〉 in
  〈nq, change_vec ? (S n) (null_action ? n) na i〉.

definition inject_TM ≝ λsig.λM:TM sig.λn,i.
  mk_mTM sig n
    (states ? M)
    (inject_trans ?? n i (trans ? M))
    (start ? M)
    (halt ? M).

axiom current_chars_change_vec: ∀sig,n,v,a,i. i < S n →
   current_chars sig ? (change_vec ? (S n) v a i) =
   change_vec ? (S n)(current_chars ?? v) (current ? a) i.
   
lemma inject_trans_def :∀sig:FinSet.∀n,i:nat.i < S n → 
  ∀M,v,s,a,sn,an.
  trans sig M 〈s,a〉 = 〈sn,an〉 → 
  cic:/matita/turing/turing/trans.fix(0,2,9) sig n (inject_TM sig M n i) 〈s,change_vec ? (S n) v a i〉 = 
    〈sn,change_vec ? (S n) (null_action ? n) an i〉.
#sig #n #i #Hlt #trans #v #s #a #sn #an #Htrans
whd in ⊢ (??%?); >nth_change_vec // >Htrans //
qed.

lemma inject_step : ∀sig,n,M,i,q,t,nq,nt,v. i < S n →
  step sig M (mk_config ?? q t) = mk_config ?? nq nt → 
  cic:/matita/turing/turing/step.def(10) sig n (inject_TM sig M n i) 
    (mk_mconfig ?? n q (change_vec ? (S n) v t i)) 
  = mk_mconfig ?? n nq (change_vec ? (S n) v nt i).
#sig #n #M #i #q #t #nq #nt #v #lein whd in ⊢ (??%?→?);
whd in match (step ????); >(current_chars_change_vec … lein)
>(eq_pair_fst_snd … (trans sig M ?)) whd in ⊢ (??%?→?); #H
>(inject_trans_def sig n i lein M … (eq_pair_fst_snd … ))
whd in ⊢ (??%?); @eq_f2 [destruct (H) // ]
@(eq_vec … (niltape ?)) #i0 #lei0n 
>nth_change_vec_neq >nth_change_vec_neq 
 … (tr
// qed.


lemma halt_inject: ∀sig,n,M,i,x.
  cic:/matita/turing/turing/halt.fix(0,2,9) sig n (inject_TM sig M n i) x
   = halt sig M x.
// qed.

lemma de_option: ∀A,a,b. Some A a = Some A b → a = b. 
#A #a #b #H destruct //
qed. 

lemma loop_inject: ∀sig,n,M,i,k,ins,int,outs,outt,vt.
 loopM sig M k (mk_config ?? ins int) = Some ? (mk_config ?? outs outt) → 
 cic:/matita/turing/turing/loopM.def(11) sig n (inject_TM sig M n i) k (mk_mconfig ?? n ins (change_vec ?? vt int i))
  =Some ? (mk_mconfig sig ? n outs (change_vec ?? vt outt i)).
#sig #n #M #i #k elim k -k
  [#ins #int #outs #outt #vt normalize in ⊢ (%→?); #H destruct
  |#k #Hind #ins #int #outs #outt #vt whd in ⊢ (??%?→??%?);
   >halt_inject whd in match (cstate ????);
   cases (true_or_false (halt sig M ins)) #Hhalt >Hhalt 
   whd in ⊢ (??%?→??%?);
    [#H @eq_f whd in ⊢ (??%?); lapply (de_option ??? H) -H 
     whd  in ⊢ (??%?→?); #H @eq_f2  
      [whd in ⊢ (??%?); destruct (H) //
      |@(eq_vec … (niltape ?)) #j #lejn
       cases (true_or_false (eqb i j)) #eqij
        [>(eqb_true_to_eq … eqij) >nth_change_vec //
         destruct (H) >nth_change_vec //
        |destruct (H) //
        ]
      ]
    |>(config_expand … (step ???)) #H <(Hind … H) 
     >loopM_unfold @eq_f >(mconfig_expand … (step ????)) 
     @eq_f2 [ normalize in ⊢ (???%);
  |%[>nth_change_vec // @le_S_S //
    |#j #i >nth_change_vec_neq //
    ]
  ]

(*
lemma cstate_inject: ∀sig,n,M,i,x. *)
  

definition inject_R ≝ λsig.λR:relation (tape sig).λn,i:nat.
  λv1,v2: (Vector (tape sig) (S n)).
  R (nth i ? v1 (niltape ?)) (nth i ? v2 (niltape ?)) ∧
  ∀j. i ≠ j → nth j ? v1 (niltape ?) = nth j ? v2 (niltape ?). 

(*
lemma nth_make : ∀A,i,n,j,a,d. i < n → nth i ? (make_veci A a n j) d = a (j+i).
#A #i elim i
  [#n #j #a #d #ltOn @(lt_O_n_elim … ltOn) <plus_n_O //
  |#m #Hind #n #j #a #d #Hlt lapply Hlt @(lt_O_n_elim … (ltn_to_ltO … Hlt)) 
   #p <plus_n_Sm #ltmp @Hind @le_S_S_to_le //  
  ]
qed. *)

(*
lemma mk_config_eq_s: ∀S,sig,s1,s2,t1,t2. 
  mk_config S sig s1 t1 = mk_config S sig s2 t2 → s1=s2.
#S #sig #s1 #s2 #t1 #t2 #H destruct //
qed.

lemma mk_config_eq_t: ∀S,sig,s1,s2,t1,t2. 
  mk_config S sig s1 t1 = mk_config S sig s2 t2 → s1=s2.
#S #sig #s1 #s2 #t1 #t2 #H destruct //
qed.
*)

theorem sem_inject: ∀sig.∀M:TM sig.∀R.∀n,i.
 i≤n → M ⊨ R → inject_TM sig M n i ⊨ inject_R sig R n i. 
#sig #M #R #n #i #lein #HR #vt cases (HR (nth i ? vt (niltape ?)))
#k * * #outs #outt * #Hloop #HRout @(ex_intro ?? k) 
@(ex_intro ?? (mk_mconfig ?? n outs (change_vec ? (S n) vt outt i))) % 
  [elim k in Hloop;
    [normalize in ⊢ (%\to ?); #H destruct
    |#k0 #Hind whd in ⊢ (??%?→??%?);
     >halt_inject whd in match (cstate ????);
     whd in match (cstate sig (states sig M)
       (initc sig M (nth i (tape sig) vt (niltape sig)))); 
     cases (true_or_false (halt sig M (start sig M))) #Hhalt >Hhalt 
     whd in ⊢ (??%?→??%?);
      [#H @eq_f whd in ⊢ (??%?); lapply (de_option ??? H) -H 
       whd  in ⊢ (??%?→?); #H @eq_f2  
        [whd in ⊢ (??%?); destruct (H) //
        |@(eq_vec … (niltape ?)) #j #lejn
         cases (true_or_false (eqb i j)) #eqij
          [>(eqb_true_to_eq … eqij) >nth_change_vec //
           <(eqb_true_to_eq … eqij) destruct (H) //
          |>nth_change_vec_neq // @(eqb_false_to_not_eq … eqij)
          ]
        ]
      |#H <Hind //
  |%[>nth_change_vec // @le_S_S //
    |#j #i >nth_change_vec_neq //
    ]
  ]
          
  
  

  



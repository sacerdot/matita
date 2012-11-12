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
  let nai ≝ λj.if (eqb j i) then na else (None ?) in
  〈q, make_veci ? nai (S n) 0〉.
  
definition inject_TM ≝ λsig.λM:TM sig.λn,i.
  mk_mTM sig n
    (states ? M)
    (inject_trans ?? n i (trans ? M))
    (start ? M)
    (halt ? M).

definition inject_R ≝ λsig.λR:relation (tape sig).λn,i:nat.
  λv1,v2: (Vector (tape sig) (S n)).
  R (nth i ? v1 (niltape ?)) (nth i ? v2 (niltape ?)) ∧
  ∀j. j ≠ i → nth j ? v1 (niltape ?) = nth j ? v2 (niltape ?). 

lemma nth_make : ∀A,i,n,j,a,d. i < n → nth i ? (make_veci A a n j) d = a (j+i).
#A #i elim i
  [#n #j #a #d #ltOn @(lt_O_n_elim … ltOn) <plus_n_O //
  |#m #Hind #n #j #a #d #Hlt lapply Hlt @(lt_O_n_elim … (ltn_to_ltO … Hlt)) 
   #p <plus_n_Sm #ltmp @Hind @le_S_S_to_le //  
  ]
qed.

theorem sem_inject: ∀sig.∀M:TM sig.∀R.∀n,i.
 i≤n → M ⊨ R → inject_TM sig M n i ⊨ inject_R sig R n i. 
#sig #M #R #n #i #lein #HR #vt cases (HR (nth i ? vt (niltape ?)))
#k * * #outs #outt * #Hloop #HRout @(ex_intro ?? k) 
@(ex_intro ?? (mk_mconfig ?? n outs ?) )
  [(* this is the vector of tapes in the last mk_config *)
   @(make_veci ? (λj.if (eqb j i) then outt else (nth j ? vt (niltape ?))) (S n) 0) 
  |% 
    [
    |%[>nth_make [>(eq_to_eqb_true … (refl ? i)) @HRout|@le_S_S //]
      |#j #neqji >nth_make [>(not_eq_to_eqb_false … neqji) // |@le_S_S //]
       normalize
       
  
  

  



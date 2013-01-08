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
include "turing/inject.ma".
include "turing/while_multi.ma".

definition partest_states ≝ initN 3.

definition partest0 : partest_states ≝ mk_Sig ?? 0 (leb_true_to_le 1 3 (refl …)).
definition partest1 : partest_states ≝ mk_Sig ?? 1 (leb_true_to_le 2 3 (refl …)).
definition partest2 : partest_states ≝ mk_Sig ?? 2 (leb_true_to_le 3 3 (refl …)).

definition trans_partest ≝ 
 λsig,n,test.
 λp:partest_states × (Vector (option sig) (S n)).
 let 〈q,a〉 ≝ p in
 if test a then 〈partest1,null_action sig n〉 
 else 〈partest2,null_action ? n〉.

definition partest ≝ 
  λsig,n,test.
  mk_mTM sig n partest_states (trans_partest sig n test) 
    partest0 (λq.q == partest1 ∨ q == partest2).

definition R_partest_true ≝ 
  λsig,n,test.λint,outt: Vector (tape sig) (S n).
  test (current_chars ?? int) = true ∧ outt = int.
  
definition R_partest_false ≝ 
  λsig,n,test.λint,outt: Vector (tape sig) (S n).
  test (current_chars ?? int) = false ∧ outt = int.

lemma partest_q0_q1:
  ∀sig,n,test,v.
  test (current_chars ?? v) = true → 
  step sig n (partest sig n test)(mk_mconfig ??? partest0 v) 
    = mk_mconfig ??? partest1 v.
#sig #n #test #v #Htest
whd in ⊢ (??%?); >(eq_pair_fst_snd … (trans ????)) whd in ⊢ (??%?);
@eq_f2
[ whd in ⊢ (??(???%)?); >Htest %
| whd in ⊢ (??(????(???%))?); >Htest @tape_move_null_action ]
qed.

lemma partest_q0_q2:
  ∀sig,n,test,v.
  test (current_chars ?? v) = false → 
  step sig n (partest sig n test)(mk_mconfig ??? partest0 v) 
    = mk_mconfig ??? partest2 v.
#sig #n #test #v #Htest
whd in ⊢ (??%?); >(eq_pair_fst_snd … (trans ????)) whd in ⊢ (??%?);
@eq_f2
[ whd in ⊢ (??(???%)?); >Htest %
| whd in ⊢ (??(????(???%))?); >Htest @tape_move_null_action ]
qed.

lemma sem_partest:
  ∀sig,n,test.
  partest sig n test ⊨ 
    [ partest1: R_partest_true sig n test, R_partest_false sig n test ].
#sig #n #test #int
cases (true_or_false (test (current_chars ?? int))) #Htest
[ %{2} %{(mk_mconfig ? partest_states n partest1 int)} %
  [ % [ whd in ⊢ (??%?); >partest_q0_q1 /2/ | #_ % // ] 
  | * #H @False_ind @H %
  ]
| %{2} %{(mk_mconfig ? partest_states n partest2 int)} %
  [ % [ whd in ⊢ (??%?); >partest_q0_q2 /2/ 
      | whd in ⊢ (??%%→?); #H destruct (H)]
  | #_ % //]
]
qed.
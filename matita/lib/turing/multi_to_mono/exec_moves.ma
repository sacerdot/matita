(* include "turing/auxiliary_machines.ma". *)

include "turing/multi_to_mono/exec_trace_move.ma".
(* include "turing/turing.ma". *)

let rec exec_moves sig n i on i : TM (multi_sig sig n) ≝
  match i with 
  [ O ⇒ nop ? (* exec_move_i sig n 0 *)
  | S j ⇒ seq ? (exec_moves sig n j) (exec_move_i sig n j) 
  ].
     
axiom get_moves : ∀sig,n.∀a:multi_sig sig n.∀i.Vector DeqMove i.

axiom get_moves_cons: ∀sig,n,a,j.j < n → 
 get_moves sig n a (S j) = 
 vec_cons ? (get_move ? n a j) j (get_moves sig n a j).
 
definition a_moves ≝ 
  λsig,n.λactions: Vector ((option sig) × move) n. 
  vec_map ?? (snd ??) n actions.
  
definition a_chars ≝ 
  λsig,n.λactions: Vector ((option sig) × move) n. 
  vec_map ?? (fst ??) n actions.

definition tape_moves ≝ 
  λsig,n,ts,mvs.
  pmap_vec ??? (tape_move sig) n ts mvs.
  
lemma tape_moves_def : ∀sig,n,ts,mvs.
  tape_moves sig n ts mvs = pmap_vec ??? (tape_move sig) n ts mvs.
// qed.
 
definition tape_writem ≝ 
  λsig,n,ts,chars.
  pmap_vec ??? (tape_write sig) n ts chars.

(*
axiom actions_commute : ∀sig,n,ts,actions.
  tape_moves sig n (tape_writem ?? ts (a_chars … actions)) (a_moves … actions) = 
    tape_move_multi ?? ts actions. *)

(* devo rafforzare la semantica, dicendo che i tape non toccati
dalle moves non cambiano *)

definition R_exec_moves ≝ λsig,n,i,t1,t2.
∀a,ls,rs. 
  t1 = midtape ? ls a rs → 
  (∀i.regular_trace sig n a ls rs i) → 
  nth n ? (vec … a) (blank ?) = head ? → 
  no_head_in … ls →
  no_head_in … rs →
  ∃ls1,a1,rs1. 
   t2 = midtape (multi_sig sig n) ls1 a1 rs1 ∧
   (∀i.regular_trace sig n a1 ls1 rs1 i) ∧
   readback sig n ls1 (vec … a1) rs1 i = 
     tape_moves ?? (readback sig n ls (vec … a) rs i) (get_moves sig n a i) ∧
   (∀j. i ≤ j → j ≤ n →  
    rb_trace_i sig n ls1 (vec … a1) rs1 j = 
      rb_trace_i sig n ls (vec … a) rs j).
     
(* alias id "Realize_to_Realize" = 
  "cic:/matita/turing/mono/Realize_to_Realize.def(13)". *)

lemma nth_readback: ∀sig,n,ls,a,rs,j,i. i < j →
 nth i ? (readback sig n ls a rs j) (niltape ?) = 
   rb_trace_i sig n ls a rs (j - S i).
#sig #n #ls #a #rs #j elim j
  [#i #lti0 @False_ind /2/
  |-j #j #Hind *
    [#_ >minus_S_S <minus_n_O % 
    |#m #Hmj >minus_S_S @Hind @le_S_S_to_le //
    ]
  ]
qed.

lemma sem_exec_moves: ∀sig,n,i. i < n → 
  exec_moves sig n i ⊨ R_exec_moves sig n i.
#sig #n #i elim i 
  [#_ @(Realize_to_Realize … (sem_nop …))
   #t1 #t2 #H #a #ls #rs #Ht1 #Hreg #H1 #H2 #H3 
   %{ls} %{a} %{rs} %[% >H [%[@Ht1|@Hreg]| %]|//]
  |#j #Hind #lttj lapply (lt_to_le … lttj) #ltj
   @(sem_seq_app … (Hind ltj) (sem_exec_move_i … ltj)) -Hind
   #int #outt * #t1 * #H1 #H2
   #a #ls #rs #Hint #H3 #H4 #H5 #H6
   lapply (H1 … Hint H3 H4 H5 H6)
   * #ls1 * #a1 * #rs1 * * * #H7 #H8 #H9 #H10
   lapply (reg_inv … (H8 n) ? H4 H5 H6)
    [@H10 [@lt_to_le @ltj |@le_n]]
   -H3 -H4 -H5 -H6 * * #H3 #H4 #H5
   lapply (H2 … H7 H8 H3 H4 H5)
   * #ls2 * #a2 * #rs2 * * * #Houtt #Hregout #Hrboutt #Hrbid
   %{ls2} %{a2} %{rs2} 
   cut (∀i. get_move sig n a i = get_move sig n a1 i)
     [@daemon] #aa1
   %[%[%[@Houtt|@Hregout]
      |whd in ⊢ (??%?); @Vector_eq >(get_moves_cons … ltj)
       >tape_moves_def >pmap_vec_cons @eq_f2
        [<H10 [>aa1 @Hrboutt |@lt_to_le @ltj |@le_n]
        |<tape_moves_def <H9 (* mitico *) @eq_f 
         @(eq_vec … (niltape ?)) #i #ltij 
         >(nth_readback … ltij) >(nth_readback … ltij) @Hrbid 
          [@(transitive_le … ltj) // |@lt_to_not_eq @lt_plus_to_minus //]
        ]
      ]
    |#a #Hja #Han >(Hrbid … Han) 
      [@(H10 … Han) @lt_to_le @Hja |@sym_not_eq @lt_to_not_eq @Hja ]
    ]
  ]
qed.
  














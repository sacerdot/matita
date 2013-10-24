(* include "turing/auxiliary_machines.ma". *)

include "turing/multi_to_mono/exec_trace_move.ma".
(* include "turing/turing.ma". *)

(**************************** Vector Operations *******************************)

let rec resize A (l:list A) i d on i ≝
  match i with 
  [ O ⇒ [ ]
  | S j ⇒ (hd ? l d)::resize A (tail ? l) j d
  ].

lemma length_resize : ∀A,l,i,d. |resize A l i d| = i.
#A #l #i lapply l -l elim i 
  [#l #d % 
  |#m #Hind #l cases l 
    [#d normalize @eq_f @Hind
    |#a #tl #d normalize @eq_f @Hind
    ]
  ]
qed.

lemma resize_id : ∀A,n,l,d. |l| = n → 
  resize A l n d = l.
#A #n elim n 
  [#l #d #H >(lenght_to_nil … H) //
  |#m #Hind * #d normalize 
    [#H destruct |#a #tl #H @eq_f @Hind @injective_S // ]
  ]
qed.

definition resize_vec :∀A,n.Vector A n → ∀i.A→Vector A i.
#A #n #a #i #d @(mk_Vector A i (resize A a i d) ) @length_resize
qed.

axiom nth_resize_vec :∀A,n.∀v:Vector A n.∀d,i,j. i < j →i < n →
  nth i ? (resize_vec A n v j d) d = nth i ? v d.
  
lemma resize_vec_id : ∀A,n.∀v:Vector A n.∀d. 
  resize_vec A n v n d = v.
#A #n #v #d @(eq_vec … d) #i #ltin @nth_resize_vec //
qed.

definition vec_single: ∀A,a. Vector A 1 ≝ λA,a.
  mk_Vector A 1 [a] (refl ??).
  
definition vec_cons_right : ∀A.∀a:A.∀n. Vector A n → Vector A (S n).
#A #a #n #v >(plus_n_O n) >plus_n_Sm @(vec_append … v (vec_single A a))
>length_append >(len A n v) //
qed.

lemma eq_cons_right : ∀A,a1,a2.∀n.∀v1,v2:Vector A n.
  a1 = a2 → v1 = v2 → vec_cons_right A a1 n v1 = vec_cons_right A a2 n v2.
// qed.

axiom nth_cons_right: ∀A.∀a:A.∀n.∀v:Vector A n.∀d. 
  nth n ? (vec_cons_right A a n v) d = a.
(*
#A #a #n elim n 
  [#v #d >(vector_nil … v) //
  |#m #Hind #v #d >(vec_expand … v) whd in ⊢ (??%?);    
   whd in match (vec_cons_right ????);  
*)

lemma get_moves_cons_right: ∀Q,sig,n,q,moves,a.
  get_moves Q sig (S n)
    (vec_cons_right ? (Some ? (inl ?? 〈q,moves〉)) (S n) a) = moves.
#Q #sig #n #q #moves #a whd in ⊢(??%?); >nth_cons_right //
qed.
    
axiom resize_cons_right: ∀A.∀a:A.∀n.∀v:Vector A n.∀d. 
  resize_vec ? (S n) (vec_cons_right A a n v) n d = v.
  
let rec exec_moves Q sig n i on i : TM (MTA (HC Q n) sig (S n)) ≝
  match i with 
  [ O ⇒ nop ? (* exec_move_i sig n 0 *)
  | S j ⇒ seq ? (exec_moves Q sig n j) (exec_move_i Q sig n j) 
  ].

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
let rec i_moves a i on i : Vector move i ≝
  match i with 
  [ O ⇒ mk_Vector ? 0 (nil ?) (refl ??)
  | S j ⇒ vec_cons ? (nth j ? a N) j (i_moves a j)
  ]. *)

definition vec_moves ≝ λQ,sig,n,a,i. 
  resize_vec … (get_moves Q sig n a) i N.

axiom vec_moves_cons: ∀Q,sig,n,a,j.j < n → 
 vec_moves Q sig n a (S j) = 
 vec_cons ? (get_move Q ? n a j) j (vec_moves Q sig n a j).

(*
axiom actions_commute : ∀sig,n,ts,actions.
  tape_moves sig n (tape_writem ?? ts (a_chars … actions)) (a_moves … actions) = 
    tape_move_multi ?? ts actions. *)

(* devo rafforzare la semantica, dicendo che i tape non toccati
dalle moves non cambiano *)


definition R_exec_moves ≝ λQ,sig,n,i,t1,t2.
∀a,ls,rs. 
  t1 = midtape ? ls a rs → 
  (∀i.regular_trace (TA (HC Q n) sig) (S n) a ls rs i) → 
  is_head ?? (nth n ? (vec … a) (blank ?)) = true →  
  no_head_in … ls →
  no_head_in … rs →
  ∃ls1,a1,rs1. 
   t2 = midtape (MTA (HC Q n) sig (S n)) ls1 a1 rs1 ∧
   (∀i.regular_trace (TA (HC Q n) sig) (S n) a1 ls1 rs1 i) ∧
   readback ? (S n) ls1 (vec … a1) rs1 i = 
     tape_moves ?? (readback ? (S n) ls (vec … a) rs i) (vec_moves Q sig n a i) ∧
   (∀j. i ≤ j → j ≤ n →  
    rb_trace_i ? (S n) ls1 (vec … a1) rs1 j = 
      rb_trace_i ? (S n) ls (vec … a) rs j).
     
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

lemma sem_exec_moves: ∀Q,sig,n,i. i ≤ n → 
  exec_moves Q sig n i ⊨ R_exec_moves Q sig n i.
#Q #sig #n #i elim i 
  [#_ @(Realize_to_Realize … (sem_nop …))
   #t1 #t2 #H #a #ls #rs #Ht1 #Hreg #H1 #H2 #H3 
   %{ls} %{a} %{rs} %[% >H [%[@Ht1|@Hreg]| %]|//]
  |#j #Hind #lttj lapply (lt_to_le … lttj) #ltj
   @(sem_seq_app … (Hind ltj) (sem_exec_move_i … lttj)) -Hind
   #int #outt * #t1 * #H1 #H2
   #a #ls #rs #Hint #H3 #H4 #H5 #H6
   lapply (H1 … Hint H3 H4 H5 H6)
   * #ls1 * #a1 * #rs1 * * * #H7 #H8 #H9 #H10
   lapply (reg_inv … (H8 n) ? H4 H5 H6)
    [@H10 [@ltj |@le_n]]
   -H3 -H4 -H5 -H6 * * #H3 #H4 #H5
   lapply (H2 … H7 H8 H3 H4 H5)
   * #ls2 * #a2 * #rs2 * * * #Houtt #Hregout #Hrboutt #Hrbid
   %{ls2} %{a2} %{rs2} 
   cut (∀i. get_move Q sig n a i = get_move Q sig n a1 i)
     [@daemon] #aa1
   %[%[%[@Houtt|@Hregout]
      |whd in ⊢ (??%?); @Vector_eq >(vec_moves_cons … lttj)
       >tape_moves_def >pmap_vec_cons @eq_f2
        [<H10 [>aa1 @Hrboutt |@ltj |@le_n]
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
  














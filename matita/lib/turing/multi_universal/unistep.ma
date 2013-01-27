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


include "turing/multi_universal/unistep_aux.ma".

definition exec_move ≝ 
  cfg_to_obj · tape_move_obj · restart_tape prg 2 · obj_to_cfg.

definition R_exec_move ≝ λt1,t2:Vector (tape FSUnialpha) 3.
∀c,m,ls1,ls2,rs2.
  nth cfg ? t1 (niltape ?) = mk_tape FSUnialpha (c::ls1@[bar]) (None ?) [ ] → 
  nth prg ? t1 (niltape ?) = midtape FSUnialpha (ls2@[bar]) m rs2 →
  only_bits (list_of_tape ? (nth obj ? t1 (niltape ?))) →
  c ≠ bar → m ≠ bar →
  let new_obj ≝ 
      tape_move_mono ? (nth obj ? t1 (niltape ?)) 
        〈char_to_bit_option c, char_to_move m〉 in
  let next_c ≝ low_char' (current ? new_obj) in 
  let new_cfg ≝ midtape ? [ ] bar ((reverse ? ls1)@[next_c]) in 
  let new_prg ≝ midtape FSUnialpha [ ] bar ((reverse ? ls2)@m::rs2) in
  t2 = Vector_of_list ? [new_obj;new_cfg;new_prg].


lemma sem_exec_move: exec_move ⊨ R_exec_move.
@(sem_seq_app ??????? sem_cfg_to_obj1
  (sem_seq ?????? sem_tape_move_obj
   (sem_seq ?????? (sem_restart_tape ???) sem_obj_to_cfg1))) //
#ta #tout * #t1 * #semM1 * #t2 * #semM2 * #t3 * #semM3 #semM4 
#c #m #ls1 #ls2 #rs2 #Hcfg #Hprg #Honlybits #Hc #Hm 
(* M1 = cfg_to_obj *)
lapply (semM1 … Hcfg Hc) #Ht1 
(* M2 = tape_move *)
whd in semM2; >Ht1 in semM2; -Ht1
>nth_change_vec_neq [2:@eqb_false_to_not_eq %] 
>nth_change_vec_neq [2:@eqb_false_to_not_eq %] 
>Hprg #Ht2 lapply (Ht2 … (refl ??)) -Ht2
>nth_change_vec_neq [2:@eqb_false_to_not_eq %]
>nth_change_vec // >change_vec_commute [2:@eqb_false_to_not_eq %]
>change_vec_change_vec #Ht2 
(* M3 = restart prg *) 
whd in semM3; >Ht2 in semM3; #semM3 lapply (semM3 … (refl ??)); -semM3
>nth_change_vec_neq [2:@eqb_false_to_not_eq %] 
>nth_change_vec_neq [2:@eqb_false_to_not_eq %] #Ht3
(* M4 = obj_to_cfg *) 
whd in semM4; >Ht3 in semM4; 
>nth_change_vec_neq [2:@eqb_false_to_not_eq %]
>nth_change_vec [2:@leb_true_to_le %] #semM4 lapply (semM4 … (refl ??)) -semM4
>nth_change_vec_neq [2:@eqb_false_to_not_eq %]
>nth_change_vec_neq [2:@eqb_false_to_not_eq %]
>nth_change_vec [2:@leb_true_to_le %] #semM4 >(semM4 ?)
  [(* tape by tape *)
   @(eq_vec … (niltape ?)) #i #lei2 
   cases (le_to_or_lt_eq … (le_S_S_to_le …lei2))
    [#lei1 cases (le_to_or_lt_eq … (le_S_S_to_le …lei1))
      [#lei0 lapply(le_n_O_to_eq … (le_S_S_to_le …lei0)) #eqi <eqi
       >nth_change_vec_neq [2:@eqb_false_to_not_eq %]
       >nth_change_vec_neq [2:@eqb_false_to_not_eq %]
       >nth_change_vec_neq [2:@eqb_false_to_not_eq %]
       >nth_change_vec [2:@leb_true_to_le %] %
      |#Hi >Hi (* obj tape *)
       >nth_change_vec [2:@leb_true_to_le %] whd in ⊢ (???%);
       >reverse_cons >reverse_append >reverse_single 
       whd in match (option_hd ??); whd in match (tail ??);
       whd in ⊢ (??%?); %
      ]
    |#Hi >Hi (* prg tape *)
     >nth_change_vec_neq [2:@eqb_false_to_not_eq %]
     >nth_change_vec [2:@leb_true_to_le %] whd in ⊢ (???%);
     >Hprg whd in match (list_of_tape ??); >reverse_append
     >reverse_single % 
    ]
  |
       
definition unistep ≝ 
  match_m cfg prg FSUnialpha 2 · 
  restart_tape cfg 2 · mmove cfg ? 2 R · copy prg cfg FSUnialpha 2 ·
  cfg_to_obj · tape_move_obj · restart_tape prg 2 · obj_to_cfg.

(*
definition legal_tape ≝ λn,l,h,t.
  ∃state,char,table.
  nth cfg ? t1 (niltape ?) = midtape ? [ ] bar (state@[char]) →
  is_config n (bar::state@[char]) →  
  nth prg ? t1 (niltape ?) = midtape ? [ ] bar table →
  bar::table = table_TM n l h → *)

definition R_unistep ≝ λn,l,h.λt1,t2: Vector ? 3.
  ∀state,char,table.
  (* cfg *)
  nth cfg ? t1 (niltape ?) = midtape ? [ ] bar (state@[char]) →
  is_config n (bar::state@[char]) →  
  (* prg *)
  nth prg ? t1 (niltape ?) = midtape ? [ ] bar table →
  bar::table = table_TM n l h →
  (* obj *)
  only_bits (list_of_tape ? (nth obj ? t1 (niltape ?))) →
  let conf ≝ (bar::state@[char]) in
  (∃ll,lr.bar::table = ll@conf@lr) →
(*
    ∃nstate,nchar,m,t. tuple_encoding n h t = (conf@nstate@[nchar;m]) ∧ 
    mem ? t l ∧  *)
    ∀nstate,nchar,m,t. 
    tuple_encoding n h t = (conf@nstate@[nchar;m])→ 
    mem ? t l →
    let new_obj ≝ 
     tape_move_mono ? (nth obj ? t1 (niltape ?)) 
       〈char_to_bit_option nchar,char_to_move m〉 in
    let next_char ≝ low_char' (current ? new_obj) in
    t2 = 
      change_vec ??
        (change_vec ?? t1 (midtape ? [ ] bar (nstate@[next_char])) cfg)
        new_obj obj.
        
lemma lt_obj : obj < 3. // qed.
lemma lt_cfg : cfg < 3. // qed.
lemma lt_prg : prg < 3. // qed.

definition R_copy_strict ≝ 
  λsrc,dst,sig,n.λint,outt: Vector (tape sig) (S n).
  ((current ? (nth src ? int (niltape ?)) = None ? ∨
    current ? (nth dst ? int (niltape ?)) = None ?) → outt = int) ∧
  (∀ls,x,x0,rs,ls0,rs0. 
    nth src ? int (niltape ?) = midtape sig ls x rs →
    nth dst ? int (niltape ?) = midtape sig ls0 x0 rs0 →
    |rs0| ≤ |rs| → 
    (∃rs1,rs2.rs = rs1@rs2 ∧ |rs1| = |rs0| ∧
     outt = change_vec ?? 
            (change_vec ?? int  
              (mk_tape sig (reverse sig rs1@x::ls) (option_hd sig rs2)
            (tail sig rs2)) src)
            (mk_tape sig (reverse sig rs1@x::ls0) (None sig) []) dst)).

axiom sem_copy_strict : ∀src,dst,sig,n. src ≠ dst → src < S n → dst < S n → 
  copy src dst sig n ⊨ R_copy_strict src dst sig n.

lemma sem_unistep : ∀n,l,h.unistep ⊨ R_unistep n l h.
#n #l #h
@(sem_seq_app ??????? (sem_match_m cfg prg FSUnialpha 2 ???)
  (sem_seq ?????? (sem_restart_tape ???)
   (sem_seq ?????? (sem_move_multi ? 2 cfg R ?)
    (sem_seq ?????? (sem_copy_strict prg cfg FSUnialpha 2 ???)
     (sem_seq ?????? sem_cfg_to_obj1
      (sem_seq ?????? sem_tape_move_obj
       (sem_seq ?????? (sem_restart_tape ???) sem_obj_to_cfg)))))))
  /2 by le_n,sym_not_eq/
#ta #tb #HR #state #char #table #Hta_cfg #Hcfg #Hta_prg #Htable
#Hbits_obj #Htotaltable
#nstate #nchar #m #t #Htuple #Hmatch
cases HR -HR #tc * whd in ⊢ (%→?); 
>Hta_cfg #H cases (H ?? (refl ??)) -H 
(* prg starts with a bar, so it's not empty *) #_
>Hta_prg #H lapply (H ??? (refl ??)) -H *
[| cases Htotaltable #ll * #lr #H >H 
   #Hfalse @False_ind cases (Hfalse ll lr) #H1 @H1 //]
* #ll * #lr * #Hintable -Htotaltable #Htc
* #td * whd in ⊢ (%→?); >Htc
>nth_change_vec_neq [|@sym_not_eq //] >(nth_change_vec ?????? lt_cfg)
#Htd lapply (Htd ? (refl ??)) -Htd
>change_vec_commute [|@sym_not_eq //] >change_vec_change_vec
>(?: list_of_tape ? (mk_tape ? (reverse ? (state@[char])@[bar]) (None ?) [ ]) =
     bar::state@[char]) 
[|whd in ⊢ (??%?); >left_mk_tape >reverse_append >reverse_reverse
  >current_mk_tape >right_mk_tape normalize >append_nil % ]
whd in ⊢ (???(???(????%?)??)→?); whd in match (tail ??); #Htd
(* move cfg to R *)
* #te * whd in ⊢ (%→?); >Htd
>change_vec_commute [|@sym_not_eq //] >change_vec_change_vec
>nth_change_vec_neq [|@sym_not_eq //] >nth_change_vec //
>Htable in Hintable; #Hintable #Hte
(* copy *)
cases (cfg_in_table_to_tuple ???? Hcfg ?? Hintable)
#newstate * #m0 * #lr0 * * #Hlr destruct (Hlr) #Hnewcfg #Hm0
cut (∃fo,so,co.state = fo::so@[co] ∧ |so| = n)
[ @daemon ] * #fo * #so * #co * #Hstate_exp #Hsolen
cut (∃fn,sn,cn.newstate = fn::sn@[cn] ∧ |sn| = n)
[ @daemon ] * #fn * #sn * #cn * #Hnewstate_exp #Hsnlen
* #tf * * #_ >Hte >(nth_change_vec ?????? lt_prg)
>nth_change_vec_neq [|@sym_not_eq //] >(nth_change_vec ?????? lt_cfg)
>Hstate_exp >Hnewstate_exp
whd in match (mk_tape ????); whd in match (tape_move ???);
#Htf cases (Htf ?????? (refl ??) (refl ??) ?) -Htf
[| whd in match (tail ??); >length_append >length_append 
   >Hsolen >length_append >length_append >Hsnlen 
   <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_O <plus_n_O normalize // ]
#rs1 * #rs2 whd in match (tail ??); * *
>append_cons #Hrs1rs2 #Hrs1len
>change_vec_change_vec >change_vec_commute [|@sym_not_eq //]
>change_vec_change_vec #Htf 
(* cfg to obj *)
* #tg * whd in ⊢ (%→?); >Htf
>nth_change_vec_neq [|@sym_not_eq //] >(nth_change_vec ?????? lt_cfg)
lapply (append_l1_injective ?????? Hrs1rs2)
[ >Hsnlen >Hrs1len >length_append >length_append >length_append >length_append
  normalize >Hsolen >Hsnlen % ] #Hrs1 <Hrs1 >reverse_append >reverse_single
  >associative_append #Htg lapply (Htg … (refl ??) Hm0) -Htg
  (* simplifying tg *)
  >nth_change_vec_neq [2:@eqb_false_to_not_eq %]
  >nth_change_vec_neq [2:@eqb_false_to_not_eq %]





  cut ((mk_tape FSUnialpha []
     (option_hd FSUnialpha
      (reverse FSUnialpha (m0::[]@reverse FSUnialpha (sn@[cn])@[fn; bar])))
     (tail FSUnialpha
      (reverse FSUnialpha (m0::[]@reverse FSUnialpha (sn@[cn])@[fn; bar])))) =
      midtape ? [ ] bar (fn::sn@[cn;m0]))
  [cut (reverse FSUnialpha (m0::[]@reverse FSUnialpha (sn@[cn])@[fn; bar]) =
          bar::fn::sn@[cn;m0])
    [>reverse_cons whd in ⊢ (??(??(??%)?)?); >reverse_append >reverse_reverse
     >append_cons in ⊢ (???%); % ] #Hrev >Hrev % ] #Hmk_tape >Hmk_tape -Hmk_tape
   >change_vec_commute

  >reverse_append >reverse_append
  check reverse_cons
  <reverse_cons >reverse_cons
   -Htg #Htg 

>(change_vec_commute ????? cfg prg) [2:@eqb_false_to_not_eq %]
>nth_change_vec_neq [2:@eqb_false_to_not_eq %]
>nth_change_vec_neq [2:@eqb_false_to_not_eq %]
lapply (append_l1_injective ?????? Hrs1rs2)
[ >Hsnlen >Hrs1len >length_append >length_append >length_append >length_append
  normalize >Hsolen >Hsnlen % ]
#Hrs1 <Hrs1 >reverse_append #Htg cases (Htg ?? (refl ??)) -Htg
cases m0
  [#mv #_ #Htg #_

   
      
      

[ * 
 
  match_m cfg prg FSUnialpha 2 ·
  restart_tape cfg · copy prg cfg FSUnialpha 2 ·
  cfg_to_obj · tape_move_obj · restart_tape prg · obj_to_cfg.

definition tape_map ≝ λA,B:FinSet.λf:A→B.λt.
  mk_tape B (map ?? f (left ? t)) 
    (option_map ?? f (current ? t)) 
    (map ?? f (right ? t)).
    
lemma map_list_of_tape: ∀A,B,f,t.
  list_of_tape B (tape_map ?? f t) = map ?? f (list_of_tape A t).
#A #B #f * // normalize // #ls #c #rs <map_append %
qed.

lemma low_char_current : ∀t.
  low_char' (current FSUnialpha (tape_map FinBool FSUnialpha bit t))
  = low_char (current FinBool t).
* // qed.

definition low_tapes: ∀M:normalTM.∀c:nconfig (no_states M).Vector ? 3 ≝ 
λM:normalTM.λc:nconfig (no_states M).Vector_of_list ?
  [tape_map ?? bit (ctape ?? c);
   midtape ? [ ] bar 
    ((bits_of_state ? (nhalt M) (cstate ?? c))@[low_char (current ? (ctape ?? c))]);
   midtape ? [ ] bar (tail ? (table_TM ? (graph_enum ?? (ntrans M)) (nhalt M)))
  ].

lemma obj_low_tapes: ∀M,c.
  nth obj ? (low_tapes M c) (niltape ?) = tape_map ?? bit (ctape ?? c).
// qed.

lemma cfg_low_tapes: ∀M,c.
  nth cfg ? (low_tapes M c) (niltape ?) = 
  midtape ? [ ] bar 
    ((bits_of_state ? (nhalt M) (cstate ?? c))@[low_char (current ? (ctape ?? c))]).
// qed.

lemma prg_low_tapes: ∀M,c.
  nth prg ? (low_tapes M c) (niltape ?) = 
  midtape ? [ ] bar (tail ? (table_TM ? (graph_enum ?? (ntrans M)) (nhalt M))).
// qed.

(* commutation lemma for write *)
lemma map_write: ∀t,cout.
 tape_write ? (tape_map FinBool ? bit t) (char_to_bit_option (low_char cout))
  = tape_map ?? bit (tape_write ? t cout).
#t * // #b whd in match (char_to_bit_option ?);
whd in ⊢ (??%%); @eq_f3 [elim t // | // | elim t //]
qed.

(* commutation lemma for moves *)
lemma map_move: ∀t,m.
 tape_move ? (tape_map FinBool ? bit t) (char_to_move (low_mv m))
  = tape_map ?? bit (tape_move ? t m).
#t * // whd in match (char_to_move ?);
  [cases t // * // | cases t // #ls #a * //]
qed.
  
(* commutation lemma for actions *)
lemma map_action: ∀t,cout,m.
 tape_move ? (tape_write ? (tape_map FinBool ? bit t)
    (char_to_bit_option (low_char cout))) (char_to_move (low_mv m)) 
 = tape_map ?? bit (tape_move ? (tape_write ? t cout) m).
#t #cout #m >map_write >map_move % 
qed. 

lemma map_move_mono: ∀t,cout,m.
 tape_move_mono ? (tape_map FinBool ? bit t)
  〈char_to_bit_option (low_char cout), char_to_move (low_mv m)〉
 = tape_map ?? bit (tape_move_mono ? t 〈cout,m〉).
@map_action
qed. 

definition R_unistep_high ≝ λM:normalTM.λt1,t2.
∀c:nconfig (no_states M).
  t1 = low_tapes M c → 
  t2 = low_tapes M (step ? M c). 

lemma R_unistep_equiv : ∀M,t1,t2. 
  R_unistep (no_states M) (graph_enum ?? (ntrans M)) (nhalt M) t1 t2 →
  R_unistep_high M t1 t2.
#M #t1 #t2 #H whd whd in match (nconfig ?); #c #Ht1
lapply (initial_bar ? (nhalt M) (graph_enum ?? (ntrans M)) (nTM_nog ?)) #Htable
(* tup = current tuple *)
cut (∃t.t = 〈〈cstate … c,current ? (ctape … c)〉, 
             ntrans M 〈cstate … c,current ? (ctape … c)〉〉) [% //] * #tup #Htup
(* tup is in the graph *)
cut (mem ? tup (graph_enum ?? (ntrans M)))
  [@memb_to_mem >Htup @(graph_enum_complete … (ntrans M)) %] #Hingraph
(* tupe target = 〈qout,cout,m〉 *)
lapply (decomp_target ? (ntrans M 〈cstate … c,current ? (ctape … c)〉))
* #qout * #cout * #m #Htg >Htg in Htup; #Htup
(* new config *)
cut (step FinBool M c = mk_config ?? qout (tape_move ? (tape_write ? (ctape … c) cout) m))
  [>(config_expand … c) whd in ⊢ (??%?); (* >Htg ?? why not?? *)
   cut (trans ? M 〈cstate  … c, current ? (ctape … c)〉 = 〈qout,cout,m〉) [<Htg %] #Heq1 
   >Heq1 %] #Hstep
(* new state *)
cut (cstate ?? (step FinBool M c) = qout) [>Hstep %] #Hnew_state
(* new tape *)
cut (ctape ?? (step FinBool M c) = tape_move ? (tape_write ? (ctape … c) cout) m)
  [>Hstep %] #Hnew_tape
lapply(H (bits_of_state ? (nhalt M) (cstate ?? c)) 
         (low_char (current ? (ctape ?? c)))
         (tail ? (table_TM ? (graph_enum ?? (ntrans M)) (nhalt M)))
         ??????)
[<Htable
 lapply(list_to_table … (nhalt M) …Hingraph) * #ll * #lr #Htable1 %{ll} 
 %{(((bits_of_state ? (nhalt M) qout)@[low_char cout;low_mv m])@lr)} 
 >Htable1 @eq_f <associative_append @eq_f2 // >Htup
 whd in ⊢ (??%?); @eq_f >associative_append %
|>Ht1 >obj_low_tapes >map_list_of_tape elim (list_of_tape ??) 
  [#b @False_ind | #b #tl #Hind #a * [#Ha >Ha //| @Hind]]
|@sym_eq @Htable
|>Ht1 %
|%{(bits_of_state ? (nhalt M) (cstate ?? c))} %{(low_char (current ? (ctape ?? c)))}
 % [% [% [// | cases (current ??) normalize [|#b] % #Hd destruct (Hd)]
      |>length_map whd in match (length ??); @eq_f //]
   |//]
|>Ht1 >cfg_low_tapes //] -H #H 
lapply(H (bits_of_state … (nhalt M) qout) (low_char … cout) 
         (low_mv … m) tup ? Hingraph)
  [>Htup whd in ⊢ (??%?); @eq_f >associative_append %] -H
#Ht2 @(eq_vec ? 3 ?? (niltape ?) ?) >Ht2 #i #Hi 
cases (le_to_or_lt_eq … (le_S_S_to_le … Hi)) -Hi #Hi
  [cases (le_to_or_lt_eq … (le_S_S_to_le … Hi)) -Hi #Hi
    [cases (le_to_or_lt_eq … (le_S_S_to_le … Hi)) -Hi #Hi
      [@False_ind /2/
      |>Hi >obj_low_tapes >nth_change_vec //
       >Ht1 >obj_low_tapes >Hstep @map_action 
      ]
    |>Hi >cfg_low_tapes >nth_change_vec_neq 
      [|% whd in ⊢ (??%?→?);  #H destruct (H)]
     >nth_change_vec // >Hnew_state @eq_f @eq_f >Hnew_tape 
     @eq_f2 [|2:%] >Ht1 >obj_low_tapes >map_move_mono >low_char_current %
    ]
  |(* program tapes do not change *)
   >Hi >prg_low_tapes 
   >nth_change_vec_neq [|% whd in ⊢ (??%?→?);  #H destruct (H)]
   >nth_change_vec_neq [|% whd in ⊢ (??%?→?);  #H destruct (H)]
   >Ht1 >prg_low_tapes //
  ]
qed. 

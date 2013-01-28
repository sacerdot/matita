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


(****************************** table of tuples *******************************)
include "turing/multi_universal/normalTM.ma".

(* a well formed table is a list of tuples *) 
 
definition table_TM ≝ λn,l,h.flatten ? (tuples_list n h l).

lemma table_TM_cons: ∀n,h,t,o. 
  table_TM n (t::o) h = (tuple_encoding n h t)@(table_TM n o h).
// qed.

lemma initial_bar: ∀n,h,l. l ≠ [ ] →
  table_TM n l h = bar :: tail ? (table_TM n l h).
#n #h * 
  [* #H @False_ind @H // 
  |#a #tl #_ >table_TM_cons lapply (is_tuple n h a) 
   * #qin * #cin * #qout * #cout * #mv * #_ #Htup >Htup %
  ]
qed. 

(************************** matching in a table *******************************)
lemma list_to_table: ∀n,l,h,t. mem ? t l →
  ∃ll,lr.table_TM n l h = ll@(tuple_encoding n h t)@lr.
#n #l #h #t elim l 
  [@False_ind
  |#hd #tl #Hind *
    [#Htup %{[]} %{(table_TM n tl h)} >Htup %
    |#H cases (Hind H) #ll * #lr #H1
     %{((tuple_encoding n h hd)@ll)} %{lr} 
     >associative_append <H1 %
    ]
  ]
qed.

lemma list_to_table1: ∀n,l,h,tup. mem ? tup (tuples_list n h l) →
  ∃ll,lr.table_TM n l h = ll@tup@lr.
#n #l #h #tup elim l 
  [@False_ind
  |#hd #tl #Hind *
    [#Htup %{[]} %{(table_TM n tl h)} >Htup %
    |#H cases (Hind H) #ll * #lr #H1
     %{((tuple_encoding n h hd)@ll)} %{lr} 
     >associative_append <H1 %
    ]
  ]
qed.

definition is_config : nat → list unialpha → Prop ≝  
 λn,t.∃qin,cin.
 only_bits qin ∧ cin ≠ bar ∧ |qin| = S n ∧ t = bar::qin@[cin].

lemma table_to_list: ∀n,l,h,c. is_config n c → 
  (∃ll,lr.table_TM n l h = ll@c@lr) → 
    ∃out,t. tuple_encoding n h t = (c@out) ∧ mem ? t l.
#n #l #h #c * #qin * #cin * * * #H1 #H2 #H3 #H4  
 * #ll * #lr lapply ll -ll elim l
  [>H4 #ll cases ll normalize [|#hd #tl ] #Habs destruct
  |#t1 #othert #Hind #ll >table_TM_cons #Htuple
   cut (S n < |ll@c@lr|)
     [<Htuple >length_append >(length_of_tuple  … (is_tuple … ))
      /2 by transitive_lt, le_n/] #Hsplit lapply Htuple -Htuple
   cases (is_tuple … n h t1) #q1 * #c1 * #q2 * #c2 * #m 
   * * * * * * * #Hq1 #Hq2 #Hc1 #Hc2 #Hm #Hlen1 #Hlen2 
   whd in ⊢ (???%→?); #Ht1 
   (* if ll is empty we match the first tuple t1, otherwise
      we match inside othert *)
   cases ll
    [>H4 >Ht1 normalize in ⊢ (???%→?); 
     >associative_append whd in ⊢ (??%?→?); #Heq destruct (Heq) -Heq
     >associative_append in e0; #e0
     lapply (append_l1_injective  … e0) [>H3 @Hlen1] #Heq1
     lapply (append_l2_injective  … e0) [>H3 @Hlen1]
     normalize in ⊢ (???%→?); whd in ⊢ (??%?→?); #Htemp 
     lapply (cons_injective_l ????? Htemp) #Hc1
     lapply (cons_injective_r ????? Htemp) -Htemp #Heq2
     %{(q2@[c2;m])} %{t1} % 
      [>Ht1 >Heq1 >Hc1 @eq_f >associative_append % 
      |%1 %
      ]
    |(* ll not nil *)
     #b #tl >Ht1 normalize in ⊢ (???%→?); 
     whd in ⊢ (??%?→?); #Heq destruct (Heq) 
     cases (compare_append … e0) #l *
      [* cases l 
        [#_ #Htab cases (Hind [ ] (sym_eq … Htab)) #out * #t * #Ht #Hmemt
         %{out} %{t} % // %2 //
        |(* this case is absurd *) 
         #al #tll #Heq1 >H4 #Heq2 @False_ind 
         lapply (cons_injective_l ? bar … Heq2) #Hbar <Hbar in Heq1; #Heq1
         @(absurd (mem ? bar (q1@(c1::q2@[c2; m]))))
          [>Heq1 @mem_append_l2 %1 //
          |% #Hmembar cases (mem_append ???? Hmembar) -Hmembar
            [#Hmembar lapply(Hq1 bar Hmembar) normalize #Habs destruct (Habs)
            |* [#Habs @absurd //]
             #Hmembar cases (mem_append ???? Hmembar) -Hmembar
              [#Hmembar lapply(Hq2 bar Hmembar) normalize #Habs destruct (Habs)
              |* [#Habs @absurd //] #Hmembar @(absurd ?? Hm) @sym_eq @mem_single //
              ]
            ]
          ]
        ]
      |* #Htl #Htab cases (Hind … Htab) #out * #t * #Ht #Hmemt
       %{out} %{t} % // %2 //
      ] 
    ]
  ]
qed.

lemma cfg_in_table_to_tuple: ∀n,l,h,c. is_config n c → 
  ∀ll,lr.table_TM n l h = ll@c@lr → 
    ∃out,m,lr0. lr = out@m::lr0 ∧ is_config n (bar::out) ∧ m ≠ bar.
#n #l #h #c * #qin * #cin * * * #H1 #H2 #H3 #H4  
#ll #lr lapply ll -ll elim l
  [>H4 #ll cases ll normalize [|#hd #tl ] #Habs destruct
  |#t1 #othert #Hind #ll >table_TM_cons #Htuple
   cut (S n < |ll@c@lr|)
     [<Htuple >length_append >(length_of_tuple  … (is_tuple … ))
      /2 by transitive_lt, le_n/] #Hsplit lapply Htuple -Htuple
   cases (is_tuple … n h t1) #q1 * #c1 * #q2 * #c2 * #m 
   * * * * * * * #Hq1 #Hq2 #Hc1 #Hc2 #Hm #Hlen1 #Hlen2 
   whd in ⊢ (???%→?); #Ht1 
   (* if ll is empty we match the first tuple t1, otherwise
      we match inside othert *)
   cases ll
    [>H4 >Ht1 normalize in ⊢ (???%→?); 
     >associative_append whd in ⊢ (??%?→?); #Heq destruct (Heq) -Heq
     >associative_append in e0; #e0
     lapply (append_l1_injective  … e0) [>H3 @Hlen1] #Heq1
     lapply (append_l2_injective  … e0) [>H3 @Hlen1]
     normalize in ⊢ (???%→?); whd in ⊢ (??%?→?); #Htemp 
     lapply (cons_injective_l ????? Htemp) #Hc1
     lapply (cons_injective_r ????? Htemp) -Htemp #Heq2
     %{(q2@[c2])} %{m} %{(table_TM n othert h)} % // %
     [ <Heq2 >associative_append >associative_append % | %{q2} %{c2} % // % // % // ] 
    |(* ll not nil *)
     #b #tl >Ht1 normalize in ⊢ (???%→?); 
     whd in ⊢ (??%?→?); #Heq destruct (Heq) 
     cases (compare_append … e0) #l *
      [* cases l 
        [#_ #Htab cases (Hind [ ] (sym_eq … Htab)) #out * #m0 * #lr0 * * #Hlr #Hcfg #Hm0
         %{out} %{m0} %{lr0} % // % //
        |(* this case is absurd *) 
         #al #tll #Heq1 >H4 #Heq2 @False_ind 
         lapply (cons_injective_l ? bar … Heq2) #Hbar <Hbar in Heq1; #Heq1
         @(absurd (mem ? bar (q1@(c1::q2@[c2; m]))))
          [>Heq1 @mem_append_l2 %1 //
          |% #Hmembar cases (mem_append ???? Hmembar) -Hmembar
            [#Hmembar lapply(Hq1 bar Hmembar) normalize #Habs destruct (Habs)
            |* [#Habs @absurd //]
             #Hmembar cases (mem_append ???? Hmembar) -Hmembar
              [#Hmembar lapply(Hq2 bar Hmembar) normalize #Habs destruct (Habs)
              |* [#Habs @absurd //] #Hmembar @(absurd ?? Hm) @sym_eq @mem_single //
              ]
            ]
          ]
        ]
      |* #Htl #Htab cases (Hind … Htab) #out * #m0 * #lr0 * * #Hlr #Hcfg #Hm0
        %{out} %{m0} %{lr0} % // % //
      ] 
    ]
  ]
qed.

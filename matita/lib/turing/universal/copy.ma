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


include "turing/universal/marks.ma".

definition copy_step_subcase ≝
  λalpha,c,elseM.ifTM ? (test_char ? (λx.x == 〈c,true〉))
    (seq (FinProd alpha FinBool) (adv_mark_r …)
      (seq ? (move_l …)
        (seq ? (adv_to_mark_l … (is_marked alpha))
          (seq ? (write ? 〈c,false〉)
            (seq ? (move_r …)
              (seq ? (mark …)
                (seq ? (move_r …) (adv_to_mark_r … (is_marked alpha)))))))))
    elseM tc_true.

definition R_copy_step_subcase ≝ 
  λalpha,c,RelseM,t1,t2.
    ∀a,l1,x0,a0,l2,x,l3.
    t1 = midtape (FinProd … alpha FinBool) (l1@〈a0,false〉::〈x0,true〉::l2) 
         〈x,true〉 (〈a,false〉::l3) → 
    (∀c.memb ? c l1 = true → is_marked ? c = false) →          
    (x = c ∧ t2 = midtape ? (〈x,false〉::l1@〈a0,true〉::〈x,false〉::l2) 〈a,true〉 l3) ∨
    (x ≠ c ∧ RelseM t1 t2).
    
lemma sem_copy_step_subcase : 
  ∀alpha,c,elseM,RelseM. Realize ? elseM RelseM → 
  Realize ? (copy_step_subcase alpha c elseM) (R_copy_step_subcase alpha c RelseM).
#alpha #c #elseM #RelseM #HelseM #intape
cases (sem_if ? (test_char ? (λx. x == 〈c,true〉)) ?????? tc_true (sem_test_char ? (λx.x == 〈c,true〉))
        (sem_seq ????? (sem_adv_mark_r alpha)
          (sem_seq ????? (sem_move_l …)
            (sem_seq ????? (sem_adv_to_mark_l … (is_marked alpha))
              (sem_seq ????? (sem_write ? 〈c,false〉)
                (sem_seq ????? (sem_move_r …)
                  (sem_seq ????? (sem_mark …)
                    (sem_seq ????? (sem_move_r …) (sem_adv_to_mark_r … (is_marked alpha)))))))))
        HelseM intape)
#k * #outc * #Hloop #HR %{k} %{outc} % [@Hloop] -Hloop
#a #l1 #x0 #a0 #l2 #x #l3 #Hintape #Hl1marks cases HR -HR
[ * #ta * whd in ⊢ (%→?); >Hintape * * #c0 * whd in ⊢ (??%?→?); #Hx #Hc #Hta
  * #tb * whd in ⊢ (%→?); * #Htb cases (Htb (l1@〈a0,false〉::〈x0,true〉::l2) x) -Htb
  #Htb lapply (Htb … Hta) -Htb #Htb #_ #_
  * #tc * whd in ⊢ (%→?); * #_ #Htc lapply (Htc … Htb) -Htb -Htc #Htc
  * #td * whd in ⊢ (%→?); * #_ #Htd cases (Htd … Htc) -Htd #_ #Htd cases (Htd (refl ??))
  -Htd #Htd lapply (Htd (l1@[〈a0,false〉]) 〈x0,true〉 l2 ???) //
  [#x1 #Hx1 cases (memb_append … Hx1) [ @Hl1marks | #Hsingle >(memb_single … Hsingle) % ]
  |whd in ⊢ (??%?); // ]
  -Htd #Htd #_
  * #te * whd in ⊢ (%→?); #Hte lapply (Hte … Htd) -Hte -Htd -Htc #Hte
  * #tf * whd in ⊢ (%→?); * #_ #Htf lapply (Htf … Hte) -Hte -Htf >reverse_append #Htf
  * #tg * whd in ⊢ (%→?); * #Htg #_ lapply (Htg … Htf) -Htf -Htg >reverse_single #Htg
  * #th * whd in ⊢ (%→?); * #_ #Hth lapply (Hth … Htg) -Htg -Hth
  generalize in match Hl1marks; -Hl1marks @(list_elim_left … l1)
  [ #Hl1marks #Hth whd in ⊢ (%→?); * #_ #Houtc cases (Houtc … Hth) -Houtc
    [ * normalize in ⊢ (%→?); #Hfalse destruct (Hfalse) ]
    * * #_ #Houtc #_ lapply (Houtc [] ?? (refl ??) (refl ??) Hl1marks) -Houtc
    #Houtc % >(\P Hc) in Hx; #Hx destruct (Hx) % // @Houtc
  | -l1 #c1 #l1 #_ #Hl1marks >reverse_append >reverse_single
    #Hth whd in ⊢ (%→?); * #_ #Houtc cases (Houtc … Hth) -Houtc
    [ * >Hl1marks [ #Hfalse destruct (Hfalse) ] @memb_append_l2 @memb_hd ]
    * * #_ #Houtc lapply (Houtc (reverse ? l1@[〈x,false〉]) 〈a,true〉 l3 ? (refl ??) ?) -Houtc
    [ #x1 #Hx1 cases (memb_append … Hx1) -Hx1 #Hx1   
      [@Hl1marks @memb_append_l1 <(reverse_reverse … l1) @memb_reverse @Hx1 
      |>(memb_single … Hx1) % ]
    | normalize >associative_append % ] 
    #Houtc #_ % destruct (Hx) lapply (\P Hc) -Hc #Hc destruct (Hc) % //
    >Houtc >reverse_append >reverse_reverse >associative_append >associative_append % ]
| * #ta * whd in ⊢ (%→?); >Hintape * #Hxc #Hta #Helse %2 %
  [| <Hta @Helse ]
  % #Hxc0 >Hxc0 in Hxc; #Hxc lapply (Hxc 〈c,true〉 (refl …)) #Hfalse
  cases (\Pf Hfalse) #Hfalse0 @Hfalse0 %
]
qed.
    
(*
if current = 0,tt
   then advance_mark_r;
        move_l;
        advance_to_mark_l;
        write(0,ff)
        move_r;
        mark;
        move_r;
        advance_to_mark_r;
else if current = 1,tt
   then advance_mark_r;
        move_l;
        advance_to_mark_l;
        write(1,ff)
        move_r;
        mark;
        move_r;
        advance_to_mark_r;
else if current = null 
   then advance_mark_r;
        move_l;
        advance_to_mark_l
        adv_mark_r;
        move_r;
        advance_to_mark_r
*)

definition nocopy_subcase ≝
  ifTM STape (test_char ? (λx:STape.x == 〈null,true〉))
    (seq ? (adv_mark_r …)
      (seq ? (move_l …)
        (seq ? (adv_to_mark_l … (is_marked ?))
          (seq ? (adv_mark_r …)
            (seq ? (move_r …) (adv_to_mark_r … (is_marked ?)))))))
    (nop ?) tc_true.

definition R_nocopy_subcase ≝ 
  λt1,t2.
    ∀a,l1,x0,a0,l2,x,l3.
    t1 = midtape STape (l1@〈a0,false〉::〈x0,true〉::l2) 
         〈x,true〉 (〈a,false〉::l3) → 
    (∀c.memb ? c l1 = true → is_marked ? c = false) →          
    (x = null ∧
     t2 = midtape ? (〈x,false〉::l1@〈a0,true〉::〈x0,false〉::l2) 〈a,true〉 l3) ∨
    (x ≠ null ∧ t2 = t1).
    
lemma sem_nocopy_subcase : Realize ? nocopy_subcase R_nocopy_subcase.
#intape
cases (sem_if ? (test_char ? (λx:STape.x == 〈null,true〉)) ?????? tc_true
        (sem_test_char ? (λx:STape.x == 〈null,true〉))
          (sem_seq … (sem_adv_mark_r …)
            (sem_seq … (sem_move_l …)
              (sem_seq … (sem_adv_to_mark_l … (is_marked ?))
                (sem_seq … (sem_adv_mark_r …)
                  (sem_seq … (sem_move_r …) 
                    (sem_adv_to_mark_r … (is_marked ?))))))) (sem_nop ?) intape)
#k * #outc * #Hloop #HR @(ex_intro ?? k) @(ex_intro ?? outc)  % [@Hloop] -Hloop
#a #l1 #x0 #a0 #l2 #x #l3 #Hintape #Hl1marks cases HR -HR
[ * #ta * whd in ⊢ (%→?); >Hintape * * #c * whd in ⊢ (??%?→?); #Hc destruct (Hc) #Hx #Hta
  * #tb * whd in ⊢ (%→?); * #Htb #_ cases (Htb (l1@〈a0,false〉::〈x0,true〉::l2) x) -Htb #Htb #_ lapply (Htb … Hta) -Hta -Htb #Htb
  * #tc * whd in ⊢ (%→?); * #_ #Htc lapply (Htc … Htb) -Htb -Htc #Htc
  * #td * whd in ⊢ (%→?); * #_ #Htd cases (Htd … Htc) -Htd #_ #Htd cases (Htd (refl …)) -Htd #Htd #_
  lapply (Htd (l1@[〈a0,false〉]) 〈x0,true〉 l2 ? (refl …) ?)
  [#x1 #Hx1 cases (memb_append … Hx1) [@Hl1marks| -Hx1 #Hx1 >(memb_single … Hx1) % ]
  |>associative_append % ] -Htd >reverse_append in ⊢ (???%→?); >associative_append in ⊢ (???%→?); #Htd
  * #te * whd in ⊢ (%→?); * #Hte cases (Hte l2 x0) -Hte #Hte #_ #_ lapply (Hte … Htd) -Hte -Htd -Htc #Hte
  * #tf * whd in ⊢ (%→?); * #_ #Htf lapply (Htf … Hte) -Hte -Htf
  generalize in match Hl1marks; -Hl1marks @(list_elim_left … l1)
  [ #Hl1marks #Hth whd in ⊢ (%→?); * #_ #Houtc cases (Houtc … Hth) -Houtc
    [ * normalize in ⊢ (%→?); #Hfalse destruct (Hfalse) ]
    * * #_ #Houtc lapply (Houtc [] ?? (refl ??) (refl ??) Hl1marks) -Houtc
    #Houtc lapply (\P Hx) -Hx #Hx destruct (Hx) #_ % % [%] @Houtc
  | -l1 #c1 #l1 #_ #Hl1marks >reverse_append >reverse_single
    #Hth whd in ⊢ (%→?); * #_ #Houtc cases (Houtc … Hth) -Houtc
    [ * >Hl1marks [ #Hfalse destruct (Hfalse) ] @memb_append_l2 @memb_hd ]
    * * #Hc1 #Houtc #_ lapply (Houtc (reverse ? l1@[〈x,false〉]) 〈a,true〉 l3 ? (refl ??) ?) -Houtc
    [ #x1 #Hx1 cases (memb_append … Hx1) -Hx1 #Hx1
      [@Hl1marks @memb_append_l1 <(reverse_reverse … l1) @memb_reverse @Hx1 
      |>(memb_single … Hx1) % ]
    | normalize >associative_append % ] 
    #Houtc lapply (\P Hx) -Hx #Hx destruct (Hx) % % [%] >Houtc
    >reverse_append >reverse_reverse >associative_append >associative_append % ]
| * #ta * whd in ⊢ (%→?); >Hintape * #Hxc
  cut (x ≠ null) [ % #Hx cases (\Pf (Hxc ? (refl …))) #Hfalse @Hfalse >Hx % ] -Hxc #Hxnull
  #Hta whd in ⊢ (%→?); #Houtc %2 % // <Hta @Houtc ]
qed.

definition copy_step ≝
  ifTM ? (test_char STape (λc.bit_or_null (\fst c)))
  (single_finalTM ? (copy_step_subcase FSUnialpha (bit false)
    (copy_step_subcase FSUnialpha (bit true) nocopy_subcase)))
  (nop ?)
  tc_true.
  
definition R_copy_step_true ≝ 
  λt1,t2.
    ∀ls,c,rs. t1 = midtape STape ls 〈c,true〉 rs → 
    bit_or_null c = true ∧
    (∀a,l1,x0,a0,l2,l3.
     ls = (l1@〈a0,false〉::〈x0,true〉::l2) → 
     rs = (〈a,false〉::l3) → 
     no_marks l1 →          
     ((∃x. c = bit x ∧
      t2 = midtape STape (〈bit x,false〉::l1@〈a0,true〉::〈bit x,false〉::l2) 〈a,true〉 l3) ∨
      (c = null ∧
      t2 = midtape ? (〈null,false〉::l1@〈a0,true〉::〈x0,false〉::l2) 〈a,true〉 l3))).
     
definition R_copy_step_false ≝ 
  λt1,t2.
   ∀ls,c,rs.t1 = midtape (FinProd … FSUnialpha FinBool) ls c rs → 
   bit_or_null (\fst c) = false ∧ t2 = t1.
   
lemma sem_copy_step : 
  accRealize ? copy_step (inr … (inl … (inr … start_nop))) R_copy_step_true R_copy_step_false.
#intape
@(acc_sem_if_app … (sem_test_char ? (λc:STape.bit_or_null (\fst c)))  …
    (sem_copy_step_subcase FSUnialpha (bit false) …
       (sem_copy_step_subcase FSUnialpha (bit true) … (sem_nocopy_subcase …)))
          (sem_nop …))
[ #t1 #t2 #t3 whd in ⊢ (%→%→?); #H1 #H2 #ls #c #rs #Ht1 >Ht1 in H1;
  * * #c0 * whd in ⊢ (??%?→?); #Hc0 destruct (Hc0) #Hc #Ht3 % //
  #a #l1 #x0 #a0 #l2 #l3 #Hls #Hrs #Hl1marks >Hls in Ht3; >Hrs #Ht3
  cases (H2 … Ht3 ?)
  [ * #Hc' #Ht2 % %{false} % // <Hc' @Ht2
  | * #Hnotfalse whd in ⊢ (%→?); #Ht2 cases (Ht2 … Ht3 ?) -Ht2
    [ * #Hc' #Ht2 % %{true} % // <Hc' @Ht2
    |  * #Hnottrue whd in ⊢ (%→?); #Ht2 cases (Ht2 … Ht3 ?) -Ht2
      [ * #Hc' #Ht2 %2 <Hc' % // @Ht2
      | * #Hnotnull @False_ind
        generalize in match Hnotnull;generalize in match Hnottrue;generalize in match Hnotfalse;
        cases c in Hc; normalize
        [ * [ #_ #_ * #Hfalse #_ | #_ * #Hfalse #_ #_ ]
        | #_ #_ #_ * #Hfalse
        |*: #Hfalse destruct (Hfalse) ] @Hfalse %
      | @Hl1marks ]
    | @Hl1marks ]
  | @Hl1marks ]
| #t1 #t2 #t3 whd in ⊢ (%→%→?); #H1 #H2 #ls #c #rs #Ht1
  >Ht1 in H1; * #Hcur #Ht3 % // @Hcur % ]
qed.

(*
1) il primo carattere è marcato
2) l'ultimo carattere è l'unico che può essere null, gli altri sono bit
3) il terminatore non è né bit, né null
*)
   
definition copy0 ≝ whileTM ? copy_step (inr … (inl … (inr … start_nop))).

let rec merge_config (l1,l2:list STape) ≝ 
  match l1 with
  [ nil ⇒ nil ?
  | cons p1 l1' ⇒ match l2 with
    [ nil ⇒ nil ? 
    | cons p2 l2' ⇒ 
           let 〈c1,b1〉 ≝ p1 in let 〈c2,b2〉 ≝ p2 in
           match c2 with
           [ null ⇒ p1
           | _ ⇒ p2 ] :: merge_config l1' l2' ] ].
           
lemma merge_config_append :
 ∀l1,l2,l3,l4.|l1| = |l2| → 
 merge_config (l1@l3) (l2@l4) = merge_config l1 l2@merge_config l3 l4.
#l1 #l2 #l3 #l4 #Hlen @(list_ind2 … Hlen)
[normalize //
| #t1 #t2 * #c1 #b1 * #c2 #b2 #IH whd in ⊢ (??%%); >IH % ]
qed.

definition R_copy0 ≝ λt1,t2.
  ∀ls,c,c0,rs,l1,l3,l4.
  t1 = midtape STape (l3@l4@〈c0,true〉::ls) 〈c,true〉 (l1@rs) → 
  no_marks l1 → no_marks (l3@l4) → |l1| = |l4| → 
  ∀l1',bv.〈c,false〉::l1 = l1'@[〈comma,bv〉] → only_bits_or_nulls l1' → 
  ∀l4',bg.l4@[〈c0,false〉] = 〈grid,bg〉::l4' → only_bits_or_nulls l4' → 
  (c = comma ∧ t2 = t1) ∨
  (c ≠ comma ∧ 
    t2 = midtape ? (reverse ? l1'@l3@〈grid,true〉::
                  merge_config l4' (reverse ? l1')@ls) 
     〈comma,true〉 rs).
     
lemma inj_append_singleton_l1 :
  ∀A.∀l1,l2:list A.∀a1,a2.l1@[a1] = l2@[a2] → l1 = l2.
#A #l1 #l2 #a1 #a2 #H lapply (eq_f … (reverse ?) … H)
>reverse_append >reverse_append normalize #H1 destruct
lapply (eq_f … (reverse ?) … e0) >reverse_reverse >reverse_reverse //
qed.

lemma inj_append_singleton_l2 :
  ∀A.∀l1,l2:list A.∀a1,a2.l1@[a1] = l2@[a2] → a1 = a2.
#A #l1 #l2 #a1 #a2 #H lapply (eq_f … (reverse ?) … H)
>reverse_append >reverse_append normalize #H1 destruct %
qed.

axiom daemon : ∀P:Prop.P.

lemma list_cases2_full : 
  ∀T1,T2:Type[0].∀l1:list T1.∀l2:list T2.∀P:Prop.
  length ? l1 = length ? l2 →
  (l1 = [] → l2 = [] → P) → 
  (∀hd1,hd2,tl1,tl2.l1 = hd1::tl1 → l2 = hd2::tl2 → P) → P.
#T1 #T2 #l1 #l2 #P #Hl @(list_ind2 … Hl)
[ #Pnil #Pcons @Pnil //
| #tl1 #tl2 #hd1 #hd2 #IH1 #IH2 #Hp @Hp // ]
qed.

lemma wsem_copy0 : WRealize ? copy0 R_copy0.
#intape #k #outc #Hloop 
lapply (sem_while … sem_copy_step intape k outc Hloop) [%] -Hloop
* #ta * #Hstar @(star_ind_l ??????? Hstar)
[ #tb whd in ⊢ (%→?); #Hleft
  #ls #c #c0 #rs #l1 #l3 #l4 #Htb #Hl1nomarks #Hl3l4nomarks #Hlen #l1' #bv
  #Hl1 #Hl1bits #l4' #bg #Hl4 #Hl4bits
  cases (Hleft … Htb) -Hleft #Hc #Houtc % %
  [ generalize in match Hl1bits; -Hl1bits cases l1' in Hl1;
    [ normalize #Hl1 #c1 destruct (Hl1) %
    | * #c' #b' #l0 #Heq normalize in Heq; destruct (Heq)
      #Hl1bits lapply (Hl1bits 〈c',false〉 ?) [ @memb_hd ] 
      >Hc #Hfalse destruct ]
  | @Houtc ]
| #tb #tc #td whd in ⊢ (%→?→(?→%)→%→?); #Htc #Hstar1 #Hind #Htd
  lapply (Hind Htd) -Hind #Hind
  #ls #c #c0 #rs #l1 #l3 #l4 #Htb #Hl1nomarks #Hl3l4nomarks #Hlen #l1' #bv
  #Hl1 #Hl1bits #l4' #bg #Hl4 #Hl4bits %2
  cases (Htc … Htb) -Htc #Hcbitnull #Htc
  % [ % #Hc' >Hc' in Hcbitnull; normalize #Hfalse destruct (Hfalse) ]
  cut (|l1| = |reverse ? l4|) [>length_reverse @Hlen] #Hlen1
  @(list_cases2_full … Hlen1)
  [ (* case l1 = [] is discriminated because l1 contains at least comma *)
    #Hl1nil @False_ind >Hl1nil in Hl1; cases l1' normalize
    [ #Hl1 destruct normalize in Hcbitnull; destruct (Hcbitnull)
    | #p0 #l0 normalize #Hfalse destruct (Hfalse) cases l0 in e0;
      [ normalize #Hfalse1 destruct (Hfalse1)
      | #p0' #l0' normalize #Hfalse1 destruct (Hfalse1) ] ]
  | (* case c::l1 = c::a::l1'' *)
    * #a #ba * #a0 #ba0 #l1'' #l4'' #Hl1cons #Hl4cons
    lapply (eq_f ?? (reverse ?) ?? Hl4cons) >reverse_reverse >reverse_cons -Hl4cons #Hl4cons
    cut (ba = false) 
    [ >Hl1cons in Hl1nomarks; #Hl1nomarks lapply (Hl1nomarks 〈a,ba〉 ?)
      [ @memb_hd | normalize // ] ] #Hba
    cut (ba0 = false) 
    [ >Hl4cons in Hl3l4nomarks; #Hl3l4nomarks lapply (Hl3l4nomarks 〈a0,ba0〉 ?)
      [ @memb_append_l2 @memb_append_l2 @memb_hd | normalize // ] ] #Hba0
    >Hba0 in Hl4cons; >Hba in Hl1cons; -Hba0 -Hba #Hl1cons #Hl4cons
    >Hl4cons in Htc; >Hl1cons #Htc
    lapply (Htc a (l3@reverse ? l4'') c0 a0 ls (l1''@rs) ? (refl ??) ?)
    [ #x #Hx @Hl3l4nomarks >Hl4cons <associative_append
      @memb_append_l1 @Hx
    | >associative_append >associative_append %
    | -Htc
      cut (∃la.l1' = 〈c,false〉::la)
      [ >Hl1cons in Hl1; cases l1'
        [normalize #Hfalse destruct (Hfalse)
        | #p #la normalize #Hla destruct (Hla) @(ex_intro ?? la) % ] ]
      * #la #Hla
      cut (∃lb.l4' = lb@[〈c0,false〉])
      [ >Hl4cons in Hl4;
        @(list_elim_left … l4')
        [ #Heq lapply (eq_f … (length ?) … Heq)
          >length_append >length_append 
          >commutative_plus normalize >commutative_plus normalize
          #Hfalse destruct
        | #a1 #tl #_ #Heq 
          >(inj_append_singleton_l2 ? (reverse ? l4''@[〈a0,false〉]) (〈grid,bg〉::tl) 〈c0,false〉 a1 Heq)
          @ex_intro //
      ] ] * #lb #Hlb
      cut (|lb| = |reverse ? la|) 
      [ >Hla in Hl1; >Hlb in Hl4; #Hl4 #Hl1
        >(?:l1 = la@[〈comma,bv〉]) in Hlen;
        [|normalize in Hl1; destruct (Hl1) %]
        >(?:l4 = 〈grid,bg〉::lb)
        [|@(inj_append_singleton_l1 ?? (〈grid,bg〉::lb) ?? Hl4) ]
        >length_append >commutative_plus >length_reverse
        normalize #Hlalb destruct (Hlalb) //
      ] #Hlen2
      *
      (* by hyp on the first iteration step, 
         we consider whether c = bit x or c = null *)
      (* c = bit x *)
      [ * #x * #Hx #Htc 
        lapply (Hind (〈bit x,false〉::ls) a a0 rs l1'' 
                (〈bit x,false〉::l3) (reverse ? l4'') ????) 
        [ >Hl1cons in Hlen; >Hl4cons >length_append >commutative_plus 
          normalize #Hlen destruct (Hlen) //
        | #x0 #Hx0 cases (orb_true_l … Hx0)
          [ #Hx0eq >(\P Hx0eq) %
          | -Hx0 #Hx0 @Hl3l4nomarks >Hl4cons
            <associative_append @memb_append_l1 // ]
        | #x0 #Hx0 @Hl1nomarks >Hl1cons @memb_cons //
        | >Htc >associative_append % 
        | -Hind 
          <Hl1cons <Hl4cons #Hind lapply (Hind la bv ?? lb bg ??)
          [ #x0 #Hx0 @Hl4bits >Hlb @memb_append_l1 //
          | >Hlb in Hl4; normalize in ⊢ (%→?); #Hl4
            @(inj_append_singleton_l1 ? l4 (〈grid,bg〉::lb) … Hl4)
          | #x0 #Hx0 @Hl1bits >Hla @memb_cons //
          | >Hla in Hl1; normalize in ⊢ (%→?); #Hl1
            destruct (Hl1) // ] -Hind
          (* by IH, we proceed by cases, whether a = comma 
             (consequently several lists = []) or not *)          
          *
          [ * #Ha #Houtc1
           cut (la = [] ∧ lb = [] ∧ l1'' = [] ∧ l4'' = [])
           [ @daemon ] * * * #Hla1 #Hlb1 #Hl1nil #Hl4nil
           >Hl1cons in Hl1; >Hla
           >Houtc1 >Htc #Hl1
           >Hl4cons in Hl4; >Hlb #Hl4
           >Hla1 >Hlb1 >Hl1nil >Hl4nil >Hx
           cut (a0 = grid) [ @daemon ] #Ha0 <Ha <Ha0
           normalize in ⊢ (??(??%?%)(??%?%)); >associative_append %
          | * #Ha #Houtc1 >Houtc1 @eq_f3 //
            >Hla >reverse_cons >associative_append @eq_f
            >Hx whd in ⊢ (??%?); @eq_f whd in ⊢ (???%); @eq_f @eq_f
            >Hlb >append_cons @eq_f2 // >(merge_config_append … Hlen2) %            
          ]
       ]
    | (* c = null *)
      * #Hc #Htc 
      lapply (Hind (〈c0,false〉::ls) a a0 rs l1'' (〈null,false〉::l3) (reverse ? l4'') ????)
      [  >Hl1cons in Hlen; >Hl4cons >length_append >commutative_plus normalize
         #Hlen destruct (Hlen) @e0
      | #x0 #Hx0 cases (memb_append STape ? [〈null,false〉] (l3@reverse ? l4'') … Hx0) -Hx0 #Hx0
        [ >(memb_single … Hx0) %
        | @Hl3l4nomarks cases (memb_append … Hx0) -Hx0 #Hx0
          [ @memb_append_l1 //
          | @memb_append_l2 >Hl4cons @memb_append_l1 // ]
        ]
      | >Hl1cons #x' #Hx0 @Hl1nomarks >Hl1cons @memb_cons //
      | >Htc @eq_f3 // >associative_append % ] -Hind <Hl1cons <Hl4cons #Hind
        lapply (Hind la bv ?? lb bg ??)
          [ #x0 #Hx0 @Hl4bits >Hlb @memb_append_l1 //
          | >Hlb in Hl4; normalize in ⊢ (%→?); #Hl4
            @(inj_append_singleton_l1 ? l4 (〈grid,bg〉::lb) … Hl4)
          | #x0 #Hx0 @Hl1bits >Hla @memb_cons //
          | >Hla in Hl1; normalize in ⊢ (%→?); #Hl1
            destruct (Hl1) // ] -Hind *
          (* by IH, we proceed by cases, whether a = comma 
             (consequently several lists = []) or not *)          
          [ * #Ha #Houtc1 >Hl1cons in Hl1; >Hla
           >Houtc1 >Htc #Hl1
           >Hl4cons in Hl4; >Hlb #Hl4
           cut (la = [] ∧ lb = [] ∧ l1'' = [] ∧ l4'' = []) 
           [@daemon] * * * #Hla1 #Hlb1 #Hl1nil #Hl4nil
           >Hla1 >Hlb1 >Hl1nil >Hl4nil >Hc
           cut (a0 = grid) [ @daemon ] #Ha0 <Ha <Ha0
           normalize in ⊢ (??(??%?%)(??%?%)); >associative_append %
          | * #Ha #Houtc1 >Houtc1 @eq_f3 //
            >Hla >reverse_cons >associative_append @eq_f
            >Hc whd in ⊢ (??%?); @eq_f whd in ⊢ (???%); @eq_f @eq_f
            >Hlb >append_cons @eq_f2 // >(merge_config_append … Hlen2) %
          ]
       ]
]]]
qed.

definition Pre_copy0 ≝ λt1.
  ∃ls,c,c0,rs,l1,l3,l4.
  t1 = midtape STape (l3@l4@〈c0,true〉::ls) 〈c,true〉 (l1@rs) ∧
  no_marks l1 ∧ no_marks (l3@l4) ∧ |l1| = |l4| ∧
  (∃l1',bv.〈c,false〉::l1 = l1'@[〈comma,bv〉] ∧ only_bits_or_nulls l1') ∧
  (∃l4',bg.l4@[〈c0,false〉] = 〈grid,bg〉::l4' ∧ only_bits_or_nulls l4').

definition Pre_copy ≝ λt1.
  ∃ls,s0,s1,c0,c1,rs,l1,l3,l4.
  t1 = midtape STape (l3@〈grid,false〉::〈c0,false〉::l4@〈s0,true〉::ls) 〈s1,true〉 (l1@〈c1,false〉::〈comma,false〉::rs) ∧
  no_marks l1 ∧ no_marks l3 ∧ no_marks l4 ∧ |l1| = |l4| ∧ 
  only_bits (l4@[〈s0,false〉]) ∧ only_bits (〈s1,false〉::l1) ∧ 
  bit_or_null c0 = true ∧ bit_or_null c1 = true.
  
lemma list_last: ∀A.∀l:list A.
  l = [ ] ∨ ∃a,l1. l = l1@[a].
#A #l <(reverse_reverse ? l) cases (reverse A l)
  [%1 //
  |#a #l1 %2 @(ex_intro ?? a) @(ex_intro ?? (reverse ? l1)) //
  ]
qed.

lemma terminate_copy0 : ∀t.Pre_copy0 t → Terminate ? copy0 t.
#t #HPre
@(terminate_while_guarded ??? 
   Pre_copy0 … 
   (acc_Realize_to_acc_GRealize ??? Pre_copy0 … sem_copy_step)
   … HPre) [%]
  [ -HPre -t #t1 #t2 * #ls * #c * #c0 * #rs * #l1 * #l3 * #l4
    * * * * * #Ht1 #Hl1nomarks #Hl3l4nomarks #Hlen
    * #l1' * #bv * #Hl1 #Hbitsnullsl1' * #l4' * #bg * #Hl4 #Hbitsnullsl4'
    #HR cases (HR … Ht1) -HR #Hbitnullc
    cut (∃d1,l1''.l1 = 〈d1,false〉::l1'')
    [ lapply Hl1nomarks cases l1 in Hl1;
      [ whd in ⊢ (???%→?); #Hl1
        lapply (append_l2_injective_r ? [] l1' [〈c,false〉] [〈comma,bv〉] (refl ??) Hl1)
        #Hc destruct (Hc) normalize in Hbitnullc; destruct (Hbitnullc) 
      | * #d #bd #l1'' #_ #Hl1nomarks >(?:bd = false) [| @(Hl1nomarks 〈d,bd〉) @memb_hd ] /3/ ] ]
    * #d1 * #l1'' #Hl1''
    cut (∃d2,l4''.l4 = l4''@[〈d2,false〉])
    [ lapply Hl4 cases (list_last ? l4)
      [ #Hl4' >Hl4' in Hlen; >Hl1'' normalize in ⊢ (%→?); #HFalse destruct (HFalse)
      | * * #d2 #bd2 * #l4'' #Hl4'' >Hl4'' in Hl3l4nomarks; #Hl3l4nomarks #_ 
        <(?:bd2 = false) [| @(Hl3l4nomarks 〈d2,bd2〉) @memb_append_l2 @memb_append_l2 @memb_hd ]
        /3/ ] ]
    * #d2 * #l4'' #Hl4'' >Hl1'' >Hl4'' 
    #HR cases (HR d1 (l3@l4'') c0 d2 ls (l1''@rs) ? ? ?)
    [3: >associative_append >associative_append %
    |4: %
    |5: #x #Hx @Hl3l4nomarks cases (memb_append … Hx)
      [ @memb_append_l1
      | >Hl4'' -Hx #Hx @memb_append_l2 @memb_append_l1 @Hx ]
    | * #x1 * #Hc #Ht2 whd >Ht2
      %{(〈bit x1,false〉::ls)} %{d1} %{d2} %{rs} %{l1''} %{(〈bit x1,false〉::l3)} %{l4''}
      % [ % [ % [ % [ % 
      [ >associative_append %
      | #x #Hx @Hl1nomarks >Hl1'' @memb_cons @Hx ]
      | #x #Hx cases (orb_true_l … Hx) -Hx #Hx
        [ >(\P Hx) %
        | @Hl3l4nomarks cases (memb_append … Hx)
          [ @memb_append_l1
          | -Hx #Hx >Hl4'' @memb_append_l2 @memb_append_l1 @Hx ] ] ]
      | >Hl1'' in Hlen; >Hl4'' >length_append >commutative_plus
        normalize in ⊢ (%→?); #Hlen destruct (Hlen) @e0 ]
      | <Hl1'' cases (list_last ? l1) in Hl1'';
        [ #Hl1'' >Hl1''#HFalse destruct(HFalse)
        | * #a * #l1''' #Hl1''' >Hl1''' in Hl1; #Hl1 #_
          lapply (append_l2_injective_r ? (〈c,false〉::l1''') l1' [a] [〈comma,bv〉] (refl …) Hl1)
          #Ha destruct (Ha) %{l1'''} %{bv} % //
          #x #Hx @Hbitsnullsl1'
          lapply (append_l1_injective_r ? (〈c,false〉::l1''') l1' [〈comma,bv〉] [〈comma,bv〉] (refl …) Hl1)
          #H <H @memb_cons @Hx ] ]
      | <Hl4'' cases (list_last ? l4') in Hl4;
        [ #Hl4' >Hl4' >Hl4'' cases l4''
          [ normalize in ⊢ (%→?); #Hfalse destruct (Hfalse)
          | #y #yl normalize in ⊢ (%→?); #H1 destruct (H1) cases yl in e0;
            [ normalize in ⊢ (%→?); #Hfalse destruct (Hfalse)
            | #z #zl normalize in ⊢ (%→?); #Hfalse destruct (Hfalse) ] ]
        | * #a * #l4''' #Hl4''' >Hl4''' #Hl4
          lapply (append_l1_injective_r ? l4 (〈grid,bg〉::l4''') [〈c0,false〉] [a] (refl …) Hl4)
          -Hl4 #Hl4 >Hl4 %{l4'''} %{bg} % //
          #x #Hx @Hbitsnullsl4' >Hl4''' @memb_append_l1 @Hx ] ]
   | * #Hc #Ht2 whd >Ht2
      %{(〈c0,false〉::ls)} %{d1} %{d2} %{rs} %{l1''} %{(〈null,false〉::l3)} %{l4''}
      % [ % [ % [ % [ % 
      [ >associative_append %
      | #x #Hx @Hl1nomarks >Hl1'' @memb_cons @Hx ]
      | #x #Hx cases (orb_true_l … Hx) -Hx #Hx
        [ >(\P Hx) %
        | @Hl3l4nomarks cases (memb_append … Hx)
          [ @memb_append_l1
          | -Hx #Hx >Hl4'' @memb_append_l2 @memb_append_l1 @Hx ] ] ]
      | >Hl1'' in Hlen; >Hl4'' >length_append >commutative_plus
        normalize in ⊢ (%→?); #Hlen destruct (Hlen) @e0 ]
      | <Hl1'' cases (list_last ? l1) in Hl1'';
        [ #Hl1'' >Hl1''#HFalse destruct(HFalse)
        | * #a * #l1''' #Hl1''' >Hl1''' in Hl1; #Hl1 #_
          lapply (append_l2_injective_r ? (〈c,false〉::l1''') l1' [a] [〈comma,bv〉] (refl …) Hl1)
          #Ha destruct (Ha) %{l1'''} %{bv} % //
          #x #Hx @Hbitsnullsl1'
          lapply (append_l1_injective_r ? (〈c,false〉::l1''') l1' [〈comma,bv〉] [〈comma,bv〉] (refl …) Hl1)
          #H <H @memb_cons @Hx ] ]
      | <Hl4'' cases (list_last ? l4') in Hl4;
        [ #Hl4' >Hl4' >Hl4'' cases l4''
          [ normalize in ⊢ (%→?); #Hfalse destruct (Hfalse)
          | #y #yl normalize in ⊢ (%→?); #H1 destruct (H1) cases yl in e0;
            [ normalize in ⊢ (%→?); #Hfalse destruct (Hfalse)
            | #z #zl normalize in ⊢ (%→?); #Hfalse destruct (Hfalse) ] ]
        | * #a * #l4''' #Hl4''' >Hl4''' #Hl4
          lapply (append_l1_injective_r ? l4 (〈grid,bg〉::l4''') [〈c0,false〉] [a] (refl …) Hl4)
          -Hl4 #Hl4 >Hl4 %{l4'''} %{bg} % //
          #x #Hx @Hbitsnullsl4' >Hl4''' @memb_append_l1 @Hx ] ]
    ]
 |@daemon (* WIP *)
 ]
qed.
    
   
(*
  [ -HPre -t #t1 #t2 * #ls * #s0 * #s1 * #c0 * #c1 * #rs * #l1 * #l3 * #l4
    * * * * * * * * #Ht1 #Hl1nomarks #Hl3nomarks #Hl4nomarks #Hlen #Hbits1 #Hbits2
    #Hbitcnullc0 #Hbitnullc1 #HPre cases (HPre … Ht1) -HPre
    #Hbitnulls1 #HPre 
    check terminate_while_guarded
    whd 
    cut (∃a0,l4'.〈c0,false〉::l4 = l4'@[〈a0,false〉])
    [ cases (list_last ? (〈c0,false〉::l4))
      [ #Hfalse destruct (Hfalse) 
      | * * #a0 #ba0 * #l4' #Hl4' >Hl4' >(?:ba0 = false) [/3/]
        cases l4' in Hl4';
        [ whd in ⊢ (???%→?); #Hl4' destruct (Hl4') %
        | #a1 #l4'' whd in ⊢ (???%→?); #Hl4''
          destruct (Hl4'') @(Hl4nomarks 〈a0,ba0〉) @memb_append_l2 @memb_hd ] ] ]
    * #a0 * #l4' #Hl4 
    cut (∃a,l1'.〈a,false〉::l1' = l1@[〈c1,false〉])
    [ cases l1 in Hl1nomarks;
      [ #_ %{c1} %{([])} %
      | * #a #ba #l1' #Hl1nomarks;
        %{a} %{(l1'@[〈c1,false〉])} @eq_f2 // @eq_f2 //
        @sym_eq @(Hl1nomarks 〈a,ba〉) @memb_hd ] ]
    * #a * #l1' #Hl1
    cases (HPre a (l3@〈grid,false〉::l4') s0 a0 ls (l1'@〈comma,false〉::rs) ???)
    [3: >associative_append @eq_f @eq_f
        change with ((〈c0,false〉::l4)@?) in ⊢ (??%?); >Hl4
        >associative_append %
    |4: change with ((〈a,false〉::l1')@?) in ⊢ (???%); >Hl1
        >associative_append %
    |5: #x #Hx cases (memb_append … Hx) -Hx
        [ @Hl3nomarks
        | #Hx cases (orb_true_l … Hx) -Hx
          [ #Hx >(\P Hx) %
          | cases l4' in Hl4;  
            [ #_ normalize in ⊢ (%→?); #Hfalse destruct (Hfalse)
            | #c0' #l4'' whd in ⊢ (???%→?); #Hl4 destruct (Hl4) #Hx
              cases (orb_true_l … Hx) -Hx #Hx
              [ >(\P Hx) %
              | @(Hl4nomarks x) @memb_append_l1 // ] ] ] ]
    | * #x * #Hs1 #Ht2
      %{(〈bit x,false〉::ls)} %{a0} %{a} %{c0} %{c1} %{rs} 
      %{...} %{(〈bit x,false〉::l3)} %{...}
              
              @(Hl4nomarks x) ]
    
          lapply (append_l2_injective_r ? [] l4' [〈c0,false〉] [〈a0,ba0〉] (refl …) Hl4')
          #Hc0 destruct (Hc0) %
        |
        @Hl4nomarks
        [ #Hl4'
          lapply (append_l2_injective_r ? [] l4' [〈c0,false〉] [〈a0,ba0〉] (refl …) Hl4')
          lapply (append_l1_injective_r ? [] l4' [〈c0,false〉] [〈a0,ba0〉] (refl …) Hl4')
          -Hl4' #Hl4' #Hc0 destruct (Hl4' Hc0) /3/
        | * 
  #HPre whd in ⊢ (%→?); #HR #ls * * #curl #curr * #rs * #Ht1 * 
    [(* absurd case *)
     #Hgrid * #ls1 * #cur1 * #rs1 * * >Ht1 #Hdes destruct (Hdes) 
     #Habs @False_ind @(absurd ?? Habs) @(is_grid_true … Hgrid)
    |* #ls0 * #c * #l1 * #l2 * #c1 * #l3 * #l4 * #rs0 * #n
     * * * * * * * * * *
     #Hl1 #Hmarksl1 #Hc #Hc1 #Hl3 #lenl1 #eqlen #Htable #Hls #Hcur #Hrs
     * #ls1 * #cur1 * #rs1 * * >Ht1 #Hdes destruct (Hdes) #Hdes #H
     lapply (H … Hl1 Hmarksl1 Hc Hc1 Hl3 lenl1 eqlen Htable Hls Hcur Hrs)
     -H *
      [* [ * #Hdes #Ht2 >Ht2 
          @ex_intro [2:@ex_intro [2: @ex_intro [2: % [%]|]|]|]
          %1 %
         |* #test * #c2 * #l5 * #l6 * #Hl4 #Ht2 
          cut (∃l7,l8. l6 = l7@〈comma,false 〉::l8 ∧ |l7| = |l1|) [@daemon]
          * #l7 * #l8 * #Hl6 #eqlen1 
          @ex_intro [2:@ex_intro [2: @ex_intro [2: % [@Ht2]|]|]|] %2
          @(ex_intro … ls0) @(ex_intro … c) @(ex_intro … l1)
          @(ex_intro … (l2@〈c1,false〉::l3@〈comma,false〉::l5@[〈bar,false〉])) 
          @(ex_intro … c2) @(ex_intro … l7) @(ex_intro … l8) 
          @(ex_intro … rs0) @(ex_intro … n) 
          % [2: >Hl6 >associative_append >associative_append @eq_f @eq_f @eq_f
           @eq_f >associative_append @eq_f @eq_f >associative_append % ]
          % [2: %] % [2: %] % [2:@daemon] % [2: @sym_eq @eqlen1]
          % [2: @lenl1] % [2: #x #memx @daemon] 
          % [2: @daemon] % [2: @Hc] % [2: @Hmarksl1] @Hl1
         ]
     |* * #_ #_ #H cases (current_to_midtape … H) #ls * #rs #Ht1
      >Ht1  @ex_intro [2:@ex_intro [2: @ex_intro [2: % [%]|]|]|] %1 %
     ]
   ]
*) 


definition merge_char ≝ λc1,c2.
  match c2 with
  [ null ⇒ c1
  | _ ⇒ c2 ].
  
lemma merge_cons : 
  ∀c1,c2,conf1,conf2.
  merge_config (〈c1,false〉::conf1) (〈c2,false〉::conf2) = 
    〈merge_char c1 c2,false〉::merge_config conf1 conf2.
#c1 #c2 #conf1 #conf2 normalize @eq_f2 //
cases c2 /2/
qed.

lemma merge_bits : ∀l1,l2.|l1| = |l2| → only_bits l2 → merge_config l1 l2 = l2.
#l1 #l2 #Hlen @(list_ind2 … Hlen) //
#tl1 #tl2 #hd1 #hd2 #IH
>(eq_pair_fst_snd … hd1) >(eq_pair_fst_snd … hd2) #Hbits
change with (cons ???) in ⊢ (??%?); @eq_f2
[ cases (\fst hd2) in Hbits; 
  [ #b #_ %
  |*: #Hfalse lapply (Hfalse … (memb_hd …)) normalize #Hfalse1 destruct (Hfalse1) ]
| @IH #x #Hx @Hbits @memb_cons // ]
qed.

lemma merge_config_c_nil : 
  ∀c.merge_config c [] = [].
#c cases c normalize //
qed.

lemma reverse_merge_config :
  ∀c1,c2.|c1| = |c2| → reverse ? (merge_config c1 c2) = 
    merge_config (reverse ? c1) (reverse ? c2).        
#c1 #c2 <(length_reverse ? c1) <(length_reverse ? c2) #Hlen
<(reverse_reverse ? c1) in ⊢ (??%?); <(reverse_reverse ? c2) in ⊢ (??%?);
generalize in match Hlen; @(list_ind2 … Hlen) -Hlen //
#tl1 #tl2 #hd1 #hd2 #IH whd in ⊢ (??%%→?); #Hlen destruct (Hlen) -Hlen
<(length_reverse ? tl1) in e0; <(length_reverse ? tl2) #Hlen
>reverse_cons >reverse_cons >(merge_config_append ???? Hlen)
>reverse_append >(eq_pair_fst_snd ?? hd1) >(eq_pair_fst_snd ?? hd2)
whd in ⊢ (??%%); @eq_f2 // @IH //
qed.

definition copy
≝ 
  seq STape copy0 (seq ? (move_l …) (seq ? (adv_to_mark_l … (is_marked ?))
   (seq ? (clear_mark …) (seq ? (adv_to_mark_r … (is_marked ?)) (clear_mark …))))).

(*
   s0, s1 = caratteri di testa dello stato
   c0 = carattere corrente del nastro oggetto
   c1 = carattere in scrittura sul nastro oggetto
   
   questa dimostrazione sfrutta il fatto che 
   merge_config (l0@[c0]) (l1@[c1]) = l1@[merge_char c0 c1] 
   se l0 e l1 non contengono null
*)

definition R_copy ≝ λt1,t2.
  ∀ls,s0,s1,c0,c1,rs,l1,l3,l4.
  t1 = midtape STape (l3@〈grid,false〉::〈c0,false〉::l4@〈s0,true〉::ls) 〈s1,true〉 (l1@〈c1,false〉::〈comma,false〉::rs) → 
  no_marks l1 → no_marks l3 → no_marks l4 → |l1| = |l4| → 
  only_bits (l4@[〈s0,false〉]) → only_bits (〈s1,false〉::l1) → 
  bit_or_null c0 = true → bit_or_null c1 = true → 
  t2 = midtape STape (〈c1,false〉::reverse ? l1@〈s1,false〉::l3@〈grid,false〉::
                      〈merge_char c0 c1,false〉::reverse ? l1@〈s1,false〉::ls)
       〈comma,false〉 rs.
       
axiom sem_copy0 : Realize ? copy0 R_copy0.

definition option_cons ≝ λA.λa:option A.λl.
  match a with
  [ None ⇒ l
  | Some a' ⇒ a'::l ].


axiom sem_copy : Realize ? copy R_copy.
(*
#intape 
cases (sem_seq … (sem_copy0 …)
        (sem_seq … (sem_move_l …)
          (sem_seq … (sem_adv_to_mark_l … (is_marked ?))
            (sem_seq … (sem_clear_mark …)
              (sem_seq … (sem_adv_to_mark_r … (is_marked ?)) (sem_clear_mark …))))) intape)
#k * #outc * #Hloop #HR %{k} %{outc} % [@Hloop] -Hloop
#ls #s0 #s1 #c0 #c1 #rs #l1 #l2 #l3 #Hintape #Hl1marks #Hl2marks #Hl3marks #Hlen
#Hbits1 #Hbits2 #Hc0bits #Hc1bits
cases HR -HR #ta * whd in ⊢ (%→?); #Hta 
cut (ta = midtape STape (〈c1,false〉::reverse ? l1@〈s1,false〉::l2@〈grid,true〉::
                      〈merge_char c0 c1,false〉::reverse ? l1@〈s1,false〉::ls)
       〈comma,true〉 rs)
[lapply (Hta ls s1 s0 rs (l1@[〈c1,false〉;〈comma,false〉]) l2 (〈grid,false〉::〈c0,false〉::l3) ?)
  [>associative_append in ⊢ (???(????%)); normalize in ⊢ (???(??%%%)); @Hintape ]
 -Hta #Hta cases (Hta ??? (〈s1,false〉::l1@[〈c1,false〉]) false ? ? ?? (refl ??) ?)
  [3: #x #Hx cases (memb_append … Hx) -Hx #Hx
    [ @Hl1marks //
    | cases (orb_true_l … Hx) -Hx #Hx [ >(\P Hx) % | >(memb_single … Hx) % ]] 
  |4: #x #Hx cases (memb_append … Hx) -Hx #Hx
    [ @Hl2marks //
    | cases (orb_true_l … Hx) -Hx #Hx [ >(\P Hx) % | cases (orb_true_l … Hx) [-Hx #Hx >(\P Hx) % | @Hl3marks ] ] ]
  |5: >length_append normalize >Hlen >commutative_plus %
  |6: normalize >associative_append %
  |7: #x #Hx cases (memb_append ?? (〈s1,false〉::l1) … Hx) -Hx #Hx
    [ whd in ⊢ (??%?); >(Hbits2 … Hx) %
    | >(memb_single … Hx) // ]
  |8: #x #Hx cases (memb_append … Hx) -Hx #Hx
    [ cases (orb_true_l … Hx) -Hx #Hx [ >(\P Hx) // | whd in ⊢ (??%?); >Hbits1 // @memb_append_l1 // ]
    | >(memb_single … Hx) whd in ⊢ (??%?); >(Hbits1 〈s0,false〉) // @memb_append_l2 @memb_hd ]
  | * #Hs1 @False_ind >Hs1 in Hbits2; #Hbits2 lapply (Hbits2 〈comma,false〉 ?) //
    normalize #Hfalse destruct (Hfalse)
  | * #Hs1 #Ht2 >Ht2 >reverse_cons >reverse_append >reverse_single @eq_f3 //
    >merge_cons >merge_bits
    [2: #x #Hx @Hbits2 cases (memb_append STape ? (reverse ? l1) ? Hx) -Hx #Hx
      [@daemon | >(memb_single … Hx) @memb_hd ]
    |3: >length_append >length_append >length_reverse >Hlen % ]
    normalize >associative_append normalize >associative_append %
  ]
] -Hta #Hta * #tb * whd in ⊢ (%→?); #Htb
lapply (Htb … Hta) -Htb #Htb change with (midtape ????) in Htb:(???%);
* #tc * whd in ⊢ (%→?); #Htc 
cases (Htc … Htb)
[ * #Hfalse normalize in Hfalse; destruct (Hfalse) ]
* #_ #Htc 
lapply (Htc (reverse ? l1@〈s1,false〉::l2) 〈grid,true〉 
          (〈merge_char c0 c1,false〉::reverse ? l1@〈s1,false〉::ls)???)
[ #x #Hx cases (memb_append … Hx) -Hx #Hx
  [ @Hl1marks @daemon
  | cases (orb_true_l … Hx) -Hx #Hx
    [ >(\P Hx) % | @(Hl2marks … Hx) ] ]
| %
| whd in ⊢ (??%?); >associative_append % ] -Htc #Htc
* #td * whd in ⊢ (%→?); #Htd lapply (Htd … Htc) -Htd #Htd
* #te * whd in ⊢ (%→?); #Hte cases (Hte … Htd) -Hte -Htd
[ * #Hfalse normalize in Hfalse; destruct (Hfalse) ]
* #_ #Hte 
lapply (Hte (reverse ? (reverse ? l1@〈s1,false〉::l2)@[〈c1,false〉])
         〈comma,true〉 rs ? (refl ??) ?) -Hte
[ >reverse_append >reverse_cons >reverse_reverse #x #Hx
  cases (memb_append … Hx) -Hx #Hx
  [ cases (memb_append … Hx) -Hx #Hx
    [ cases (memb_append … Hx) -Hx #Hx
      [ @daemon 
      | lapply (memb_single … Hx) -Hx #Hx >Hx % ]
    | @(Hl1marks … Hx) ]
  | lapply (memb_single … Hx) -Hx #Hx >Hx % ]
| >reverse_append >reverse_reverse >reverse_cons
  >associative_append >associative_append >associative_append
  >associative_append >associative_append % ]
#Hte whd in ⊢ (%→?); #Houtc lapply (Houtc … Hte) -Houtc #Houtc >Houtc
@eq_f3 //
>reverse_append >reverse_append >reverse_single >reverse_cons
>reverse_append >reverse_append >reverse_reverse >reverse_reverse
>reverse_single >associative_append >associative_append %
qed.
*)
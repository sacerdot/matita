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


(* COMPARE BIT

*)

include "turing/universal/marks.ma".

definition STape ≝ FinProd … FSUnialpha FinBool.

definition only_bits ≝ λl.
  ∀c.memb STape c l = true → is_bit (\fst c) = true.

(*
l0 x* a l1 x0* a0 l2 ------> l0 x a* l1 x0 a0* l2
   ^                               ^

if current (* x *) = #
   then 
   else if x = 0
      then move_right; ----
           adv_to_mark_r;
           if current (* x0 *) = 0
              then advance_mark ----
                   adv_to_mark_l;
                   advance_mark
              else STOP
      else x = 1 (* analogo *)

*)


(*
   MARK NEXT TUPLE machine
   (partially axiomatized)
   
   marks the first character after the first bar (rightwards)
 *)
 
check unialpha

axiom is_bar : FinProd … myalpha FinBool → bool.
axiom is_grid : FinProd … myalpha FinBool → bool.
definition bar_or_grid ≝ λc.is_bar c ∨ is_grid c.
axiom bar : FinProd … myalpha FinBool.
axiom grid : FinProd … myalpha FinBool.

definition mark_next_tuple ≝ 
  seq ? (adv_to_mark_r ? bar_or_grid)
     (ifTM ? (test_char ? is_bar)
       (move_r_and_mark ?) (nop ?) 1).

definition R_mark_next_tuple ≝ 
  λt1,t2.
    ∀ls,c,rs1,rs2.
    (* c non può essere un separatore ... speriamo *)
    t1 = midtape ? ls c (rs1@grid::rs2) → 
    memb ? grid rs1 = false → bar_or_grid c = false → 
    (∃rs3,rs4,d,b.rs1 = rs3 @ bar :: rs4 ∧
      memb ? bar rs3 = false ∧ 
      Some ? 〈d,b〉 = option_hd ? (rs4@grid::rs2) ∧
      t2 = midtape ? (bar::reverse ? rs3@c::ls) 〈d,true〉 (tail ? (rs4@grid::rs2)))
    ∨
    (memb ? bar rs1 = false ∧ 
     t2 = midtape ? (reverse ? rs1@c::ls) grid rs2).
     
axiom tech_split :
  ∀A:DeqSet.∀f,l.
   (∀x.memb A x l = true → f x = false) ∨
   (∃l1,c,l2.f c = true ∧ l = l1@c::l2 ∧ ∀x.memb ? x l1 = true → f c = false).
(*#A #f #l elim l
[ % #x normalize #Hfalse *)
     
theorem sem_mark_next_tuple :
  Realize ? mark_next_tuple R_mark_next_tuple.
#intape 
lapply (sem_seq ? (adv_to_mark_r ? bar_or_grid)
         (ifTM ? (test_char ? is_bar) (mark ?) (nop ?) 1) ????)
[@sem_if //
| //
|||#Hif cases (Hif intape) -Hif
   #j * #outc * #Hloop * #ta * #Hleft #Hright
   @(ex_intro ?? j) @ex_intro [|% [@Hloop] ]
   -Hloop
   #ls #c #rs1 #rs2 #Hrs #Hrs1 #Hc
   cases (Hleft … Hrs)
   [ * #Hfalse >Hfalse in Hc; #Htf destruct (Htf)
   | * #_ #Hta cases (tech_split ? is_bar rs1)
     [ #H1 lapply (Hta rs1 grid rs2 (refl ??) ? ?)
       [ (* Hrs1, H1 *) @daemon
       | (* bar_or_grid grid = true *) @daemon
       | -Hta #Hta cases Hright
         [ * #tb * whd in ⊢ (%→?); #Hcurrent
           @False_ind cases(Hcurrent grid ?)
           [ #Hfalse (* grid is not a bar *) @daemon
           | >Hta % ]
         | * #tb * whd in ⊢ (%→?); #Hcurrent
           cases (Hcurrent grid ?)
           [  #_ #Htb whd in ⊢ (%→?); #Houtc
             %2 %
             [ (* H1 *) @daemon
             | >Houtc >Htb >Hta % ]
           | >Hta % ]
         ]
       ]
    | * #rs3 * #c0 * #rs4 * * #Hc0 #Hsplit #Hrs3
      % @(ex_intro ?? rs3) @(ex_intro ?? rs4)
     lapply (Hta rs3 c0 (rs4@grid::rs2) ???)
     [ #x #Hrs3' (* Hrs1, Hrs3, Hsplit *) @daemon
     | (* bar → bar_or_grid *) @daemon
     | >Hsplit >associative_append % ] -Hta #Hta
       cases Hright
       [ * #tb * whd in ⊢ (%→?); #Hta'
         whd in ⊢ (%→?); #Htb
         cases (Hta' c0 ?)
         [ #_ #Htb' >Htb' in Htb; #Htb
           generalize in match Hsplit; -Hsplit
           cases rs4 in Hta;
           [ >(eq_pair_fst_snd … grid)
             #Hta #Hsplit >(Htb … Hta)
             >(?:c0 = bar)
             [ @(ex_intro ?? (\fst grid)) @(ex_intro ?? (\snd grid))
               % [ % [ % [ (* Hsplit *) @daemon |(*Hrs3*) @daemon ] | % ] | % ] 
                     | (* Hc0 *) @daemon ]
           | #r5 #rs5 >(eq_pair_fst_snd … r5)
             #Hta #Hsplit >(Htb … Hta)
             >(?:c0 = bar)
             [ @(ex_intro ?? (\fst r5)) @(ex_intro ?? (\snd r5))
               % [ % [ % [ (* Hc0, Hsplit *) @daemon | (*Hrs3*) @daemon ] | % ]
                     | % ] | (* Hc0 *) @daemon ] ] | >Hta % ]
             | * #tb * whd in ⊢ (%→?); #Hta'
               whd in ⊢ (%→?); #Htb
               cases (Hta' c0 ?)
               [ #Hfalse @False_ind >Hfalse in Hc0;
                 #Hc0 destruct (Hc0)
               | >Hta % ]
]]]]
qed.
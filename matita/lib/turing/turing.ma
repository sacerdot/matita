(*

Macchina A:
postcondizione
PA(in,out) ≝ 
  ∀ls,cs,d,rs.
    left (tape in) = cs@'#'::ls → 
    right (tape in) = d::rs → 
    state in = q0 → 
  left (tape out) = ls ∧
  right (tape out) = d::'#'::rev cs@rs ∧
  state out = qfinal
  
Macchina A0:
postcondizione:
PA0(in,out) ≝ 
  ∀ls,c,rs.
    left (tape in) = c::ls → 
    right (tape in) = d::rs → 
    state in = q0 → 
  left (tape out) = ls ∧
  right (tape out) = d::c::rs
  state out = qfinal

Macchina A1
postcondizione true:
PA1t(in,out) ≝ 
  ∀c,rs.
    right (tape in) = c::rs → 
    tape in = tape out ∧
    (c ≠ '#' → state out = qtrue)
    
postcondizione false:
PA1f(in,out) ≝ 
  ∀c,rs.
    right (tape in) = c::rs → 
    tape in = tape out ∧
    (c = '#' → state out = qfalse) ∧


A = do A0 while A1 inv PA0 var |right (tape in)|;

     posso assumere le precondizioni di A
     H1 : left (tape in) = c::cs@'#'::ls
     H2 : right (tape in) = d::rs

     in particolare H2 → precondizioni di A1
     
     eseguiamo dunque if A1 then (A0; A) else skip
     
  
          
by induction on left (tape in)
     
     per casi su d =?= '#'
     
     Hcase: d ≠ '#' ⇒ 
     eseguo (A1; A0; A)
     devo allora provare che PA1°PA0°PA(in,out) → PA(in,out)
     ∃s1,s2: PA1t(in,s1) ∧ PA0(s1,s2) ∧ PA(s2,out)
     
     usando anche Hcase, ottengo che tape in = tape s1
     soddisfo allora le precondizioni di PA0(s1,s2) ottenendo che
     left (tape s2) = cs@'#'::ls
     right (tape s2) = d::c::rs
     
     soddisfo allora le precondizioni di PA e per ipotesi induttiva
     
       
     left (tape s) = d::cs@'#'::ls
     right (tape s) = 
     
    






∀inc.
  (∃ls,cs,d,rs. left inc = ... ∧ right inc = ... ∧ state inc = q0) → 
∃i,outc. loop i step inc = Some ? outc  
  ∧(∀ls,cs,d,rs.left inc = ... → right inc = ... →
    ∧ left outc = ls
    ∧ right outc = d::"#"::rev cs::rs
    ∧ state outc = qfinal)

ϕ1 M1 ψ1 → ϕ2 M2 ψ2 → 
(ψ1(in1,out1) → ϕ2(out1)) → (ψ2(out1,out2) → ψ3(in1,out2)) →
ϕ1 (M1;M2) ψ3



-----------------------------------------------------
{} (tmp ≝ x; x ≝ y; y ≝ tmp) {x = old(x), y = old(y)}
  

∀inc.
  ∀ls:list sig.
  ∀cs:list (sig\#).
  ∀d.sig.
  ∀rs:list sig.
  left inc = cs@"#"::ls → 
  right inc = d::rs → 
  state inc = q0 → 
∃i,outc. loop i step inc = Some outc 
  ∧
  (∀ls,cs,d,rs.left inc = ... → right inc = ... →
  ∧ left outc = ls
  ∧ right outc = d::"#"::rev cs::rs
  ∧ state outc = qfinal

*)


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

include "basics/vectors.ma".

record tape (sig:FinSet): Type[0] ≝ 
{ left : list sig;
  right: list sig
}.

inductive move : Type[0] ≝
| L : move 
| R : move
| N : move. 

(* We do not distinuish an input tape *)

record TM (sig:FinSet): Type[1] ≝ 
{ states : FinSet;
  tapes_no: nat; (* additional working tapes *)
  trans : states × (Vector (option sig) (S tapes_no)) → 
    states  × (Vector (sig × move) (S tapes_no)) × (option sig) ;
  output: list sig;
  start: states;
  halt : states → bool
}.

record config (sig:FinSet) (M:TM sig): Type[0] ≝
{ state : states sig M;
  tapes : Vector (tape sig) (S (tapes_no sig M));
  out : list sig
}.

definition option_hd ≝ λA.λl:list A.
  match l with
  [nil ⇒ None ?
  |cons a _ ⇒ Some ? a
  ].

definition tape_move ≝ λsig.λt: tape sig.λm:sig × move.
  match \snd m with
  [ R ⇒ mk_tape sig ((\fst m)::(left ? t)) (tail ? (right ? t))
  | L ⇒ mk_tape sig (tail ? (left ? t)) ((\fst m)::(right ? t))
  | N ⇒ mk_tape sig (left ? t) ((\fst m)::(tail ? (right ? t)))
  ].

definition current_chars ≝ λsig.λM:TM sig.λc:config sig M.
  vec_map ?? (λt.option_hd ? (right ? t)) (S (tapes_no sig M)) (tapes ?? c).

definition opt_cons ≝ λA.λa:option A.λl:list A.
  match a with
  [ None ⇒ l
  | Some a ⇒ a::l
  ].

definition step ≝ λsig.λM:TM sig.λc:config sig M.
  let 〈news,mvs,outchar〉 ≝ trans sig M 〈state ?? c,current_chars ?? c〉 in
  mk_config ?? 
    news 
    (pmap_vec ??? (tape_move sig) ? (tapes ?? c) mvs)
    (opt_cons ? outchar (out ?? c)).

definition empty_tapes ≝ λsig.λn.
mk_Vector ? n (make_list (tape sig) (mk_tape sig [] []) n) ?.
elim n // normalize //
qed.

definition init ≝ λsig.λM:TM sig.λi:(list sig).
  mk_config ??
    (start sig M)
    (vec_cons ? (mk_tape sig [] i) ? (empty_tapes sig (tapes_no sig M)))
    [ ].

definition stop ≝ λsig.λM:TM sig.λc:config sig M.
  halt sig M (state sig M c).

let rec loop (A:Type[0]) n (f:A→A) p a on n ≝
  match n with 
  [ O ⇒ None ?
  | S m ⇒ if p a then (Some ? a) else loop A m f p (f a)
  ].

(* Compute ? M f states that f is computed by M *)
definition Compute ≝ λsig.λM:TM sig.λf:(list sig) → (list sig).
∀l.∃i.∃c.
  loop ? i (step sig M) (stop sig M) (init sig M l) = Some ? c ∧
  out ?? c = f l.

(* for decision problems, we accept a string if on termination
output is not empty *)

definition ComputeB ≝ λsig.λM:TM sig.λf:(list sig) → bool.
∀l.∃i.∃c.
  loop ? i (step sig M) (stop sig M) (init sig M l) = Some ? c ∧
  (isnilb ? (out ?? c) = false).

(* alternative approach.
We define the notion of computation. The notion must be constructive,
since we want to define functions over it, like lenght and size 

Perche' serve Type[2] se sposto a e b a destra? *)

inductive cmove (A:Type[0]) (f:A→A) (p:A →bool) (a,b:A): Type[0] ≝
  mk_move: p a = false → b = f a → cmove A f p a b.
  
inductive cstar (A:Type[0]) (M:A→A→Type[0]) : A →A → Type[0] ≝
| empty : ∀a. cstar A M a a
| more : ∀a,b,c. M a b → cstar A M b c → cstar A M a c.

definition computation ≝ λsig.λM:TM sig.
  cstar ? (cmove ? (step sig M) (stop sig M)).

definition Compute_expl ≝ λsig.λM:TM sig.λf:(list sig) → (list sig).
  ∀l.∃c.computation sig M (init sig M l) c → 
   (stop sig M c = true) ∧ out ?? c = f l.

definition ComputeB_expl ≝ λsig.λM:TM sig.λf:(list sig) → bool.
  ∀l.∃c.computation sig M (init sig M l) c → 
   (stop sig M c = true) ∧ (isnilb ? (out ?? c) = false).

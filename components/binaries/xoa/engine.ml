(*
    ||M||  This file is part of HELM, an Hypertextual, Electronic        
    ||A||  Library of Mathematics, developed at the Computer Science     
    ||T||  Department, University of Bologna, Italy.                     
    ||I||                                                                
    ||T||  HELM is free software; you can redistribute it and/or         
    ||A||  modify it under the terms of the GNU General Public License   
    \   /  version 2 or (at your option) any later version.      
     \ /   This software is distributed as is, NO WARRANTY.     
      V_______________________________________________________________ *)

module P = Printf
module A = Ast

let string_iter sep f n =
   let rec aux = function
      | n when n < 1 -> ""
      | 1            -> f 1
      | n            -> f n ^ sep ^ aux (pred n)
   in
   aux n

let void_iter f n =
   let rec aux = function
      | n when n < 1 -> ()
      | 1            -> f 1
      | n            -> f n; aux (pred n)
   in
   aux n

let mk_exists ooch noch c v =
   let description = "multiple existental quantifier" in
   let prec = "non associative with precedence 20\n" in
   let name s = 
      if v = 1 then P.sprintf "%s%u" s c else P.sprintf "%s%u_%u" s c v
   in
   let o_name = name "ex" in
   let i_name = "'Ex" in

   let set n      = P.sprintf "A%u" (v - n) in
   let set_list   = string_iter "," set v in   
   let set_type   = string_iter "→" set v in
      
   let ele n      = P.sprintf "x%u" (v - n) in
   let ele_list   = string_iter "," ele v in
   let ele_seq    = string_iter " " ele v in
   
   let pre n      = P.sprintf "P%u" (c - n) in   
   let pre_list   = string_iter "," pre c in
   let pre_seq    = string_iter " " pre c in 
   let pre_appl n = P.sprintf "%s %s" (pre n) ele_seq in 
   let pre_type   = string_iter " → " pre_appl c in

   let qm n       = "?" in
   let qm_set     = string_iter " " qm v in 
   let qm_pre     = string_iter " " qm c in 

   let id n       = P.sprintf "ident x%u" (v - n) in
   let id_list    = string_iter " , " id v in 

   let term n     = P.sprintf "term 19 P%u" (c - n) in
   let term_conj  = string_iter " break & " term c in 

   let abst b n   = let xty = if b then P.sprintf ":$T%u" (v - n) else "" in
                    P.sprintf "λ${ident x%u}%s" (v - n) xty in

   let abst_clo b = string_iter "." (abst b) v in 

   let full b n   = P.sprintf "(%s.$P%u)" (abst_clo b) (c - n) in 
   let full_seq b = string_iter " " (full b) c in

   P.fprintf ooch "(* %s (%u, %u) *)\n\n" description c v;

   P.fprintf ooch "inductive %s (%s:Type[0]) (%s:%s→Prop) : Prop ≝\n" 
      o_name set_list pre_list set_type;
   P.fprintf ooch "   | %s_intro: ∀%s. %s → %s %s %s\n.\n\n"
      o_name ele_list pre_type o_name qm_set qm_pre;

   P.fprintf ooch "interpretation \"%s (%u, %u)\" %s %s = (%s %s %s).\n\n"
      description c v i_name pre_seq o_name qm_set pre_seq;

   P.fprintf noch "(* %s (%u, %u) *)\n\n" description c v;

   P.fprintf noch "notation > \"hvbox(∃∃ %s break . %s)\"\n %s for @{ %s %s }.\n\n"
      id_list term_conj prec i_name (full_seq false);

   P.fprintf noch "notation < \"hvbox(∃∃ %s break . %s)\"\n %s for @{ %s %s }.\n\n"
      id_list term_conj prec i_name (full_seq true)

let mk_or ooch noch c =
   let description = "multiple disjunction connective" in
   let prec = "non associative with precedence 30\n" in
   let name s = P.sprintf "%s%u" s c in
   let o_name = name "or" in
   let i_name = "'Or" in

   let pre n      = P.sprintf "P%u" (c - n) in   
   let pre_list   = string_iter "," pre c in
   let pre_seq    = string_iter " " pre c in 

   let qm n       = "?" in
   let qm_pre     = string_iter " " qm c in 

   let term n     = P.sprintf "term 29 P%u" (c - n) in
   let term_disj  = string_iter " break | " term c in 

   let par n     = P.sprintf "$P%u" (c - n) in 
   let par_seq   = string_iter " " par c in

   let mk_con n   = P.fprintf ooch "   | %s_intro%u: %s → %s %s\n"
                       o_name (c - n) (pre n) o_name qm_pre
   in

   P.fprintf ooch "(* %s (%u) *)\n\n" description c;

   P.fprintf ooch "inductive %s (%s:Prop) : Prop ≝\n" 
      o_name pre_list;
   void_iter mk_con c;
   P.fprintf ooch ".\n\n";

   P.fprintf ooch "interpretation \"%s (%u)\" %s %s = (%s %s).\n\n"
      description c i_name pre_seq o_name pre_seq;

   P.fprintf noch "(* %s (%u) *)\n\n" description c;

   P.fprintf noch "notation \"hvbox(∨∨ %s)\"\n %s for @{ %s %s }.\n\n"
      term_disj prec i_name par_seq

let mk_and ooch noch c =
   let description = "multiple conjunction connective" in
   let prec = "non associative with precedence 35\n" in
   let name s = P.sprintf "%s%u" s c in
   let o_name = name "and" in
   let i_name = "'And" in

   let pre n      = P.sprintf "P%u" (c - n) in   
   let pre_list   = string_iter "," pre c in
   let pre_type   = string_iter " → " pre c in   
   let pre_seq    = string_iter " " pre c in 

   let qm n       = "?" in
   let qm_pre     = string_iter " " qm c in 

   let term n     = P.sprintf "term 34 P%u" (c - n) in
   let term_conj  = string_iter " break & " term c in 

   let par n     = P.sprintf "$P%u" (c - n) in 
   let par_seq   = string_iter " " par c in

   P.fprintf ooch "(* %s (%u) *)\n\n" description c;

   P.fprintf ooch "inductive %s (%s:Prop) : Prop ≝\n" 
      o_name pre_list;
   P.fprintf ooch "   | %s_intro: %s → %s %s\n.\n\n"
      o_name pre_type o_name qm_pre;

   P.fprintf ooch "interpretation \"%s (%u)\" %s %s = (%s %s).\n\n"
      description c i_name pre_seq o_name pre_seq;

   P.fprintf noch "(* %s (%u) *)\n\n" description c;

   P.fprintf noch "notation \"hvbox(∧∧ %s)\"\n %s for @{ %s %s }.\n\n"
      term_conj prec i_name par_seq

let generate ooch noch = function
   | A.Exists (c, v) ->
      if c > 0 && v > 0 then mk_exists ooch noch c v
   | A.Or c          ->
      if c > 1 then mk_or ooch noch c
   | A.And c         ->
      if c > 1 then mk_and ooch noch c

(*
    ||M||  This file is part of HELM, an Hypertextual, Electronic
    ||A||  Library of Mathematics, developed at the Computer Science
    ||T||  Department of the University of Bologna, Italy.
    ||I||
    ||T||
    ||A||  This file is distributed under the terms of the
    \   /  GNU General Public License Version 2
     \ /
      V_______________________________________________________________ *)

(* THE FORMAL SYSTEM λδ - MATITA SOURCE SCRIPTS 
 * Specification started: 2011 April 17
 * - Patience on me so that I gain peace and perfection! -
 * [ suggested invocation to start formal specifications with ]
 *)

include "lambda-delta/ground.ma".

(* BINARY ITEMS *************************************************************)

(* binary items *)
inductive item2: Type[0] ≝
   | Abbr: item2 (* abbreviation *)
   | Abst: item2 (* abstraction *)
   | Appl: item2 (* application *)
   | Cast: item2 (* explicit type annotation *)
.

(* reduction-related categorization *****************************************)

(* binary items entitled for theta reduction *)
definition thable2 ≝ λI. I = Abbr.

(* binary items entitled for zeta reduction *)
definition zable2 ≝ λI. I = Abbr ∨ I = Cast.

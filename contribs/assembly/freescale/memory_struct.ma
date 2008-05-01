(**************************************************************************)
(*       ___                                                              *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||         The HELM team.                                      *)
(*      ||A||         http://helm.cs.unibo.it                             *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU General Public License Version 2                  *)
(*                                                                        *)
(**************************************************************************)

(* ********************************************************************** *)
(*                           Progetto FreeScale                           *)
(*                                                                        *)
(* Sviluppato da:                                                         *)
(*   Cosimo Oliboni, oliboni@cs.unibo.it                                  *)
(*                                                                        *)
(* Questo materiale fa parte della tesi:                                  *)
(*   "Formalizzazione Interattiva dei Microcontroller a 8bit FreeScale"   *)
(*                                                                        *)
(*                    data ultima modifica 15/11/2007                     *)
(* ********************************************************************** *)

include "freescale/translation.ma".

(* **************************** *)
(* TIPI PER I MODULI DI MEMORIA *)
(* **************************** *)

(* tipi di memoria:RAM/ROM/non installata *)
inductive memory_type : Type ≝
  MEM_READ_ONLY: memory_type
| MEM_READ_WRITE: memory_type
| MEM_OUT_OF_BOUND: memory_type.

(* **************** *)
(* TIPO ARRAY DA 16 *)
(* **************** *)

(* definizione di un array omogeneo di dimensione 16 *)
inductive Prod16T (T:Type) : Type ≝
array_16T : T → T → T → T → T → T → T → T →
            T → T → T → T → T → T → T → T →
            Prod16T T.

(* abbiamo gia' gli esadecimali come tipo induttivo quindi: *)
(* posso definire un getter a matrice sull'array *)
definition getn_array16T ≝
λn:exadecim.λT:Type.λp:Prod16T T.
 match p with 
  [ array_16T e00 e01 e02 e03 e04 e05 e06 e07 e08 e09 e10 e11 e12 e13 e14 e15 ⇒
 match n with
  [ x0 ⇒ e00 | x1 ⇒ e01 | x2 ⇒ e02 | x3 ⇒ e03 | x4 ⇒ e04 | x5 ⇒ e05 | x6 ⇒ e06 | x7 ⇒ e07
  | x8 ⇒ e08 | x9 ⇒ e09 | xA ⇒ e10 | xB ⇒ e11 | xC ⇒ e12 | xD ⇒ e13 | xE ⇒ e14 | xF ⇒ e15
  ]].

(* abbiamo gia' gli esadecimali come tipo induttivo quindi: *)
(* posso definire un setter a matrice sull'array *)
definition setn_array16T ≝
λn:exadecim.λT:Type.λp:Prod16T T.λv:T.
 match p with 
  [ array_16T e00 e01 e02 e03 e04 e05 e06 e07 e08 e09 e10 e11 e12 e13 e14 e15 ⇒
 match n with
  [ x0 ⇒ array_16T T v   e01 e02 e03 e04 e05 e06 e07 e08 e09 e10 e11 e12 e13 e14 e15
  | x1 ⇒ array_16T T e00 v   e02 e03 e04 e05 e06 e07 e08 e09 e10 e11 e12 e13 e14 e15
  | x2 ⇒ array_16T T e00 e01 v   e03 e04 e05 e06 e07 e08 e09 e10 e11 e12 e13 e14 e15
  | x3 ⇒ array_16T T e00 e01 e02 v   e04 e05 e06 e07 e08 e09 e10 e11 e12 e13 e14 e15
  | x4 ⇒ array_16T T e00 e01 e02 e03 v   e05 e06 e07 e08 e09 e10 e11 e12 e13 e14 e15
  | x5 ⇒ array_16T T e00 e01 e02 e03 e04 v   e06 e07 e08 e09 e10 e11 e12 e13 e14 e15
  | x6 ⇒ array_16T T e00 e01 e02 e03 e04 e05 v   e07 e08 e09 e10 e11 e12 e13 e14 e15
  | x7 ⇒ array_16T T e00 e01 e02 e03 e04 e05 e06 v   e08 e09 e10 e11 e12 e13 e14 e15
  | x8 ⇒ array_16T T e00 e01 e02 e03 e04 e05 e06 e07 v   e09 e10 e11 e12 e13 e14 e15
  | x9 ⇒ array_16T T e00 e01 e02 e03 e04 e05 e06 e07 e08 v   e10 e11 e12 e13 e14 e15
  | xA ⇒ array_16T T e00 e01 e02 e03 e04 e05 e06 e07 e08 e09 v   e11 e12 e13 e14 e15
  | xB ⇒ array_16T T e00 e01 e02 e03 e04 e05 e06 e07 e08 e09 e10 v   e12 e13 e14 e15
  | xC ⇒ array_16T T e00 e01 e02 e03 e04 e05 e06 e07 e08 e09 e10 e11 v   e13 e14 e15
  | xD ⇒ array_16T T e00 e01 e02 e03 e04 e05 e06 e07 e08 e09 e10 e11 e12 v   e14 e15
  | xE ⇒ array_16T T e00 e01 e02 e03 e04 e05 e06 e07 e08 e09 e10 e11 e12 e13 v   e15
  | xF ⇒ array_16T T e00 e01 e02 e03 e04 e05 e06 e07 e08 e09 e10 e11 e12 e13 e14 v
  ]].

(* abbiamo gia' gli esadecimali come tipo induttivo quindi: *)
(* posso definire un setter multiplo [m,n] a matrice sull'array *)
definition setmn_array16T ≝
λm,n:exadecim.λT:Type.λp:Prod16T T.λv:T.
 match p with 
  [ array_16T e00 e01 e02 e03 e04 e05 e06 e07 e08 e09 e10 e11 e12 e13 e14 e15 ⇒
 match m with
  [ x0 ⇒ match n with
   [ x0 ⇒ array_16T T v e01 e02 e03 e04 e05 e06 e07 e08 e09 e10 e11 e12 e13 e14 e15
   | x1 ⇒ array_16T T v v   e02 e03 e04 e05 e06 e07 e08 e09 e10 e11 e12 e13 e14 e15
   | x2 ⇒ array_16T T v v   v   e03 e04 e05 e06 e07 e08 e09 e10 e11 e12 e13 e14 e15
   | x3 ⇒ array_16T T v v   v   v   e04 e05 e06 e07 e08 e09 e10 e11 e12 e13 e14 e15
   | x4 ⇒ array_16T T v v   v   v   v   e05 e06 e07 e08 e09 e10 e11 e12 e13 e14 e15
   | x5 ⇒ array_16T T v v   v   v   v   v   e06 e07 e08 e09 e10 e11 e12 e13 e14 e15
   | x6 ⇒ array_16T T v v   v   v   v   v   v   e07 e08 e09 e10 e11 e12 e13 e14 e15
   | x7 ⇒ array_16T T v v   v   v   v   v   v   v   e08 e09 e10 e11 e12 e13 e14 e15
   | x8 ⇒ array_16T T v v   v   v   v   v   v   v   v   e09 e10 e11 e12 e13 e14 e15
   | x9 ⇒ array_16T T v v   v   v   v   v   v   v   v   v   e10 e11 e12 e13 e14 e15
   | xA ⇒ array_16T T v v   v   v   v   v   v   v   v   v   v   e11 e12 e13 e14 e15
   | xB ⇒ array_16T T v v   v   v   v   v   v   v   v   v   v   v   e12 e13 e14 e15
   | xC ⇒ array_16T T v v   v   v   v   v   v   v   v   v   v   v   v   e13 e14 e15
   | xD ⇒ array_16T T v v   v   v   v   v   v   v   v   v   v   v   v   v   e14 e15
   | xE ⇒ array_16T T v v   v   v   v   v   v   v   v   v   v   v   v   v   v   e15
   | xF ⇒ array_16T T v v   v   v   v   v   v   v   v   v   v   v   v   v   v   v ]
  | x1 ⇒ match n with
   [ x0 ⇒ p
   | x1 ⇒ array_16T T e00 v e02 e03 e04 e05 e06 e07 e08 e09 e10 e11 e12 e13 e14 e15
   | x2 ⇒ array_16T T e00 v v   e03 e04 e05 e06 e07 e08 e09 e10 e11 e12 e13 e14 e15
   | x3 ⇒ array_16T T e00 v v   v   e04 e05 e06 e07 e08 e09 e10 e11 e12 e13 e14 e15
   | x4 ⇒ array_16T T e00 v v   v   v   e05 e06 e07 e08 e09 e10 e11 e12 e13 e14 e15
   | x5 ⇒ array_16T T e00 v v   v   v   v   e06 e07 e08 e09 e10 e11 e12 e13 e14 e15
   | x6 ⇒ array_16T T e00 v v   v   v   v   v   e07 e08 e09 e10 e11 e12 e13 e14 e15
   | x7 ⇒ array_16T T e00 v v   v   v   v   v   v   e08 e09 e10 e11 e12 e13 e14 e15
   | x8 ⇒ array_16T T e00 v v   v   v   v   v   v   v   e09 e10 e11 e12 e13 e14 e15
   | x9 ⇒ array_16T T e00 v v   v   v   v   v   v   v   v   e10 e11 e12 e13 e14 e15
   | xA ⇒ array_16T T e00 v v   v   v   v   v   v   v   v   v   e11 e12 e13 e14 e15
   | xB ⇒ array_16T T e00 v v   v   v   v   v   v   v   v   v   v   e12 e13 e14 e15
   | xC ⇒ array_16T T e00 v v   v   v   v   v   v   v   v   v   v   v   e13 e14 e15
   | xD ⇒ array_16T T e00 v v   v   v   v   v   v   v   v   v   v   v   v   e14 e15
   | xE ⇒ array_16T T e00 v v   v   v   v   v   v   v   v   v   v   v   v   v   e15
   | xF ⇒ array_16T T e00 v v   v   v   v   v   v   v   v   v   v   v   v   v   v ]
  | x2 ⇒ match n with
   [ x0 ⇒ p | x1 ⇒ p
   | x2 ⇒ array_16T T e00 e01 v e03 e04 e05 e06 e07 e08 e09 e10 e11 e12 e13 e14 e15
   | x3 ⇒ array_16T T e00 e01 v v   e04 e05 e06 e07 e08 e09 e10 e11 e12 e13 e14 e15
   | x4 ⇒ array_16T T e00 e01 v v   v   e05 e06 e07 e08 e09 e10 e11 e12 e13 e14 e15
   | x5 ⇒ array_16T T e00 e01 v v   v   v   e06 e07 e08 e09 e10 e11 e12 e13 e14 e15
   | x6 ⇒ array_16T T e00 e01 v v   v   v   v   e07 e08 e09 e10 e11 e12 e13 e14 e15
   | x7 ⇒ array_16T T e00 e01 v v   v   v   v   v   e08 e09 e10 e11 e12 e13 e14 e15
   | x8 ⇒ array_16T T e00 e01 v v   v   v   v   v   v   e09 e10 e11 e12 e13 e14 e15
   | x9 ⇒ array_16T T e00 e01 v v   v   v   v   v   v   v   e10 e11 e12 e13 e14 e15
   | xA ⇒ array_16T T e00 e01 v v   v   v   v   v   v   v   v   e11 e12 e13 e14 e15
   | xB ⇒ array_16T T e00 e01 v v   v   v   v   v   v   v   v   v   e12 e13 e14 e15
   | xC ⇒ array_16T T e00 e01 v v   v   v   v   v   v   v   v   v   v   e13 e14 e15
   | xD ⇒ array_16T T e00 e01 v v   v   v   v   v   v   v   v   v   v   v   e14 e15
   | xE ⇒ array_16T T e00 e01 v v   v   v   v   v   v   v   v   v   v   v   v   e15
   | xF ⇒ array_16T T e00 e01 v v   v   v   v   v   v   v   v   v   v   v   v   v ]
  | x3 ⇒ match n with
   [ x0 ⇒ p | x1 ⇒ p | x2 ⇒ p
   | x3 ⇒ array_16T T e00 e01 e02 v e04 e05 e06 e07 e08 e09 e10 e11 e12 e13 e14 e15
   | x4 ⇒ array_16T T e00 e01 e02 v v   e05 e06 e07 e08 e09 e10 e11 e12 e13 e14 e15
   | x5 ⇒ array_16T T e00 e01 e02 v v   v   e06 e07 e08 e09 e10 e11 e12 e13 e14 e15
   | x6 ⇒ array_16T T e00 e01 e02 v v   v   v   e07 e08 e09 e10 e11 e12 e13 e14 e15
   | x7 ⇒ array_16T T e00 e01 e02 v v   v   v   v   e08 e09 e10 e11 e12 e13 e14 e15
   | x8 ⇒ array_16T T e00 e01 e02 v v   v   v   v   v   e09 e10 e11 e12 e13 e14 e15
   | x9 ⇒ array_16T T e00 e01 e02 v v   v   v   v   v   v   e10 e11 e12 e13 e14 e15
   | xA ⇒ array_16T T e00 e01 e02 v v   v   v   v   v   v   v   e11 e12 e13 e14 e15
   | xB ⇒ array_16T T e00 e01 e02 v v   v   v   v   v   v   v   v   e12 e13 e14 e15
   | xC ⇒ array_16T T e00 e01 e02 v v   v   v   v   v   v   v   v   v   e13 e14 e15
   | xD ⇒ array_16T T e00 e01 e02 v v   v   v   v   v   v   v   v   v   v   e14 e15
   | xE ⇒ array_16T T e00 e01 e02 v v   v   v   v   v   v   v   v   v   v   v   e15
   | xF ⇒ array_16T T e00 e01 e02 v v   v   v   v   v   v   v   v   v   v   v   v ]
  | x4 ⇒ match n with
   [ x0 ⇒ p | x1 ⇒ p | x2 ⇒ p | x3 ⇒ p
   | x4 ⇒ array_16T T e00 e01 e02 e03 v e05 e06 e07 e08 e09 e10 e11 e12 e13 e14 e15
   | x5 ⇒ array_16T T e00 e01 e02 e03 v v   e06 e07 e08 e09 e10 e11 e12 e13 e14 e15
   | x6 ⇒ array_16T T e00 e01 e02 e03 v v   v   e07 e08 e09 e10 e11 e12 e13 e14 e15
   | x7 ⇒ array_16T T e00 e01 e02 e03 v v   v   v   e08 e09 e10 e11 e12 e13 e14 e15
   | x8 ⇒ array_16T T e00 e01 e02 e03 v v   v   v   v   e09 e10 e11 e12 e13 e14 e15
   | x9 ⇒ array_16T T e00 e01 e02 e03 v v   v   v   v   v   e10 e11 e12 e13 e14 e15
   | xA ⇒ array_16T T e00 e01 e02 e03 v v   v   v   v   v   v   e11 e12 e13 e14 e15
   | xB ⇒ array_16T T e00 e01 e02 e03 v v   v   v   v   v   v   v   e12 e13 e14 e15
   | xC ⇒ array_16T T e00 e01 e02 e03 v v   v   v   v   v   v   v   v   e13 e14 e15
   | xD ⇒ array_16T T e00 e01 e02 e03 v v   v   v   v   v   v   v   v   v   e14 e15
   | xE ⇒ array_16T T e00 e01 e02 e03 v v   v   v   v   v   v   v   v   v   v   e15
   | xF ⇒ array_16T T e00 e01 e02 e03 v v   v   v   v   v   v   v   v   v   v   v ]
  | x5 ⇒ match n with
   [ x0 ⇒ p | x1 ⇒ p | x2 ⇒ p | x3 ⇒ p | x4 ⇒ p
   | x5 ⇒ array_16T T e00 e01 e02 e03 e04 v e06 e07 e08 e09 e10 e11 e12 e13 e14 e15
   | x6 ⇒ array_16T T e00 e01 e02 e03 e04 v v   e07 e08 e09 e10 e11 e12 e13 e14 e15
   | x7 ⇒ array_16T T e00 e01 e02 e03 e04 v v   v   e08 e09 e10 e11 e12 e13 e14 e15
   | x8 ⇒ array_16T T e00 e01 e02 e03 e04 v v   v   v   e09 e10 e11 e12 e13 e14 e15
   | x9 ⇒ array_16T T e00 e01 e02 e03 e04 v v   v   v   v   e10 e11 e12 e13 e14 e15
   | xA ⇒ array_16T T e00 e01 e02 e03 e04 v v   v   v   v   v   e11 e12 e13 e14 e15
   | xB ⇒ array_16T T e00 e01 e02 e03 e04 v v   v   v   v   v   v   e12 e13 e14 e15
   | xC ⇒ array_16T T e00 e01 e02 e03 e04 v v   v   v   v   v   v   v   e13 e14 e15
   | xD ⇒ array_16T T e00 e01 e02 e03 e04 v v   v   v   v   v   v   v   v   e14 e15
   | xE ⇒ array_16T T e00 e01 e02 e03 e04 v v   v   v   v   v   v   v   v   v   e15
   | xF ⇒ array_16T T e00 e01 e02 e03 e04 v v   v   v   v   v   v   v   v   v   v ]
  | x6 ⇒ match n with
   [ x0 ⇒ p | x1 ⇒ p | x2 ⇒ p | x3 ⇒ p | x4 ⇒ p | x5 ⇒ p
   | x6 ⇒ array_16T T e00 e01 e02 e03 e04 e05 v e07 e08 e09 e10 e11 e12 e13 e14 e15
   | x7 ⇒ array_16T T e00 e01 e02 e03 e04 e05 v v   e08 e09 e10 e11 e12 e13 e14 e15
   | x8 ⇒ array_16T T e00 e01 e02 e03 e04 e05 v v   v   e09 e10 e11 e12 e13 e14 e15
   | x9 ⇒ array_16T T e00 e01 e02 e03 e04 e05 v v   v   v   e10 e11 e12 e13 e14 e15
   | xA ⇒ array_16T T e00 e01 e02 e03 e04 e05 v v   v   v   v   e11 e12 e13 e14 e15
   | xB ⇒ array_16T T e00 e01 e02 e03 e04 e05 v v   v   v   v   v   e12 e13 e14 e15
   | xC ⇒ array_16T T e00 e01 e02 e03 e04 e05 v v   v   v   v   v   v   e13 e14 e15
   | xD ⇒ array_16T T e00 e01 e02 e03 e04 e05 v v   v   v   v   v   v   v   e14 e15
   | xE ⇒ array_16T T e00 e01 e02 e03 e04 e05 v v   v   v   v   v   v   v   v   e15
   | xF ⇒ array_16T T e00 e01 e02 e03 e04 e05 v v   v   v   v   v   v   v   v   v ]
  | x7 ⇒ match n with
   [ x0 ⇒ p | x1 ⇒ p | x2 ⇒ p | x3 ⇒ p | x4 ⇒ p | x5 ⇒ p | x6 ⇒ p
   | x7 ⇒ array_16T T e00 e01 e02 e03 e04 e05 e06 v e08 e09 e10 e11 e12 e13 e14 e15
   | x8 ⇒ array_16T T e00 e01 e02 e03 e04 e05 e06 v v   e09 e10 e11 e12 e13 e14 e15
   | x9 ⇒ array_16T T e00 e01 e02 e03 e04 e05 e06 v v   v   e10 e11 e12 e13 e14 e15
   | xA ⇒ array_16T T e00 e01 e02 e03 e04 e05 e06 v v   v   v   e11 e12 e13 e14 e15
   | xB ⇒ array_16T T e00 e01 e02 e03 e04 e05 e06 v v   v   v   v   e12 e13 e14 e15
   | xC ⇒ array_16T T e00 e01 e02 e03 e04 e05 e06 v v   v   v   v   v   e13 e14 e15
   | xD ⇒ array_16T T e00 e01 e02 e03 e04 e05 e06 v v   v   v   v   v   v   e14 e15
   | xE ⇒ array_16T T e00 e01 e02 e03 e04 e05 e06 v v   v   v   v   v   v   v   e15
   | xF ⇒ array_16T T e00 e01 e02 e03 e04 e05 e06 v v   v   v   v   v   v   v   v ]
  | x8 ⇒ match n with
   [ x0 ⇒ p | x1 ⇒ p | x2 ⇒ p | x3 ⇒ p | x4 ⇒ p | x5 ⇒ p | x6 ⇒ p | x7 ⇒ p
   | x8 ⇒ array_16T T e00 e01 e02 e03 e04 e05 e06 e07 v e09 e10 e11 e12 e13 e14 e15
   | x9 ⇒ array_16T T e00 e01 e02 e03 e04 e05 e06 e07 v v   e10 e11 e12 e13 e14 e15
   | xA ⇒ array_16T T e00 e01 e02 e03 e04 e05 e06 e07 v v   v   e11 e12 e13 e14 e15
   | xB ⇒ array_16T T e00 e01 e02 e03 e04 e05 e06 e07 v v   v   v   e12 e13 e14 e15
   | xC ⇒ array_16T T e00 e01 e02 e03 e04 e05 e06 e07 v v   v   v   v   e13 e14 e15
   | xD ⇒ array_16T T e00 e01 e02 e03 e04 e05 e06 e07 v v   v   v   v   v   e14 e15
   | xE ⇒ array_16T T e00 e01 e02 e03 e04 e05 e06 e07 v v   v   v   v   v   v   e15
   | xF ⇒ array_16T T e00 e01 e02 e03 e04 e05 e06 e07 v v   v   v   v   v   v   v ]
  | x9 ⇒ match n with
   [ x0 ⇒ p | x1 ⇒ p | x2 ⇒ p  | x3 ⇒ p | x4 ⇒ p | x5 ⇒ p | x6 ⇒ p | x7 ⇒ p
   | x8 ⇒ p
   | x9 ⇒ array_16T T e00 e01 e02 e03 e04 e05 e06 e07 e08 v e10 e11 e12 e13 e14 e15
   | xA ⇒ array_16T T e00 e01 e02 e03 e04 e05 e06 e07 e08 v v   e11 e12 e13 e14 e15
   | xB ⇒ array_16T T e00 e01 e02 e03 e04 e05 e06 e07 e08 v v   v   e12 e13 e14 e15
   | xC ⇒ array_16T T e00 e01 e02 e03 e04 e05 e06 e07 e08 v v   v   v   e13 e14 e15
   | xD ⇒ array_16T T e00 e01 e02 e03 e04 e05 e06 e07 e08 v v   v   v   v   e14 e15
   | xE ⇒ array_16T T e00 e01 e02 e03 e04 e05 e06 e07 e08 v v   v   v   v   v   e15
   | xF ⇒ array_16T T e00 e01 e02 e03 e04 e05 e06 e07 e08 v v   v   v   v   v   v ]
  | xA ⇒ match n with
   [ x0 ⇒ p | x1 ⇒ p | x2 ⇒ p | x3 ⇒ p | x4 ⇒ p | x5 ⇒ p | x6 ⇒ p | x7 ⇒ p
   | x8 ⇒ p | x9 ⇒ p
   | xA ⇒ array_16T T e00 e01 e02 e03 e04 e05 e06 e07 e08 e09 v e11 e12 e13 e14 e15
   | xB ⇒ array_16T T e00 e01 e02 e03 e04 e05 e06 e07 e08 e09 v v   e12 e13 e14 e15
   | xC ⇒ array_16T T e00 e01 e02 e03 e04 e05 e06 e07 e08 e09 v v   v   e13 e14 e15
   | xD ⇒ array_16T T e00 e01 e02 e03 e04 e05 e06 e07 e08 e09 v v   v   v   e14 e15
   | xE ⇒ array_16T T e00 e01 e02 e03 e04 e05 e06 e07 e08 e09 v v   v   v   v   e15
   | xF ⇒ array_16T T e00 e01 e02 e03 e04 e05 e06 e07 e08 e09 v v   v   v   v   v ]
  | xB ⇒ match n with
   [ x0 ⇒ p | x1 ⇒ p | x2 ⇒ p | x3 ⇒ p | x4 ⇒ p | x5 ⇒ p | x6 ⇒ p | x7 ⇒ p
   | x8 ⇒ p | x9 ⇒ p | xA ⇒ p
   | xB ⇒ array_16T T e00 e01 e02 e03 e04 e05 e06 e07 e08 e09 e10 v e12 e13 e14 e15
   | xC ⇒ array_16T T e00 e01 e02 e03 e04 e05 e06 e07 e08 e09 e10 v v   e13 e14 e15
   | xD ⇒ array_16T T e00 e01 e02 e03 e04 e05 e06 e07 e08 e09 e10 v v   v   e14 e15
   | xE ⇒ array_16T T e00 e01 e02 e03 e04 e05 e06 e07 e08 e09 e10 v v   v   v   e15
   | xF ⇒ array_16T T e00 e01 e02 e03 e04 e05 e06 e07 e08 e09 e10 v v   v   v   v ]
  | xC ⇒ match n with
   [ x0 ⇒ p | x1 ⇒ p | x2 ⇒ p | x3 ⇒ p | x4 ⇒ p | x5 ⇒ p | x6 ⇒ p | x7 ⇒ p
   | x8 ⇒ p | x9 ⇒ p | xA ⇒ p | xB ⇒ p
   | xC ⇒ array_16T T e00 e01 e02 e03 e04 e05 e06 e07 e08 e09 e10 e11 v e13 e14 e15
   | xD ⇒ array_16T T e00 e01 e02 e03 e04 e05 e06 e07 e08 e09 e10 e11 v v   e14 e15
   | xE ⇒ array_16T T e00 e01 e02 e03 e04 e05 e06 e07 e08 e09 e10 e11 v v   v   e15
   | xF ⇒ array_16T T e00 e01 e02 e03 e04 e05 e06 e07 e08 e09 e10 e11 v v   v   v ]
  | xD ⇒ match n with
   [ x0 ⇒ p | x1 ⇒ p | x2 ⇒ p | x3 ⇒ p | x4 ⇒ p | x5 ⇒ p | x6 ⇒ p | x7 ⇒ p
   | x8 ⇒ p | x9 ⇒ p | xA ⇒ p | xB ⇒ p | xC ⇒ p
   | xD ⇒ array_16T T e00 e01 e02 e03 e04 e05 e06 e07 e08 e09 e10 e11 e12 v e14 e15
   | xE ⇒ array_16T T e00 e01 e02 e03 e04 e05 e06 e07 e08 e09 e10 e11 e12 v v   e15
   | xF ⇒ array_16T T e00 e01 e02 e03 e04 e05 e06 e07 e08 e09 e10 e11 e12 v v   v ]
  | xE ⇒ match n with
   [ x0 ⇒ p | x1 ⇒ p | x2 ⇒ p | x3 ⇒ p | x4 ⇒ p | x5 ⇒ p | x6 ⇒ p | x7 ⇒ p
   | x8 ⇒ p | x9 ⇒ p | xA ⇒ p | xB ⇒ p | xC ⇒ p | xD ⇒ p
   | xE ⇒ array_16T T e00 e01 e02 e03 e04 e05 e06 e07 e08 e09 e10 e11 e12 e13 v e15
   | xF ⇒ array_16T T e00 e01 e02 e03 e04 e05 e06 e07 e08 e09 e10 e11 e12 e13 v v ]
  | xF ⇒ match n with
   [ x0 ⇒ p | x1 ⇒ p | x2 ⇒ p | x3 ⇒ p | x4 ⇒ p | x5 ⇒ p | x6 ⇒ p | x7 ⇒ p
   | x8 ⇒ p | x9 ⇒ p | xA ⇒ p | xB ⇒ p | xC ⇒ p | xD ⇒ p | xE ⇒ p
   | xF ⇒ array_16T T e00 e01 e02 e03 e04 e05 e06 e07 e08 e09 e10 e11 e12 e13 e14 v ]
  ]].

(* abbiamo gia' gli esadecimali come tipo induttivo quindi: *)
(* posso definire un setter composto [m+1,n-1] a matrice sull'array *)
(* NB: obbiettivo evitare l'overflow *)
definition setmn_array16T_succ_pred ≝
λm,n:exadecim.λT:Type.λp:Prod16T T.λv:T.
 match lt_ex m xF with
  [ true ⇒ match gt_ex n x0 with
   [ true ⇒ setmn_array16T (succ_ex m) (pred_ex n) T p v
   | false ⇒ p
   ]
  | false ⇒ p
  ].

(* abbiamo gia' gli esadecimali come tipo induttivo quindi: *)
(* posso definire un setter composto [m+1,F] a matrice sull'array *)
(* NB: obbiettivo evitare l'overflow *)
definition setmn_array16T_succ ≝
λm:exadecim.λT:Type.λp:Prod16T T.λv:T.
 match lt_ex m xF with
  [ true ⇒ setmn_array16T (succ_ex m) xF T p v
  | false ⇒ p
  ].

(* abbiamo gia' gli esadecimali come tipo induttivo quindi: *)
(* posso definire un setter composto [0,n-1] a matrice sull'array *)
(* NB: obbiettivo evitare l'overflow *)
definition setmn_array16T_pred ≝
λn:exadecim.λT:Type.λp:Prod16T T.λv:T.
 match gt_ex n x0 with
  [ true ⇒ setmn_array16T x0 (pred_ex n) T p v
  | false ⇒ p
  ].

(* ************************** *)
(* TIPO BYTE COME INSIEME BIT *)
(* ************************** *)

(* definizione di un byte come 8 bit *)
inductive Prod8T (T:Type) : Type ≝
array_8T : T → T → T → T → T → T → T → T →
           Prod8T T.

(* abbiamo gia' gli ottali come tipo induttivo quindi: *)
(* posso definire un getter a matrice sull'array *)
definition getn_array8T ≝
λn:oct.λT:Type.λp:Prod8T T.
 match p with 
  [ array_8T e07 e06 e05 e04 e03 e02 e01 e00 ⇒
 match n with
  [ o0 ⇒ e00 | o1 ⇒ e01 | o2 ⇒ e02 | o3 ⇒ e03 | o4 ⇒ e04 | o5 ⇒ e05 | o6 ⇒ e06 | o7 ⇒ e07 ]].

(* abbiamo gia' gli ottali come tipo induttivo quindi: *)
(* posso definire un setter a matrice sull'array *)
definition setn_array8T ≝
λn:oct.λT:Type.λp:Prod8T T.λv:T.
 match p with 
  [ array_8T e07 e06 e05 e04 e03 e02 e01 e00 ⇒
 match n with
  [ o0 ⇒ array_8T T e07 e06 e05 e04 e03 e02 e01 v
  | o1 ⇒ array_8T T e07 e06 e05 e04 e03 e02 v   e00
  | o2 ⇒ array_8T T e07 e06 e05 e04 e03 v   e01 e00
  | o3 ⇒ array_8T T e07 e06 e05 e04 v   e02 e01 e00
  | o4 ⇒ array_8T T e07 e06 e05 v   e03 e02 e01 e00
  | o5 ⇒ array_8T T e07 e06 v   e04 e03 e02 e01 e00
  | o6 ⇒ array_8T T e07 v   e05 e04 e03 e02 e01 e00
  | o7 ⇒ array_8T T v   e06 e05 e04 e03 e02 e01 e00
  ]].

(* lettura byte *)
definition byte8_of_bits ≝
λp:Prod8T bool.
 match p with 
  [ array_8T e07 e06 e05 e04 e03 e02 e01 e00 ⇒
   mk_byte8
   (or_ex (match e07 with [ true ⇒ x8 | false ⇒ x0 ])
   (or_ex (match e06 with [ true ⇒ x4 | false ⇒ x0 ])
   (or_ex (match e05 with [ true ⇒ x2 | false ⇒ x0 ])
          (match e04 with [ true ⇒ x1 | false ⇒ x0 ]))))
   (or_ex (match e03 with [ true ⇒ x8 | false ⇒ x0 ])
   (or_ex (match e02 with [ true ⇒ x4 | false ⇒ x0 ])
   (or_ex (match e01 with [ true ⇒ x2 | false ⇒ x0 ])
          (match e00 with [ true ⇒ x1 | false ⇒ x0 ])))) ].

(* scrittura byte *)
definition bits_of_byte8 ≝
λp:byte8.
 match b8h p with
  [ x0 ⇒ match b8l p with
   [ x0 ⇒ array_8T bool false false false false false false false false
   | x1 ⇒ array_8T bool false false false false false false false true
   | x2 ⇒ array_8T bool false false false false false false true  false
   | x3 ⇒ array_8T bool false false false false false false true  true
   | x4 ⇒ array_8T bool false false false false false true  false false
   | x5 ⇒ array_8T bool false false false false false true  false true
   | x6 ⇒ array_8T bool false false false false false true  true  false
   | x7 ⇒ array_8T bool false false false false false true  true  true
   | x8 ⇒ array_8T bool false false false false true  false false false
   | x9 ⇒ array_8T bool false false false false true  false false true
   | xA ⇒ array_8T bool false false false false true  false true  false
   | xB ⇒ array_8T bool false false false false true  false true  true
   | xC ⇒ array_8T bool false false false false true  true  false false
   | xD ⇒ array_8T bool false false false false true  true  false true
   | xE ⇒ array_8T bool false false false false true  true  true  false
   | xF ⇒ array_8T bool false false false false true  true  true  true ]
  | x1 ⇒ match b8l p with
   [ x0 ⇒ array_8T bool false false false true  false false false false
   | x1 ⇒ array_8T bool false false false true  false false false true
   | x2 ⇒ array_8T bool false false false true  false false true  false
   | x3 ⇒ array_8T bool false false false true  false false true  true
   | x4 ⇒ array_8T bool false false false true  false true  false false
   | x5 ⇒ array_8T bool false false false true  false true  false true
   | x6 ⇒ array_8T bool false false false true  false true  true  false
   | x7 ⇒ array_8T bool false false false true  false true  true  true
   | x8 ⇒ array_8T bool false false false true  true  false false false
   | x9 ⇒ array_8T bool false false false true  true  false false true
   | xA ⇒ array_8T bool false false false true  true  false true  false
   | xB ⇒ array_8T bool false false false true  true  false true  true
   | xC ⇒ array_8T bool false false false true  true  true  false false
   | xD ⇒ array_8T bool false false false true  true  true  false true
   | xE ⇒ array_8T bool false false false true  true  true  true  false
   | xF ⇒ array_8T bool false false false true  true  true  true  true ]
  | x2 ⇒ match b8l p with
   [ x0 ⇒ array_8T bool false false true  false false false false false
   | x1 ⇒ array_8T bool false false true  false false false false true
   | x2 ⇒ array_8T bool false false true  false false false true  false
   | x3 ⇒ array_8T bool false false true  false false false true  true
   | x4 ⇒ array_8T bool false false true  false false true  false false
   | x5 ⇒ array_8T bool false false true  false false true  false true
   | x6 ⇒ array_8T bool false false true  false false true  true  false
   | x7 ⇒ array_8T bool false false true  false false true  true  true
   | x8 ⇒ array_8T bool false false true  false true  false false false
   | x9 ⇒ array_8T bool false false true  false true  false false true
   | xA ⇒ array_8T bool false false true  false true  false true  false
   | xB ⇒ array_8T bool false false true  false true  false true  true
   | xC ⇒ array_8T bool false false true  false true  true  false false
   | xD ⇒ array_8T bool false false true  false true  true  false true
   | xE ⇒ array_8T bool false false true  false true  true  true  false
   | xF ⇒ array_8T bool false false true  false true  true  true  true ]
  | x3 ⇒ match b8l p with
   [ x0 ⇒ array_8T bool false false true  true  false false false false
   | x1 ⇒ array_8T bool false false true  true  false false false true
   | x2 ⇒ array_8T bool false false true  true  false false true  false
   | x3 ⇒ array_8T bool false false true  true  false false true  true
   | x4 ⇒ array_8T bool false false true  true  false true  false false
   | x5 ⇒ array_8T bool false false true  true  false true  false true
   | x6 ⇒ array_8T bool false false true  true  false true  true  false
   | x7 ⇒ array_8T bool false false true  true  false true  true  true
   | x8 ⇒ array_8T bool false false true  true  true  false false false
   | x9 ⇒ array_8T bool false false true  true  true  false false true
   | xA ⇒ array_8T bool false false true  true  true  false true  false
   | xB ⇒ array_8T bool false false true  true  true  false true  true
   | xC ⇒ array_8T bool false false true  true  true  true  false false
   | xD ⇒ array_8T bool false false true  true  true  true  false true
   | xE ⇒ array_8T bool false false true  true  true  true  true  false
   | xF ⇒ array_8T bool false false true  true  true  true  true  true ]
  | x4 ⇒ match b8l p with
   [ x0 ⇒ array_8T bool false true  false false false false false false
   | x1 ⇒ array_8T bool false true  false false false false false true
   | x2 ⇒ array_8T bool false true  false false false false true  false
   | x3 ⇒ array_8T bool false true  false false false false true  true
   | x4 ⇒ array_8T bool false true  false false false true  false false
   | x5 ⇒ array_8T bool false true  false false false true  false true
   | x6 ⇒ array_8T bool false true  false false false true  true  false
   | x7 ⇒ array_8T bool false true  false false false true  true  true
   | x8 ⇒ array_8T bool false true  false false true  false false false
   | x9 ⇒ array_8T bool false true  false false true  false false true
   | xA ⇒ array_8T bool false true  false false true  false true  false
   | xB ⇒ array_8T bool false true  false false true  false true  true
   | xC ⇒ array_8T bool false true  false false true  true  false false
   | xD ⇒ array_8T bool false true  false false true  true  false true
   | xE ⇒ array_8T bool false true  false false true  true  true  false
   | xF ⇒ array_8T bool false true  false false true  true  true  true ]
  | x5 ⇒ match b8l p with
   [ x0 ⇒ array_8T bool false true  false true  false false false false
   | x1 ⇒ array_8T bool false true  false true  false false false true
   | x2 ⇒ array_8T bool false true  false true  false false true  false
   | x3 ⇒ array_8T bool false true  false true  false false true  true
   | x4 ⇒ array_8T bool false true  false true  false true  false false
   | x5 ⇒ array_8T bool false true  false true  false true  false true
   | x6 ⇒ array_8T bool false true  false true  false true  true  false
   | x7 ⇒ array_8T bool false true  false true  false true  true  true
   | x8 ⇒ array_8T bool false true  false true  true  false false false
   | x9 ⇒ array_8T bool false true  false true  true  false false true
   | xA ⇒ array_8T bool false true  false true  true  false true  false
   | xB ⇒ array_8T bool false true  false true  true  false true  true
   | xC ⇒ array_8T bool false true  false true  true  true  false false
   | xD ⇒ array_8T bool false true  false true  true  true  false true
   | xE ⇒ array_8T bool false true  false true  true  true  true  false
   | xF ⇒ array_8T bool false true  false true  true  true  true  true ]
  | x6 ⇒ match b8l p with
   [ x0 ⇒ array_8T bool false true  true  false false false false false
   | x1 ⇒ array_8T bool false true  true  false false false false true
   | x2 ⇒ array_8T bool false true  true  false false false true  false
   | x3 ⇒ array_8T bool false true  true  false false false true  true
   | x4 ⇒ array_8T bool false true  true  false false true  false false
   | x5 ⇒ array_8T bool false true  true  false false true  false true
   | x6 ⇒ array_8T bool false true  true  false false true  true  false
   | x7 ⇒ array_8T bool false true  true  false false true  true  true
   | x8 ⇒ array_8T bool false true  true  false true  false false false
   | x9 ⇒ array_8T bool false true  true  false true  false false true
   | xA ⇒ array_8T bool false true  true  false true  false true  false
   | xB ⇒ array_8T bool false true  true  false true  false true  true
   | xC ⇒ array_8T bool false true  true  false true  true  false false
   | xD ⇒ array_8T bool false true  true  false true  true  false true
   | xE ⇒ array_8T bool false true  true  false true  true  true  false
   | xF ⇒ array_8T bool false true  true  false true  true  true  true ]
  | x7 ⇒ match b8l p with
   [ x0 ⇒ array_8T bool false true  true  true  false false false false
   | x1 ⇒ array_8T bool false true  true  true  false false false true
   | x2 ⇒ array_8T bool false true  true  true  false false true  false
   | x3 ⇒ array_8T bool false true  true  true  false false true  true
   | x4 ⇒ array_8T bool false true  true  true  false true  false false
   | x5 ⇒ array_8T bool false true  true  true  false true  false true
   | x6 ⇒ array_8T bool false true  true  true  false true  true  false
   | x7 ⇒ array_8T bool false true  true  true  false true  true  true
   | x8 ⇒ array_8T bool false true  true  true  true  false false false
   | x9 ⇒ array_8T bool false true  true  true  true  false false true
   | xA ⇒ array_8T bool false true  true  true  true  false true  false
   | xB ⇒ array_8T bool false true  true  true  true  false true  true
   | xC ⇒ array_8T bool false true  true  true  true  true  false false
   | xD ⇒ array_8T bool false true  true  true  true  true  false true
   | xE ⇒ array_8T bool false true  true  true  true  true  true  false
   | xF ⇒ array_8T bool false true  true  true  true  true  true  true ]
  | x8 ⇒ match b8l p with
   [ x0 ⇒ array_8T bool true  false false false false false false false
   | x1 ⇒ array_8T bool true  false false false false false false true
   | x2 ⇒ array_8T bool true  false false false false false true  false
   | x3 ⇒ array_8T bool true  false false false false false true  true
   | x4 ⇒ array_8T bool true  false false false false true  false false
   | x5 ⇒ array_8T bool true  false false false false true  false true
   | x6 ⇒ array_8T bool true  false false false false true  true  false
   | x7 ⇒ array_8T bool true  false false false false true  true  true
   | x8 ⇒ array_8T bool true  false false false true  false false false
   | x9 ⇒ array_8T bool true  false false false true  false false true
   | xA ⇒ array_8T bool true  false false false true  false true  false
   | xB ⇒ array_8T bool true  false false false true  false true  true
   | xC ⇒ array_8T bool true  false false false true  true  false false
   | xD ⇒ array_8T bool true  false false false true  true  false true
   | xE ⇒ array_8T bool true  false false false true  true  true  false
   | xF ⇒ array_8T bool true  false false false true  true  true  true ]
  | x9 ⇒ match b8l p with
   [ x0 ⇒ array_8T bool true  false false true  false false false false
   | x1 ⇒ array_8T bool true  false false true  false false false true
   | x2 ⇒ array_8T bool true  false false true  false false true  false
   | x3 ⇒ array_8T bool true  false false true  false false true  true
   | x4 ⇒ array_8T bool true  false false true  false true  false false
   | x5 ⇒ array_8T bool true  false false true  false true  false true
   | x6 ⇒ array_8T bool true  false false true  false true  true  false
   | x7 ⇒ array_8T bool true  false false true  false true  true  true
   | x8 ⇒ array_8T bool true  false false true  true  false false false
   | x9 ⇒ array_8T bool true  false false true  true  false false true
   | xA ⇒ array_8T bool true  false false true  true  false true  false
   | xB ⇒ array_8T bool true  false false true  true  false true  true
   | xC ⇒ array_8T bool true  false false true  true  true  false false
   | xD ⇒ array_8T bool true  false false true  true  true  false true
   | xE ⇒ array_8T bool true  false false true  true  true  true  false
   | xF ⇒ array_8T bool true  false false true  true  true  true  true ]
  | xA ⇒ match b8l p with
   [ x0 ⇒ array_8T bool true  false true  false false false false false
   | x1 ⇒ array_8T bool true  false true  false false false false true
   | x2 ⇒ array_8T bool true  false true  false false false true  false
   | x3 ⇒ array_8T bool true  false true  false false false true  true
   | x4 ⇒ array_8T bool true  false true  false false true  false false
   | x5 ⇒ array_8T bool true  false true  false false true  false true
   | x6 ⇒ array_8T bool true  false true  false false true  true  false
   | x7 ⇒ array_8T bool true  false true  false false true  true  true
   | x8 ⇒ array_8T bool true  false true  false true  false false false
   | x9 ⇒ array_8T bool true  false true  false true  false false true
   | xA ⇒ array_8T bool true  false true  false true  false true  false
   | xB ⇒ array_8T bool true  false true  false true  false true  true
   | xC ⇒ array_8T bool true  false true  false true  true  false false
   | xD ⇒ array_8T bool true  false true  false true  true  false true
   | xE ⇒ array_8T bool true  false true  false true  true  true  false
   | xF ⇒ array_8T bool true  false true  false true  true  true  true ]
  | xB ⇒ match b8l p with
   [ x0 ⇒ array_8T bool true  false true  true  false false false false
   | x1 ⇒ array_8T bool true  false true  true  false false false true
   | x2 ⇒ array_8T bool true  false true  true  false false true  false
   | x3 ⇒ array_8T bool true  false true  true  false false true  true
   | x4 ⇒ array_8T bool true  false true  true  false true  false false
   | x5 ⇒ array_8T bool true  false true  true  false true  false true
   | x6 ⇒ array_8T bool true  false true  true  false true  true  false
   | x7 ⇒ array_8T bool true  false true  true  false true  true  true
   | x8 ⇒ array_8T bool true  false true  true  true  false false false
   | x9 ⇒ array_8T bool true  false true  true  true  false false true
   | xA ⇒ array_8T bool true  false true  true  true  false true  false
   | xB ⇒ array_8T bool true  false true  true  true  false true  true
   | xC ⇒ array_8T bool true  false true  true  true  true  false false
   | xD ⇒ array_8T bool true  false true  true  true  true  false true
   | xE ⇒ array_8T bool true  false true  true  true  true  true  false
   | xF ⇒ array_8T bool true  false true  true  true  true  true  true ]
  | xC ⇒ match b8l p with
   [ x0 ⇒ array_8T bool true  true  false false false false false false
   | x1 ⇒ array_8T bool true  true  false false false false false true
   | x2 ⇒ array_8T bool true  true  false false false false true  false
   | x3 ⇒ array_8T bool true  true  false false false false true  true
   | x4 ⇒ array_8T bool true  true  false false false true  false false
   | x5 ⇒ array_8T bool true  true  false false false true  false true
   | x6 ⇒ array_8T bool true  true  false false false true  true  false
   | x7 ⇒ array_8T bool true  true  false false false true  true  true
   | x8 ⇒ array_8T bool true  true  false false true  false false false
   | x9 ⇒ array_8T bool true  true  false false true  false false true
   | xA ⇒ array_8T bool true  true  false false true  false true  false
   | xB ⇒ array_8T bool true  true  false false true  false true  true
   | xC ⇒ array_8T bool true  true  false false true  true  false false
   | xD ⇒ array_8T bool true  true  false false true  true  false true
   | xE ⇒ array_8T bool true  true  false false true  true  true  false
   | xF ⇒ array_8T bool true  true  false false true  true  true  true ]
  | xD ⇒ match b8l p with
   [ x0 ⇒ array_8T bool true  true  false true  false false false false
   | x1 ⇒ array_8T bool true  true  false true  false false false true
   | x2 ⇒ array_8T bool true  true  false true  false false true  false
   | x3 ⇒ array_8T bool true  true  false true  false false true  true
   | x4 ⇒ array_8T bool true  true  false true  false true  false false
   | x5 ⇒ array_8T bool true  true  false true  false true  false true
   | x6 ⇒ array_8T bool true  true  false true  false true  true  false
   | x7 ⇒ array_8T bool true  true  false true  false true  true  true
   | x8 ⇒ array_8T bool true  true  false true  true  false false false
   | x9 ⇒ array_8T bool true  true  false true  true  false false true
   | xA ⇒ array_8T bool true  true  false true  true  false true  false
   | xB ⇒ array_8T bool true  true  false true  true  false true  true
   | xC ⇒ array_8T bool true  true  false true  true  true  false false
   | xD ⇒ array_8T bool true  true  false true  true  true  false true
   | xE ⇒ array_8T bool true  true  false true  true  true  true  false
   | xF ⇒ array_8T bool true  true  false true  true  true  true  true ]
  | xE ⇒ match b8l p with
   [ x0 ⇒ array_8T bool true  true  true  false false false false false
   | x1 ⇒ array_8T bool true  true  true  false false false false true
   | x2 ⇒ array_8T bool true  true  true  false false false true  false
   | x3 ⇒ array_8T bool true  true  true  false false false true  true
   | x4 ⇒ array_8T bool true  true  true  false false true  false false
   | x5 ⇒ array_8T bool true  true  true  false false true  false true
   | x6 ⇒ array_8T bool true  true  true  false false true  true  false
   | x7 ⇒ array_8T bool true  true  true  false false true  true  true
   | x8 ⇒ array_8T bool true  true  true  false true  false false false
   | x9 ⇒ array_8T bool true  true  true  false true  false false true
   | xA ⇒ array_8T bool true  true  true  false true  false true  false
   | xB ⇒ array_8T bool true  true  true  false true  false true  true
   | xC ⇒ array_8T bool true  true  true  false true  true  false false
   | xD ⇒ array_8T bool true  true  true  false true  true  false true
   | xE ⇒ array_8T bool true  true  true  false true  true  true  false
   | xF ⇒ array_8T bool true  true  true  false true  true  true  true ]
  | xF ⇒ match b8l p with
   [ x0 ⇒ array_8T bool true  true  true  true  false false false false
   | x1 ⇒ array_8T bool true  true  true  true  false false false true
   | x2 ⇒ array_8T bool true  true  true  true  false false true  false
   | x3 ⇒ array_8T bool true  true  true  true  false false true  true
   | x4 ⇒ array_8T bool true  true  true  true  false true  false false
   | x5 ⇒ array_8T bool true  true  true  true  false true  false true
   | x6 ⇒ array_8T bool true  true  true  true  false true  true  false
   | x7 ⇒ array_8T bool true  true  true  true  false true  true  true
   | x8 ⇒ array_8T bool true  true  true  true  true  false false false
   | x9 ⇒ array_8T bool true  true  true  true  true  false false true
   | xA ⇒ array_8T bool true  true  true  true  true  false true  false
   | xB ⇒ array_8T bool true  true  true  true  true  false true  true
   | xC ⇒ array_8T bool true  true  true  true  true  true  false false
   | xD ⇒ array_8T bool true  true  true  true  true  true  false true
   | xE ⇒ array_8T bool true  true  true  true  true  true  true  false
   | xF ⇒ array_8T bool true  true  true  true  true  true  true  true ]
  ].

(* ********************** *)
(* TEOREMI/LEMMMI/ASSIOMI *)
(* ********************** *)

(* check *)
lemma ok_byte8_of_bits_bits_of_byte8 :
 ∀b.
  byte8_of_bits (bits_of_byte8 b) = b.
 intros;
 elim b; elim e; elim e1;
 reflexivity.
qed.

(* check *)
lemma ok_bits_of_byte8_byte8_of_bits :
 ∀b7,b6,b5,b4,b3,b2,b1,b0.
  bits_of_byte8 (byte8_of_bits (array_8T bool b7 b6 b5 b4 b3 b2 b1 b0))
  = array_8T bool b7 b6 b5 b4 b3 b2 b1 b0.
 intros;
 elim b0; elim b1; elim b2; elim b3; elim b4; elim b5; elim b6; elim b7;
 reflexivity.
qed.

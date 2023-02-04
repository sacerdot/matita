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
(*                          Progetto FreeScale                            *)
(*                                                                        *)
(*   Sviluppato da: Ing. Cosimo Oliboni, oliboni@cs.unibo.it              *)
(*   Sviluppo: 2008-2010                                                  *)
(*                                                                        *)
(* ********************************************************************** *)

include "num/oct.ma".
include "num/byte8.ma".

(* **************************** *)
(* TIPI PER I MODULI DI MEMORIA *)
(* **************************** *)

(* tipi di memoria:RAM/ROM/non installata *)
ninductive memory_type : Type ≝
  MEM_READ_ONLY: memory_type
| MEM_READ_WRITE: memory_type
| MEM_OUT_OF_BOUND: memory_type.

(* **************** *)
(* TIPO ARRAY DA 16 *)
(* **************** *)

(* definizione di un array omogeneo di dimensione 16 *)
nrecord Array16T (T:Type) : Type ≝
{ a16_1  : T ; a16_2  : T ; a16_3  : T ; a16_4  : T
; a16_5  : T ; a16_6  : T ; a16_7  : T ; a16_8  : T
; a16_9  : T ; a16_10 : T ; a16_11 : T ; a16_12 : T
; a16_13 : T ; a16_14 : T ; a16_15 : T ; a16_16 : T }.

(* operatore uguaglianza *)
ndefinition eq_ar16 ≝
λT.λf:T → T → bool.λa1,a2:Array16T T.
 (f (a16_1 ? a1) (a16_1 ? a2)) ⊗ (f (a16_2 ? a1) (a16_2 ? a2)) ⊗
 (f (a16_3 ? a1) (a16_3 ? a2)) ⊗ (f (a16_4 ? a1) (a16_4 ? a2)) ⊗
 (f (a16_5 ? a1) (a16_5 ? a2)) ⊗ (f (a16_6 ? a1) (a16_6 ? a2)) ⊗
 (f (a16_7 ? a1) (a16_7 ? a2)) ⊗ (f (a16_8 ? a1) (a16_8 ? a2)) ⊗
 (f (a16_9 ? a1) (a16_9 ? a2)) ⊗ (f (a16_10 ? a1) (a16_10 ? a2)) ⊗
 (f (a16_11 ? a1) (a16_11 ? a2)) ⊗ (f (a16_12 ? a1) (a16_12 ? a2)) ⊗
 (f (a16_13 ? a1) (a16_13 ? a2)) ⊗ (f (a16_14 ? a1) (a16_14 ? a2)) ⊗
 (f (a16_15 ? a1) (a16_15 ? a2)) ⊗ (f (a16_16 ? a1) (a16_16 ? a2)).

(* abbiamo gia' gli esadecimali come tipo induttivo quindi: *)
(* posso definire un getter a matrice sull'array *)

ndefinition getn_array16T ≝
λn:exadecim.λT:Type.λp:Array16T T.
 match n return λn.(Array16T T) → T with
  [ x0 ⇒ a16_1  T | x1 ⇒ a16_2  T | x2 ⇒ a16_3  T | x3 ⇒ a16_4  T
  | x4 ⇒ a16_5  T | x5 ⇒ a16_6  T | x6 ⇒ a16_7  T | x7 ⇒ a16_8  T
  | x8 ⇒ a16_9  T | x9 ⇒ a16_10 T | xA ⇒ a16_11 T | xB ⇒ a16_12 T
  | xC ⇒ a16_13 T | xD ⇒ a16_14 T | xE ⇒ a16_15 T | xF ⇒ a16_16 T
  ] p.

(* abbiamo gia' gli esadecimali come tipo induttivo quindi: *)
(* posso definire un setter a matrice sull'array *)
ndefinition setn_array16T ≝
λn:exadecim.λT:Type.λp:Array16T T.λv:T.
let e00 ≝ (a16_1 T p) in
let e01 ≝ (a16_2 T p) in
let e02 ≝ (a16_3 T p) in
let e03 ≝ (a16_4 T p) in
let e04 ≝ (a16_5 T p) in
let e05 ≝ (a16_6 T p) in
let e06 ≝ (a16_7 T p) in
let e07 ≝ (a16_8 T p) in
let e08 ≝ (a16_9 T p) in
let e09 ≝ (a16_10 T p) in
let e10 ≝ (a16_11 T p) in
let e11 ≝ (a16_12 T p) in
let e12 ≝ (a16_13 T p) in
let e13 ≝ (a16_14 T p) in
let e14 ≝ (a16_15 T p) in
let e15 ≝ (a16_16 T p) in
 match n with
  [ x0 ⇒ mk_Array16T T v   e01 e02 e03 e04 e05 e06 e07 e08 e09 e10 e11 e12 e13 e14 e15
  | x1 ⇒ mk_Array16T T e00 v   e02 e03 e04 e05 e06 e07 e08 e09 e10 e11 e12 e13 e14 e15
  | x2 ⇒ mk_Array16T T e00 e01 v   e03 e04 e05 e06 e07 e08 e09 e10 e11 e12 e13 e14 e15
  | x3 ⇒ mk_Array16T T e00 e01 e02 v   e04 e05 e06 e07 e08 e09 e10 e11 e12 e13 e14 e15
  | x4 ⇒ mk_Array16T T e00 e01 e02 e03 v   e05 e06 e07 e08 e09 e10 e11 e12 e13 e14 e15
  | x5 ⇒ mk_Array16T T e00 e01 e02 e03 e04 v   e06 e07 e08 e09 e10 e11 e12 e13 e14 e15
  | x6 ⇒ mk_Array16T T e00 e01 e02 e03 e04 e05 v   e07 e08 e09 e10 e11 e12 e13 e14 e15
  | x7 ⇒ mk_Array16T T e00 e01 e02 e03 e04 e05 e06 v   e08 e09 e10 e11 e12 e13 e14 e15
  | x8 ⇒ mk_Array16T T e00 e01 e02 e03 e04 e05 e06 e07 v   e09 e10 e11 e12 e13 e14 e15
  | x9 ⇒ mk_Array16T T e00 e01 e02 e03 e04 e05 e06 e07 e08 v   e10 e11 e12 e13 e14 e15
  | xA ⇒ mk_Array16T T e00 e01 e02 e03 e04 e05 e06 e07 e08 e09 v   e11 e12 e13 e14 e15
  | xB ⇒ mk_Array16T T e00 e01 e02 e03 e04 e05 e06 e07 e08 e09 e10 v   e12 e13 e14 e15
  | xC ⇒ mk_Array16T T e00 e01 e02 e03 e04 e05 e06 e07 e08 e09 e10 e11 v   e13 e14 e15
  | xD ⇒ mk_Array16T T e00 e01 e02 e03 e04 e05 e06 e07 e08 e09 e10 e11 e12 v   e14 e15
  | xE ⇒ mk_Array16T T e00 e01 e02 e03 e04 e05 e06 e07 e08 e09 e10 e11 e12 e13 v   e15
  | xF ⇒ mk_Array16T T e00 e01 e02 e03 e04 e05 e06 e07 e08 e09 e10 e11 e12 e13 e14 v
  ].

(* abbiamo gia' gli esadecimali come tipo induttivo quindi: *)
(* posso definire un setter multiplo [m,n] a matrice sull'array *)
(* m ≤ n *)
ndefinition setmn_array16T ≝
λm,n:exadecim.λT:Type.λp:Array16T T.λv:T.
let e00 ≝ (a16_1 T p) in
let e01 ≝ (a16_2 T p) in
let e02 ≝ (a16_3 T p) in
let e03 ≝ (a16_4 T p) in
let e04 ≝ (a16_5 T p) in
let e05 ≝ (a16_6 T p) in
let e06 ≝ (a16_7 T p) in
let e07 ≝ (a16_8 T p) in
let e08 ≝ (a16_9 T p) in
let e09 ≝ (a16_10 T p) in
let e10 ≝ (a16_11 T p) in
let e11 ≝ (a16_12 T p) in
let e12 ≝ (a16_13 T p) in
let e13 ≝ (a16_14 T p) in
let e14 ≝ (a16_15 T p) in
let e15 ≝ (a16_16 T p) in
 match m with
  [ x0 ⇒ match n with
   [ x0 ⇒ mk_Array16T T v e01 e02 e03 e04 e05 e06 e07 e08 e09 e10 e11 e12 e13 e14 e15
   | x1 ⇒ mk_Array16T T v v   e02 e03 e04 e05 e06 e07 e08 e09 e10 e11 e12 e13 e14 e15
   | x2 ⇒ mk_Array16T T v v   v   e03 e04 e05 e06 e07 e08 e09 e10 e11 e12 e13 e14 e15
   | x3 ⇒ mk_Array16T T v v   v   v   e04 e05 e06 e07 e08 e09 e10 e11 e12 e13 e14 e15
   | x4 ⇒ mk_Array16T T v v   v   v   v   e05 e06 e07 e08 e09 e10 e11 e12 e13 e14 e15
   | x5 ⇒ mk_Array16T T v v   v   v   v   v   e06 e07 e08 e09 e10 e11 e12 e13 e14 e15
   | x6 ⇒ mk_Array16T T v v   v   v   v   v   v   e07 e08 e09 e10 e11 e12 e13 e14 e15
   | x7 ⇒ mk_Array16T T v v   v   v   v   v   v   v   e08 e09 e10 e11 e12 e13 e14 e15
   | x8 ⇒ mk_Array16T T v v   v   v   v   v   v   v   v   e09 e10 e11 e12 e13 e14 e15
   | x9 ⇒ mk_Array16T T v v   v   v   v   v   v   v   v   v   e10 e11 e12 e13 e14 e15
   | xA ⇒ mk_Array16T T v v   v   v   v   v   v   v   v   v   v   e11 e12 e13 e14 e15
   | xB ⇒ mk_Array16T T v v   v   v   v   v   v   v   v   v   v   v   e12 e13 e14 e15
   | xC ⇒ mk_Array16T T v v   v   v   v   v   v   v   v   v   v   v   v   e13 e14 e15
   | xD ⇒ mk_Array16T T v v   v   v   v   v   v   v   v   v   v   v   v   v   e14 e15
   | xE ⇒ mk_Array16T T v v   v   v   v   v   v   v   v   v   v   v   v   v   v   e15
   | xF ⇒ mk_Array16T T v v   v   v   v   v   v   v   v   v   v   v   v   v   v   v ]
  | x1 ⇒ match n with
   [ x0 ⇒ p
   | x1 ⇒ mk_Array16T T e00 v e02 e03 e04 e05 e06 e07 e08 e09 e10 e11 e12 e13 e14 e15
   | x2 ⇒ mk_Array16T T e00 v v   e03 e04 e05 e06 e07 e08 e09 e10 e11 e12 e13 e14 e15
   | x3 ⇒ mk_Array16T T e00 v v   v   e04 e05 e06 e07 e08 e09 e10 e11 e12 e13 e14 e15
   | x4 ⇒ mk_Array16T T e00 v v   v   v   e05 e06 e07 e08 e09 e10 e11 e12 e13 e14 e15
   | x5 ⇒ mk_Array16T T e00 v v   v   v   v   e06 e07 e08 e09 e10 e11 e12 e13 e14 e15
   | x6 ⇒ mk_Array16T T e00 v v   v   v   v   v   e07 e08 e09 e10 e11 e12 e13 e14 e15
   | x7 ⇒ mk_Array16T T e00 v v   v   v   v   v   v   e08 e09 e10 e11 e12 e13 e14 e15
   | x8 ⇒ mk_Array16T T e00 v v   v   v   v   v   v   v   e09 e10 e11 e12 e13 e14 e15
   | x9 ⇒ mk_Array16T T e00 v v   v   v   v   v   v   v   v   e10 e11 e12 e13 e14 e15
   | xA ⇒ mk_Array16T T e00 v v   v   v   v   v   v   v   v   v   e11 e12 e13 e14 e15
   | xB ⇒ mk_Array16T T e00 v v   v   v   v   v   v   v   v   v   v   e12 e13 e14 e15
   | xC ⇒ mk_Array16T T e00 v v   v   v   v   v   v   v   v   v   v   v   e13 e14 e15
   | xD ⇒ mk_Array16T T e00 v v   v   v   v   v   v   v   v   v   v   v   v   e14 e15
   | xE ⇒ mk_Array16T T e00 v v   v   v   v   v   v   v   v   v   v   v   v   v   e15
   | xF ⇒ mk_Array16T T e00 v v   v   v   v   v   v   v   v   v   v   v   v   v   v ]
  | x2 ⇒ match n with
   [ x0 ⇒ p | x1 ⇒ p
   | x2 ⇒ mk_Array16T T e00 e01 v e03 e04 e05 e06 e07 e08 e09 e10 e11 e12 e13 e14 e15
   | x3 ⇒ mk_Array16T T e00 e01 v v   e04 e05 e06 e07 e08 e09 e10 e11 e12 e13 e14 e15
   | x4 ⇒ mk_Array16T T e00 e01 v v   v   e05 e06 e07 e08 e09 e10 e11 e12 e13 e14 e15
   | x5 ⇒ mk_Array16T T e00 e01 v v   v   v   e06 e07 e08 e09 e10 e11 e12 e13 e14 e15
   | x6 ⇒ mk_Array16T T e00 e01 v v   v   v   v   e07 e08 e09 e10 e11 e12 e13 e14 e15
   | x7 ⇒ mk_Array16T T e00 e01 v v   v   v   v   v   e08 e09 e10 e11 e12 e13 e14 e15
   | x8 ⇒ mk_Array16T T e00 e01 v v   v   v   v   v   v   e09 e10 e11 e12 e13 e14 e15
   | x9 ⇒ mk_Array16T T e00 e01 v v   v   v   v   v   v   v   e10 e11 e12 e13 e14 e15
   | xA ⇒ mk_Array16T T e00 e01 v v   v   v   v   v   v   v   v   e11 e12 e13 e14 e15
   | xB ⇒ mk_Array16T T e00 e01 v v   v   v   v   v   v   v   v   v   e12 e13 e14 e15
   | xC ⇒ mk_Array16T T e00 e01 v v   v   v   v   v   v   v   v   v   v   e13 e14 e15
   | xD ⇒ mk_Array16T T e00 e01 v v   v   v   v   v   v   v   v   v   v   v   e14 e15
   | xE ⇒ mk_Array16T T e00 e01 v v   v   v   v   v   v   v   v   v   v   v   v   e15
   | xF ⇒ mk_Array16T T e00 e01 v v   v   v   v   v   v   v   v   v   v   v   v   v ]
  | x3 ⇒ match n with
   [ x0 ⇒ p | x1 ⇒ p | x2 ⇒ p
   | x3 ⇒ mk_Array16T T e00 e01 e02 v e04 e05 e06 e07 e08 e09 e10 e11 e12 e13 e14 e15
   | x4 ⇒ mk_Array16T T e00 e01 e02 v v   e05 e06 e07 e08 e09 e10 e11 e12 e13 e14 e15
   | x5 ⇒ mk_Array16T T e00 e01 e02 v v   v   e06 e07 e08 e09 e10 e11 e12 e13 e14 e15
   | x6 ⇒ mk_Array16T T e00 e01 e02 v v   v   v   e07 e08 e09 e10 e11 e12 e13 e14 e15
   | x7 ⇒ mk_Array16T T e00 e01 e02 v v   v   v   v   e08 e09 e10 e11 e12 e13 e14 e15
   | x8 ⇒ mk_Array16T T e00 e01 e02 v v   v   v   v   v   e09 e10 e11 e12 e13 e14 e15
   | x9 ⇒ mk_Array16T T e00 e01 e02 v v   v   v   v   v   v   e10 e11 e12 e13 e14 e15
   | xA ⇒ mk_Array16T T e00 e01 e02 v v   v   v   v   v   v   v   e11 e12 e13 e14 e15
   | xB ⇒ mk_Array16T T e00 e01 e02 v v   v   v   v   v   v   v   v   e12 e13 e14 e15
   | xC ⇒ mk_Array16T T e00 e01 e02 v v   v   v   v   v   v   v   v   v   e13 e14 e15
   | xD ⇒ mk_Array16T T e00 e01 e02 v v   v   v   v   v   v   v   v   v   v   e14 e15
   | xE ⇒ mk_Array16T T e00 e01 e02 v v   v   v   v   v   v   v   v   v   v   v   e15
   | xF ⇒ mk_Array16T T e00 e01 e02 v v   v   v   v   v   v   v   v   v   v   v   v ]
  | x4 ⇒ match n with
   [ x0 ⇒ p | x1 ⇒ p | x2 ⇒ p | x3 ⇒ p
   | x4 ⇒ mk_Array16T T e00 e01 e02 e03 v e05 e06 e07 e08 e09 e10 e11 e12 e13 e14 e15
   | x5 ⇒ mk_Array16T T e00 e01 e02 e03 v v   e06 e07 e08 e09 e10 e11 e12 e13 e14 e15
   | x6 ⇒ mk_Array16T T e00 e01 e02 e03 v v   v   e07 e08 e09 e10 e11 e12 e13 e14 e15
   | x7 ⇒ mk_Array16T T e00 e01 e02 e03 v v   v   v   e08 e09 e10 e11 e12 e13 e14 e15
   | x8 ⇒ mk_Array16T T e00 e01 e02 e03 v v   v   v   v   e09 e10 e11 e12 e13 e14 e15
   | x9 ⇒ mk_Array16T T e00 e01 e02 e03 v v   v   v   v   v   e10 e11 e12 e13 e14 e15
   | xA ⇒ mk_Array16T T e00 e01 e02 e03 v v   v   v   v   v   v   e11 e12 e13 e14 e15
   | xB ⇒ mk_Array16T T e00 e01 e02 e03 v v   v   v   v   v   v   v   e12 e13 e14 e15
   | xC ⇒ mk_Array16T T e00 e01 e02 e03 v v   v   v   v   v   v   v   v   e13 e14 e15
   | xD ⇒ mk_Array16T T e00 e01 e02 e03 v v   v   v   v   v   v   v   v   v   e14 e15
   | xE ⇒ mk_Array16T T e00 e01 e02 e03 v v   v   v   v   v   v   v   v   v   v   e15
   | xF ⇒ mk_Array16T T e00 e01 e02 e03 v v   v   v   v   v   v   v   v   v   v   v ]
  | x5 ⇒ match n with
   [ x0 ⇒ p | x1 ⇒ p | x2 ⇒ p | x3 ⇒ p | x4 ⇒ p
   | x5 ⇒ mk_Array16T T e00 e01 e02 e03 e04 v e06 e07 e08 e09 e10 e11 e12 e13 e14 e15
   | x6 ⇒ mk_Array16T T e00 e01 e02 e03 e04 v v   e07 e08 e09 e10 e11 e12 e13 e14 e15
   | x7 ⇒ mk_Array16T T e00 e01 e02 e03 e04 v v   v   e08 e09 e10 e11 e12 e13 e14 e15
   | x8 ⇒ mk_Array16T T e00 e01 e02 e03 e04 v v   v   v   e09 e10 e11 e12 e13 e14 e15
   | x9 ⇒ mk_Array16T T e00 e01 e02 e03 e04 v v   v   v   v   e10 e11 e12 e13 e14 e15
   | xA ⇒ mk_Array16T T e00 e01 e02 e03 e04 v v   v   v   v   v   e11 e12 e13 e14 e15
   | xB ⇒ mk_Array16T T e00 e01 e02 e03 e04 v v   v   v   v   v   v   e12 e13 e14 e15
   | xC ⇒ mk_Array16T T e00 e01 e02 e03 e04 v v   v   v   v   v   v   v   e13 e14 e15
   | xD ⇒ mk_Array16T T e00 e01 e02 e03 e04 v v   v   v   v   v   v   v   v   e14 e15
   | xE ⇒ mk_Array16T T e00 e01 e02 e03 e04 v v   v   v   v   v   v   v   v   v   e15
   | xF ⇒ mk_Array16T T e00 e01 e02 e03 e04 v v   v   v   v   v   v   v   v   v   v ]
  | x6 ⇒ match n with
   [ x0 ⇒ p | x1 ⇒ p | x2 ⇒ p | x3 ⇒ p | x4 ⇒ p | x5 ⇒ p
   | x6 ⇒ mk_Array16T T e00 e01 e02 e03 e04 e05 v e07 e08 e09 e10 e11 e12 e13 e14 e15
   | x7 ⇒ mk_Array16T T e00 e01 e02 e03 e04 e05 v v   e08 e09 e10 e11 e12 e13 e14 e15
   | x8 ⇒ mk_Array16T T e00 e01 e02 e03 e04 e05 v v   v   e09 e10 e11 e12 e13 e14 e15
   | x9 ⇒ mk_Array16T T e00 e01 e02 e03 e04 e05 v v   v   v   e10 e11 e12 e13 e14 e15
   | xA ⇒ mk_Array16T T e00 e01 e02 e03 e04 e05 v v   v   v   v   e11 e12 e13 e14 e15
   | xB ⇒ mk_Array16T T e00 e01 e02 e03 e04 e05 v v   v   v   v   v   e12 e13 e14 e15
   | xC ⇒ mk_Array16T T e00 e01 e02 e03 e04 e05 v v   v   v   v   v   v   e13 e14 e15
   | xD ⇒ mk_Array16T T e00 e01 e02 e03 e04 e05 v v   v   v   v   v   v   v   e14 e15
   | xE ⇒ mk_Array16T T e00 e01 e02 e03 e04 e05 v v   v   v   v   v   v   v   v   e15
   | xF ⇒ mk_Array16T T e00 e01 e02 e03 e04 e05 v v   v   v   v   v   v   v   v   v ]
  | x7 ⇒ match n with
   [ x0 ⇒ p | x1 ⇒ p | x2 ⇒ p | x3 ⇒ p | x4 ⇒ p | x5 ⇒ p | x6 ⇒ p
   | x7 ⇒ mk_Array16T T e00 e01 e02 e03 e04 e05 e06 v e08 e09 e10 e11 e12 e13 e14 e15
   | x8 ⇒ mk_Array16T T e00 e01 e02 e03 e04 e05 e06 v v   e09 e10 e11 e12 e13 e14 e15
   | x9 ⇒ mk_Array16T T e00 e01 e02 e03 e04 e05 e06 v v   v   e10 e11 e12 e13 e14 e15
   | xA ⇒ mk_Array16T T e00 e01 e02 e03 e04 e05 e06 v v   v   v   e11 e12 e13 e14 e15
   | xB ⇒ mk_Array16T T e00 e01 e02 e03 e04 e05 e06 v v   v   v   v   e12 e13 e14 e15
   | xC ⇒ mk_Array16T T e00 e01 e02 e03 e04 e05 e06 v v   v   v   v   v   e13 e14 e15
   | xD ⇒ mk_Array16T T e00 e01 e02 e03 e04 e05 e06 v v   v   v   v   v   v   e14 e15
   | xE ⇒ mk_Array16T T e00 e01 e02 e03 e04 e05 e06 v v   v   v   v   v   v   v   e15
   | xF ⇒ mk_Array16T T e00 e01 e02 e03 e04 e05 e06 v v   v   v   v   v   v   v   v ]
  | x8 ⇒ match n with
   [ x0 ⇒ p | x1 ⇒ p | x2 ⇒ p | x3 ⇒ p | x4 ⇒ p | x5 ⇒ p | x6 ⇒ p | x7 ⇒ p
   | x8 ⇒ mk_Array16T T e00 e01 e02 e03 e04 e05 e06 e07 v e09 e10 e11 e12 e13 e14 e15
   | x9 ⇒ mk_Array16T T e00 e01 e02 e03 e04 e05 e06 e07 v v   e10 e11 e12 e13 e14 e15
   | xA ⇒ mk_Array16T T e00 e01 e02 e03 e04 e05 e06 e07 v v   v   e11 e12 e13 e14 e15
   | xB ⇒ mk_Array16T T e00 e01 e02 e03 e04 e05 e06 e07 v v   v   v   e12 e13 e14 e15
   | xC ⇒ mk_Array16T T e00 e01 e02 e03 e04 e05 e06 e07 v v   v   v   v   e13 e14 e15
   | xD ⇒ mk_Array16T T e00 e01 e02 e03 e04 e05 e06 e07 v v   v   v   v   v   e14 e15
   | xE ⇒ mk_Array16T T e00 e01 e02 e03 e04 e05 e06 e07 v v   v   v   v   v   v   e15
   | xF ⇒ mk_Array16T T e00 e01 e02 e03 e04 e05 e06 e07 v v   v   v   v   v   v   v ]
  | x9 ⇒ match n with
   [ x0 ⇒ p | x1 ⇒ p | x2 ⇒ p  | x3 ⇒ p | x4 ⇒ p | x5 ⇒ p | x6 ⇒ p | x7 ⇒ p
   | x8 ⇒ p
   | x9 ⇒ mk_Array16T T e00 e01 e02 e03 e04 e05 e06 e07 e08 v e10 e11 e12 e13 e14 e15
   | xA ⇒ mk_Array16T T e00 e01 e02 e03 e04 e05 e06 e07 e08 v v   e11 e12 e13 e14 e15
   | xB ⇒ mk_Array16T T e00 e01 e02 e03 e04 e05 e06 e07 e08 v v   v   e12 e13 e14 e15
   | xC ⇒ mk_Array16T T e00 e01 e02 e03 e04 e05 e06 e07 e08 v v   v   v   e13 e14 e15
   | xD ⇒ mk_Array16T T e00 e01 e02 e03 e04 e05 e06 e07 e08 v v   v   v   v   e14 e15
   | xE ⇒ mk_Array16T T e00 e01 e02 e03 e04 e05 e06 e07 e08 v v   v   v   v   v   e15
   | xF ⇒ mk_Array16T T e00 e01 e02 e03 e04 e05 e06 e07 e08 v v   v   v   v   v   v ]
  | xA ⇒ match n with
   [ x0 ⇒ p | x1 ⇒ p | x2 ⇒ p | x3 ⇒ p | x4 ⇒ p | x5 ⇒ p | x6 ⇒ p | x7 ⇒ p
   | x8 ⇒ p | x9 ⇒ p
   | xA ⇒ mk_Array16T T e00 e01 e02 e03 e04 e05 e06 e07 e08 e09 v e11 e12 e13 e14 e15
   | xB ⇒ mk_Array16T T e00 e01 e02 e03 e04 e05 e06 e07 e08 e09 v v   e12 e13 e14 e15
   | xC ⇒ mk_Array16T T e00 e01 e02 e03 e04 e05 e06 e07 e08 e09 v v   v   e13 e14 e15
   | xD ⇒ mk_Array16T T e00 e01 e02 e03 e04 e05 e06 e07 e08 e09 v v   v   v   e14 e15
   | xE ⇒ mk_Array16T T e00 e01 e02 e03 e04 e05 e06 e07 e08 e09 v v   v   v   v   e15
   | xF ⇒ mk_Array16T T e00 e01 e02 e03 e04 e05 e06 e07 e08 e09 v v   v   v   v   v ]
  | xB ⇒ match n with
   [ x0 ⇒ p | x1 ⇒ p | x2 ⇒ p | x3 ⇒ p | x4 ⇒ p | x5 ⇒ p | x6 ⇒ p | x7 ⇒ p
   | x8 ⇒ p | x9 ⇒ p | xA ⇒ p
   | xB ⇒ mk_Array16T T e00 e01 e02 e03 e04 e05 e06 e07 e08 e09 e10 v e12 e13 e14 e15
   | xC ⇒ mk_Array16T T e00 e01 e02 e03 e04 e05 e06 e07 e08 e09 e10 v v   e13 e14 e15
   | xD ⇒ mk_Array16T T e00 e01 e02 e03 e04 e05 e06 e07 e08 e09 e10 v v   v   e14 e15
   | xE ⇒ mk_Array16T T e00 e01 e02 e03 e04 e05 e06 e07 e08 e09 e10 v v   v   v   e15
   | xF ⇒ mk_Array16T T e00 e01 e02 e03 e04 e05 e06 e07 e08 e09 e10 v v   v   v   v ]
  | xC ⇒ match n with
   [ x0 ⇒ p | x1 ⇒ p | x2 ⇒ p | x3 ⇒ p | x4 ⇒ p | x5 ⇒ p | x6 ⇒ p | x7 ⇒ p
   | x8 ⇒ p | x9 ⇒ p | xA ⇒ p | xB ⇒ p
   | xC ⇒ mk_Array16T T e00 e01 e02 e03 e04 e05 e06 e07 e08 e09 e10 e11 v e13 e14 e15
   | xD ⇒ mk_Array16T T e00 e01 e02 e03 e04 e05 e06 e07 e08 e09 e10 e11 v v   e14 e15
   | xE ⇒ mk_Array16T T e00 e01 e02 e03 e04 e05 e06 e07 e08 e09 e10 e11 v v   v   e15
   | xF ⇒ mk_Array16T T e00 e01 e02 e03 e04 e05 e06 e07 e08 e09 e10 e11 v v   v   v ]
  | xD ⇒ match n with
   [ x0 ⇒ p | x1 ⇒ p | x2 ⇒ p | x3 ⇒ p | x4 ⇒ p | x5 ⇒ p | x6 ⇒ p | x7 ⇒ p
   | x8 ⇒ p | x9 ⇒ p | xA ⇒ p | xB ⇒ p | xC ⇒ p
   | xD ⇒ mk_Array16T T e00 e01 e02 e03 e04 e05 e06 e07 e08 e09 e10 e11 e12 v e14 e15
   | xE ⇒ mk_Array16T T e00 e01 e02 e03 e04 e05 e06 e07 e08 e09 e10 e11 e12 v v   e15
   | xF ⇒ mk_Array16T T e00 e01 e02 e03 e04 e05 e06 e07 e08 e09 e10 e11 e12 v v   v ]
  | xE ⇒ match n with
   [ x0 ⇒ p | x1 ⇒ p | x2 ⇒ p | x3 ⇒ p | x4 ⇒ p | x5 ⇒ p | x6 ⇒ p | x7 ⇒ p
   | x8 ⇒ p | x9 ⇒ p | xA ⇒ p | xB ⇒ p | xC ⇒ p | xD ⇒ p
   | xE ⇒ mk_Array16T T e00 e01 e02 e03 e04 e05 e06 e07 e08 e09 e10 e11 e12 e13 v e15
   | xF ⇒ mk_Array16T T e00 e01 e02 e03 e04 e05 e06 e07 e08 e09 e10 e11 e12 e13 v v ]
  | xF ⇒ match n with
   [ x0 ⇒ p | x1 ⇒ p | x2 ⇒ p | x3 ⇒ p | x4 ⇒ p | x5 ⇒ p | x6 ⇒ p | x7 ⇒ p
   | x8 ⇒ p | x9 ⇒ p | xA ⇒ p | xB ⇒ p | xC ⇒ p | xD ⇒ p | xE ⇒ p
   | xF ⇒ mk_Array16T T e00 e01 e02 e03 e04 e05 e06 e07 e08 e09 e10 e11 e12 e13 e14 v ]
  ].

(* abbiamo gia' gli esadecimali come tipo induttivo quindi: *)
(* posso definire un setter composto [m+1,n-1] a matrice sull'array *)
(* NB: obbiettivo evitare l'overflow *)
ndefinition setmn_array16T_succ_pred ≝
λm,n:exadecim.λT:Type.λp:Array16T T.λv:T.
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
ndefinition setmn_array16T_succ ≝
λm:exadecim.λT:Type.λp:Array16T T.λv:T.
 match lt_ex m xF with
  [ true ⇒ setmn_array16T (succ_ex m) xF T p v
  | false ⇒ p
  ].

(* abbiamo gia' gli esadecimali come tipo induttivo quindi: *)
(* posso definire un setter composto [0,n-1] a matrice sull'array *)
(* NB: obbiettivo evitare l'overflow *)
ndefinition setmn_array16T_pred ≝
λn:exadecim.λT:Type.λp:Array16T T.λv:T.
 match gt_ex n x0 with
  [ true ⇒ setmn_array16T x0 (pred_ex n) T p v
  | false ⇒ p
  ].

(* ************************** *)
(* TIPO BYTE COME INSIEME BIT *)
(* ************************** *)

(* definizione di un byte come 8 bit *)
nrecord Array8T (T:Type) : Type ≝
{ a8_1  : T ; a8_2  : T ; a8_3  : T ; a8_4  : T
; a8_5  : T ; a8_6  : T ; a8_7  : T ; a8_8  : T }.

(* operatore uguaglianza *)
ndefinition eq_ar8 ≝
λT.λf:T → T → bool.λa1,a2:Array8T T.
 (f (a8_1 ? a1) (a8_1 ? a2)) ⊗ (f (a8_2 ? a1) (a8_2 ? a2)) ⊗
 (f (a8_3 ? a1) (a8_3 ? a2)) ⊗ (f (a8_4 ? a1) (a8_4 ? a2)) ⊗
 (f (a8_5 ? a1) (a8_5 ? a2)) ⊗ (f (a8_6 ? a1) (a8_6 ? a2)) ⊗
 (f (a8_7 ? a1) (a8_7 ? a2)) ⊗ (f (a8_8 ? a1) (a8_8 ? a2)).

(* abbiamo gia' gli ottali come tipo induttivo quindi: *)
(* posso definire un getter a matrice sull'array *)
ndefinition getn_array8T ≝
λn:oct.λT:Type.λp:Array8T T.
 match n return λn.(Array8T T) → T with
  [ o0 ⇒ a8_1  T | o1 ⇒ a8_2  T | o2 ⇒ a8_3  T | o3 ⇒ a8_4  T
  | o4 ⇒ a8_5  T | o5 ⇒ a8_6  T | o6 ⇒ a8_7  T | o7 ⇒ a8_8  T
  ] p.

(* abbiamo gia' gli ottali come tipo induttivo quindi: *)
(* posso definire un setter a matrice sull'array *)
ndefinition setn_array8T ≝
λn:oct.λT:Type.λp:Array8T T.λv:T.
let e00 ≝ (a8_1 T p) in
let e01 ≝ (a8_2 T p) in
let e02 ≝ (a8_3 T p) in
let e03 ≝ (a8_4 T p) in
let e04 ≝ (a8_5 T p) in
let e05 ≝ (a8_6 T p) in
let e06 ≝ (a8_7 T p) in
let e07 ≝ (a8_8 T p) in
 match n with
  [ o0 ⇒ mk_Array8T T v   e01 e02 e03 e04 e05 e06 e07
  | o1 ⇒ mk_Array8T T e00 v   e02 e03 e04 e05 e06 e07
  | o2 ⇒ mk_Array8T T e00 e01 v   e03 e04 e05 e06 e07
  | o3 ⇒ mk_Array8T T e00 e01 e02 v   e04 e05 e06 e07
  | o4 ⇒ mk_Array8T T e00 e01 e02 e03 v   e05 e06 e07
  | o5 ⇒ mk_Array8T T e00 e01 e02 e03 e04 v   e06 e07
  | o6 ⇒ mk_Array8T T e00 e01 e02 e03 e04 e05 v   e07
  | o7 ⇒ mk_Array8T T e00 e01 e02 e03 e04 e05 e06 v
  ].

(* lettura byte *)
ndefinition byte8_of_bits ≝
λp:Array8T bool.
   mk_byte8
   (or_ex (match a8_1 ? p with [ true ⇒ x8 | false ⇒ x0 ])
   (or_ex (match a8_2 ? p with [ true ⇒ x4 | false ⇒ x0 ])
   (or_ex (match a8_3 ? p with [ true ⇒ x2 | false ⇒ x0 ])
          (match a8_4 ? p with [ true ⇒ x1 | false ⇒ x0 ]))))
   (or_ex (match a8_5 ? p with [ true ⇒ x8 | false ⇒ x0 ])
   (or_ex (match a8_6 ? p with [ true ⇒ x4 | false ⇒ x0 ])
   (or_ex (match a8_7 ? p with [ true ⇒ x2 | false ⇒ x0 ])
          (match a8_8 ? p with [ true ⇒ x1 | false ⇒ x0 ])))).

(* scrittura byte *)
ndefinition bits_of_exadecim ≝
λe:exadecim.match e with
 [ x0 ⇒ quadruple … false false false false
 | x1 ⇒ quadruple … false false false true
 | x2 ⇒ quadruple … false false true  false
 | x3 ⇒ quadruple … false false true  true
 | x4 ⇒ quadruple … false true  false false
 | x5 ⇒ quadruple … false true  false true
 | x6 ⇒ quadruple … false true  true  false
 | x7 ⇒ quadruple … false true  true  true
 | x8 ⇒ quadruple … true  false false false
 | x9 ⇒ quadruple … true  false false true
 | xA ⇒ quadruple … true  false true  false
 | xB ⇒ quadruple … true  false true  true
 | xC ⇒ quadruple … true  true  false false
 | xD ⇒ quadruple … true  true  false true
 | xE ⇒ quadruple … true  true  true  false
 | xF ⇒ quadruple … true  true  true  true
 ].

ndefinition bits_of_byte8 ≝
λb:byte8.
 mk_Array8T ? (fst4T … (bits_of_exadecim (cnH ? b)))
              (snd4T … (bits_of_exadecim (cnH ? b)))
              (thd4T … (bits_of_exadecim (cnH ? b)))
              (fth4T … (bits_of_exadecim (cnH ? b)))
              (fst4T … (bits_of_exadecim (cnL ? b)))
              (snd4T … (bits_of_exadecim (cnL ? b)))
              (thd4T … (bits_of_exadecim (cnL ? b)))
              (fth4T … (bits_of_exadecim (cnL ? b))).

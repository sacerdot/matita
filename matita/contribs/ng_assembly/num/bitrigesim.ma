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

include "num/bool.ma".

(* ************* *)
(* BITRIGESIMALI *)
(* ************* *)

ninductive bitrigesim : Type ≝
  t00: bitrigesim
| t01: bitrigesim
| t02: bitrigesim
| t03: bitrigesim
| t04: bitrigesim
| t05: bitrigesim
| t06: bitrigesim
| t07: bitrigesim
| t08: bitrigesim
| t09: bitrigesim
| t0A: bitrigesim
| t0B: bitrigesim
| t0C: bitrigesim
| t0D: bitrigesim
| t0E: bitrigesim
| t0F: bitrigesim
| t10: bitrigesim
| t11: bitrigesim
| t12: bitrigesim
| t13: bitrigesim
| t14: bitrigesim
| t15: bitrigesim
| t16: bitrigesim
| t17: bitrigesim
| t18: bitrigesim
| t19: bitrigesim
| t1A: bitrigesim
| t1B: bitrigesim
| t1C: bitrigesim
| t1D: bitrigesim
| t1E: bitrigesim
| t1F: bitrigesim.

(* operatore = *)
ndefinition eq_bit ≝
λt1,t2:bitrigesim.
 match t1 with
  [ t00 ⇒ match t2 with [ t00 ⇒ true | _ ⇒ false ] | t01 ⇒ match t2 with [ t01 ⇒ true | _ ⇒ false ]
  | t02 ⇒ match t2 with [ t02 ⇒ true | _ ⇒ false ] | t03 ⇒ match t2 with [ t03 ⇒ true | _ ⇒ false ]
  | t04 ⇒ match t2 with [ t04 ⇒ true | _ ⇒ false ] | t05 ⇒ match t2 with [ t05 ⇒ true | _ ⇒ false ]
  | t06 ⇒ match t2 with [ t06 ⇒ true | _ ⇒ false ] | t07 ⇒ match t2 with [ t07 ⇒ true | _ ⇒ false ]
  | t08 ⇒ match t2 with [ t08 ⇒ true | _ ⇒ false ] | t09 ⇒ match t2 with [ t09 ⇒ true | _ ⇒ false ]
  | t0A ⇒ match t2 with [ t0A ⇒ true | _ ⇒ false ] | t0B ⇒ match t2 with [ t0B ⇒ true | _ ⇒ false ]
  | t0C ⇒ match t2 with [ t0C ⇒ true | _ ⇒ false ] | t0D ⇒ match t2 with [ t0D ⇒ true | _ ⇒ false ]
  | t0E ⇒ match t2 with [ t0E ⇒ true | _ ⇒ false ] | t0F ⇒ match t2 with [ t0F ⇒ true | _ ⇒ false ]
  | t10 ⇒ match t2 with [ t10 ⇒ true | _ ⇒ false ] | t11 ⇒ match t2 with [ t11 ⇒ true | _ ⇒ false ]
  | t12 ⇒ match t2 with [ t12 ⇒ true | _ ⇒ false ] | t13 ⇒ match t2 with [ t13 ⇒ true | _ ⇒ false ]
  | t14 ⇒ match t2 with [ t14 ⇒ true | _ ⇒ false ] | t15 ⇒ match t2 with [ t15 ⇒ true | _ ⇒ false ]
  | t16 ⇒ match t2 with [ t16 ⇒ true | _ ⇒ false ] | t17 ⇒ match t2 with [ t17 ⇒ true | _ ⇒ false ]
  | t18 ⇒ match t2 with [ t18 ⇒ true | _ ⇒ false ] | t19 ⇒ match t2 with [ t19 ⇒ true | _ ⇒ false ]
  | t1A ⇒ match t2 with [ t1A ⇒ true | _ ⇒ false ] | t1B ⇒ match t2 with [ t1B ⇒ true | _ ⇒ false ]
  | t1C ⇒ match t2 with [ t1C ⇒ true | _ ⇒ false ] | t1D ⇒ match t2 with [ t1D ⇒ true | _ ⇒ false ]
  | t1E ⇒ match t2 with [ t1E ⇒ true | _ ⇒ false ] | t1F ⇒ match t2 with [ t1F ⇒ true | _ ⇒ false ]
  ].

(* iteratore sui bitrigesimali *)
ndefinition forall_bit ≝ λP.
 P t00 ⊗ P t01 ⊗ P t02 ⊗ P t03 ⊗ P t04 ⊗ P t05 ⊗ P t06 ⊗ P t07 ⊗
 P t08 ⊗ P t09 ⊗ P t0A ⊗ P t0B ⊗ P t0C ⊗ P t0D ⊗ P t0E ⊗ P t0F ⊗
 P t10 ⊗ P t11 ⊗ P t12 ⊗ P t13 ⊗ P t14 ⊗ P t15 ⊗ P t16 ⊗ P t17 ⊗
 P t18 ⊗ P t19 ⊗ P t1A ⊗ P t1B ⊗ P t1C ⊗ P t1D ⊗ P t1E ⊗ P t1F.

(* operatore successore *)
ndefinition succ_bit ≝
λn.match n with
 [ t00 ⇒ t01 | t01 ⇒ t02 | t02 ⇒ t03 | t03 ⇒ t04 | t04 ⇒ t05 | t05 ⇒ t06 | t06 ⇒ t07 | t07 ⇒ t08
 | t08 ⇒ t09 | t09 ⇒ t0A | t0A ⇒ t0B | t0B ⇒ t0C | t0C ⇒ t0D | t0D ⇒ t0E | t0E ⇒ t0F | t0F ⇒ t10
 | t10 ⇒ t11 | t11 ⇒ t12 | t12 ⇒ t13 | t13 ⇒ t14 | t14 ⇒ t15 | t15 ⇒ t16 | t16 ⇒ t17 | t17 ⇒ t18
 | t18 ⇒ t19 | t19 ⇒ t1A | t1A ⇒ t1B | t1B ⇒ t1C | t1C ⇒ t1D | t1D ⇒ t1E | t1E ⇒ t1F | t1F ⇒ t00
 ].

(* bitrigesimali ricorsivi *)
ninductive rec_bitrigesim : bitrigesim → Type ≝
  bi_O : rec_bitrigesim t00
| bi_S : ∀n.rec_bitrigesim n → rec_bitrigesim (succ_bit n).

(* bitrigesimali → bitrigesimali ricorsivi *)
ndefinition bit_to_recbit ≝
λn.match n return λx.rec_bitrigesim x with
 [ t00 ⇒ bi_O
 | t01 ⇒ bi_S ? bi_O
 | t02 ⇒ bi_S ? (bi_S ? bi_O)
 | t03 ⇒ bi_S ? (bi_S ? (bi_S ? bi_O))
 | t04 ⇒ bi_S ? (bi_S ? (bi_S ? (bi_S ? bi_O)))
 | t05 ⇒ bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? bi_O))))
 | t06 ⇒ bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? bi_O)))))
 | t07 ⇒ bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? bi_O))))))
 | t08 ⇒ bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
         bi_O)))))))
 | t09 ⇒ bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? bi_O))))))))
 | t0A ⇒ bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? bi_O)))))))))
 | t0B ⇒ bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? bi_O))))))))))
 | t0C ⇒ bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? (bi_S ? bi_O)))))))))))
 | t0D ⇒ bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? bi_O))))))))))))
 | t0E ⇒ bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? bi_O)))))))))))))
 | t0F ⇒ bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? bi_O))))))))))))))
 | t10 ⇒ bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
         bi_O)))))))))))))))
 | t11 ⇒ bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? bi_O))))))))))))))))
 | t12 ⇒ bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? bi_O)))))))))))))))))
 | t13 ⇒ bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? bi_O))))))))))))))))))
 | t14 ⇒ bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? (bi_S ? bi_O)))))))))))))))))))
 | t15 ⇒ bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? bi_O))))))))))))))))))))
 | t16 ⇒ bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? bi_O)))))))))))))))))))))
 | t17 ⇒ bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? bi_O))))))))))))))))))))))
 | t18 ⇒ bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
         bi_O)))))))))))))))))))))))
 | t19 ⇒ bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? bi_O))))))))))))))))))))))))
 | t1A ⇒ bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? bi_O)))))))))))))))))))))))))
 | t1B ⇒ bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? bi_O))))))))))))))))))))))))))
 | t1C ⇒ bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? (bi_S ? bi_O)))))))))))))))))))))))))))
 | t1D ⇒ bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? bi_O))))))))))))))))))))))))))))
 | t1E ⇒ bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? bi_O)))))))))))))))))))))))))))))
 | t1F ⇒ bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? bi_O))))))))))))))))))))))))))))))
 ].

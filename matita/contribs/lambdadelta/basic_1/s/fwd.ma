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

(* This file was automatically generated: do not edit *********************)

include "basic_1/s/defs.ma".

theorem s_inj:
 \forall (k: K).(\forall (i: nat).(\forall (j: nat).((eq nat (s k i) (s k j)) 
\to (eq nat i j))))
\def
 \lambda (k: K).(let TMP_1 \def (\lambda (k0: K).(\forall (i: nat).(\forall 
(j: nat).((eq nat (s k0 i) (s k0 j)) \to (eq nat i j))))) in (let TMP_2 \def 
(\lambda (b: B).(\lambda (i: nat).(\lambda (j: nat).(\lambda (H: (eq nat (s 
(Bind b) i) (s (Bind b) j))).(eq_add_S i j H))))) in (let TMP_3 \def (\lambda 
(f: F).(\lambda (i: nat).(\lambda (j: nat).(\lambda (H: (eq nat (s (Flat f) 
i) (s (Flat f) j))).H)))) in (K_ind TMP_1 TMP_2 TMP_3 k)))).

theorem s_le_gen:
 \forall (k: K).(\forall (i: nat).(\forall (j: nat).((le (s k i) (s k j)) \to 
(le i j))))
\def
 \lambda (k: K).(let TMP_1 \def (\lambda (k0: K).(\forall (i: nat).(\forall 
(j: nat).((le (s k0 i) (s k0 j)) \to (le i j))))) in (let TMP_2 \def (\lambda 
(b: B).(\lambda (i: nat).(\lambda (j: nat).(\lambda (H: (le (s (Bind b) i) (s 
(Bind b) j))).(le_S_n i j H))))) in (let TMP_3 \def (\lambda (f: F).(\lambda 
(i: nat).(\lambda (j: nat).(\lambda (H: (le (s (Flat f) i) (s (Flat f) 
j))).H)))) in (K_ind TMP_1 TMP_2 TMP_3 k)))).

theorem s_lt_gen:
 \forall (k: K).(\forall (i: nat).(\forall (j: nat).((lt (s k i) (s k j)) \to 
(lt i j))))
\def
 \lambda (k: K).(let TMP_1 \def (\lambda (k0: K).(\forall (i: nat).(\forall 
(j: nat).((lt (s k0 i) (s k0 j)) \to (lt i j))))) in (let TMP_3 \def (\lambda 
(b: B).(\lambda (i: nat).(\lambda (j: nat).(\lambda (H: (lt (s (Bind b) i) (s 
(Bind b) j))).(let TMP_2 \def (S i) in (le_S_n TMP_2 j H)))))) in (let TMP_4 
\def (\lambda (f: F).(\lambda (i: nat).(\lambda (j: nat).(\lambda (H: (lt (s 
(Flat f) i) (s (Flat f) j))).H)))) in (K_ind TMP_1 TMP_3 TMP_4 k)))).


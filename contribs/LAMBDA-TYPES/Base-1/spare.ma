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

set "baseuri" "cic:/matita/LAMBDA-TYPES/Base-1/spare".

include "theory.ma".
(*
inductive pr: Set \def
| pr_zero: pr
| pr_succ: pr
| pr_proj: nat \to pr
| pr_comp: ((nat \to pr)) \to (pr \to pr)
| pr_prec: pr \to (pr \to pr).

definition pr_type:
 Set
\def
 ((nat \to nat)) \to nat.

definition prec_appl:
 pr_type \to (pr_type \to (nat \to pr_type))
\def
 let rec prec_appl (f: pr_type) (g: pr_type) (n: nat) on n: pr_type \def 
(match n with [O \Rightarrow f | (S m) \Rightarrow (\lambda (ns: ((nat \to 
nat))).(g (\lambda (i: nat).(match i with [O \Rightarrow (prec_appl f g m ns) 
| (S n0) \Rightarrow (match n0 with [O \Rightarrow m | (S j) \Rightarrow (ns 
j)])]))))]) in prec_appl.

definition pr_appl:
 pr \to pr_type
\def
 let rec pr_appl (h: pr) on h: pr_type \def (match h with [pr_zero 
\Rightarrow (\lambda (_: ((nat \to nat))).O) | pr_succ \Rightarrow (\lambda 
(ns: ((nat \to nat))).(S (ns O))) | (pr_proj i) \Rightarrow (\lambda (ns: 
((nat \to nat))).(ns i)) | (pr_comp fs g) \Rightarrow (\lambda (ns: ((nat \to 
nat))).(pr_appl g (\lambda (i: nat).(pr_appl (fs i) ns)))) | (pr_prec f g) 
\Rightarrow (\lambda (ns: ((nat \to nat))).(prec_appl (pr_appl f) (pr_appl g) 
(ns O) (\lambda (i: nat).(ns (S i)))))]) in pr_appl.

inductive pr_arity: pr \to (nat \to Prop) \def
| pr_arity_zero: \forall (n: nat).(pr_arity pr_zero n)
| pr_arity_succ: \forall (n: nat).((lt O n) \to (pr_arity pr_succ n))
| pr_arity_proj: \forall (n: nat).(\forall (i: nat).((lt i n) \to (pr_arity 
(pr_proj i) n)))
| pr_arity_comp: \forall (n: nat).(\forall (m: nat).(\forall (fs: ((nat \to 
pr))).(\forall (g: pr).((pr_arity g m) \to (((\forall (i: nat).((lt i m) \to 
(pr_arity (fs i) n)))) \to (pr_arity (pr_comp fs g) n))))))
| pr_arity_prec: \forall (n: nat).(\forall (f: pr).(\forall (g: pr).((lt O n) 
\to ((pr_arity f (pred n)) \to ((pr_arity g (S n)) \to (pr_arity (pr_prec f 
g) n)))))).

theorem pr_arity_le:
 \forall (h: pr).(\forall (m: nat).((pr_arity h m) \to (\forall (n: nat).((le 
m n) \to (pr_arity h n)))))
\def
 \lambda (h: pr).(\lambda (m: nat).(\lambda (H: (pr_arity h m)).(pr_arity_ind 
(\lambda (p: pr).(\lambda (n: nat).(\forall (n0: nat).((le n n0) \to 
(pr_arity p n0))))) (\lambda (n: nat).(\lambda (n0: nat).(\lambda (_: (le n 
n0)).(pr_arity_zero n0)))) (\lambda (n: nat).(\lambda (H0: (lt O n)).(\lambda 
(n0: nat).(\lambda (H1: (le n n0)).(pr_arity_succ n0 (lt_le_trans O n n0 H0 
H1)))))) (\lambda (n: nat).(\lambda (i: nat).(\lambda (H0: (lt i n)).(\lambda 
(n0: nat).(\lambda (H1: (le n n0)).(pr_arity_proj n0 i (lt_le_trans i n n0 H0 
H1))))))) (\lambda (n: nat).(\lambda (m0: nat).(\lambda (fs: ((nat \to 
pr))).(\lambda (g: pr).(\lambda (H0: (pr_arity g m0)).(\lambda (_: ((\forall 
(n0: nat).((le m0 n0) \to (pr_arity g n0))))).(\lambda (_: ((\forall (i: 
nat).((lt i m0) \to (pr_arity (fs i) n))))).(\lambda (H3: ((\forall (i: 
nat).((lt i m0) \to (\forall (n0: nat).((le n n0) \to (pr_arity (fs i) 
n0))))))).(\lambda (n0: nat).(\lambda (H4: (le n n0)).(pr_arity_comp n0 m0 fs 
g H0 (\lambda (i: nat).(\lambda (H5: (lt i m0)).(H3 i H5 n0 H4)))))))))))))) 
(\lambda (n: nat).(\lambda (f: pr).(\lambda (g: pr).(\lambda (H0: (lt O 
n)).(\lambda (_: (pr_arity f (pred n))).(\lambda (H2: ((\forall (n0: 
nat).((le (pred n) n0) \to (pr_arity f n0))))).(\lambda (_: (pr_arity g (S 
n))).(\lambda (H4: ((\forall (n0: nat).((le (S n) n0) \to (pr_arity g 
n0))))).(\lambda (n0: nat).(\lambda (H5: (le n n0)).(pr_arity_prec n0 f g 
(lt_le_trans O n n0 H0 H5) (H2 (pred n0) (le_n_pred n n0 H5)) (H4 (S n0) 
(le_n_S n n0 H5))))))))))))) h m H))).

theorem pr_arity_appl:
 \forall (h: pr).(\forall (n: nat).((pr_arity h n) \to (\forall (ns: ((nat 
\to nat))).(\forall (ms: ((nat \to nat))).(((\forall (i: nat).((lt i n) \to 
(eq nat (ns i) (ms i))))) \to (eq nat (pr_appl h ns) (pr_appl h ms)))))))
\def
 \lambda (h: pr).(\lambda (n: nat).(\lambda (H: (pr_arity h n)).(pr_arity_ind 
(\lambda (p: pr).(\lambda (n0: nat).(\forall (ns: ((nat \to nat))).(\forall 
(ms: ((nat \to nat))).(((\forall (i: nat).((lt i n0) \to (eq nat (ns i) (ms 
i))))) \to (eq nat (pr_appl p ns) (pr_appl p ms))))))) (\lambda (n0: 
nat).(\lambda (ns: ((nat \to nat))).(\lambda (ms: ((nat \to nat))).(\lambda 
(_: ((\forall (i: nat).((lt i n0) \to (eq nat (ns i) (ms i)))))).(refl_equal 
nat O))))) (\lambda (n0: nat).(\lambda (H0: (lt O n0)).(\lambda (ns: ((nat 
\to nat))).(\lambda (ms: ((nat \to nat))).(\lambda (H1: ((\forall (i: 
nat).((lt i n0) \to (eq nat (ns i) (ms i)))))).(f_equal nat nat S (ns O) (ms 
O) (H1 O H0))))))) (\lambda (n0: nat).(\lambda (i: nat).(\lambda (H0: (lt i 
n0)).(\lambda (ns: ((nat \to nat))).(\lambda (ms: ((nat \to nat))).(\lambda 
(H1: ((\forall (i0: nat).((lt i0 n0) \to (eq nat (ns i0) (ms i0)))))).(H1 i 
H0))))))) (\lambda (n0: nat).(\lambda (m: nat).(\lambda (fs: ((nat \to 
pr))).(\lambda (g: pr).(\lambda (_: (pr_arity g m)).(\lambda (H1: ((\forall 
(ns: ((nat \to nat))).(\forall (ms: ((nat \to nat))).(((\forall (i: nat).((lt 
i m) \to (eq nat (ns i) (ms i))))) \to (eq nat (pr_appl g ns) (pr_appl g 
ms))))))).(\lambda (_: ((\forall (i: nat).((lt i m) \to (pr_arity (fs i) 
n0))))).(\lambda (H3: ((\forall (i: nat).((lt i m) \to (\forall (ns: ((nat 
\to nat))).(\forall (ms: ((nat \to nat))).(((\forall (i0: nat).((lt i0 n0) 
\to (eq nat (ns i0) (ms i0))))) \to (eq nat (pr_appl (fs i) ns) (pr_appl (fs 
i) ms))))))))).(\lambda (ns: ((nat \to nat))).(\lambda (ms: ((nat \to 
nat))).(\lambda (H4: ((\forall (i: nat).((lt i n0) \to (eq nat (ns i) (ms 
i)))))).(H1 (\lambda (i: nat).(pr_appl (fs i) ns)) (\lambda (i: nat).(pr_appl 
(fs i) ms)) (\lambda (i: nat).(\lambda (H5: (lt i m)).(H3 i H5 ns ms 
H4))))))))))))))) (\lambda (n0: nat).(\lambda (f: pr).(\lambda (g: 
pr).(\lambda (H0: (lt O n0)).(\lambda (_: (pr_arity f (pred n0))).(\lambda 
(H2: ((\forall (ns: ((nat \to nat))).(\forall (ms: ((nat \to 
nat))).(((\forall (i: nat).((lt i (pred n0)) \to (eq nat (ns i) (ms i))))) 
\to (eq nat (pr_appl f ns) (pr_appl f ms))))))).(\lambda (_: (pr_arity g (S 
n0))).(\lambda (H4: ((\forall (ns: ((nat \to nat))).(\forall (ms: ((nat \to 
nat))).(((\forall (i: nat).((lt i (S n0)) \to (eq nat (ns i) (ms i))))) \to 
(eq nat (pr_appl g ns) (pr_appl g ms))))))).(\lambda (ns: ((nat \to 
nat))).(\lambda (ms: ((nat \to nat))).(\lambda (H5: ((\forall (i: nat).((lt i 
n0) \to (eq nat (ns i) (ms i)))))).(eq_ind nat (ns O) (\lambda (n1: nat).(eq 
nat (prec_appl (pr_appl f) (pr_appl g) (ns O) (\lambda (i: nat).(ns (S i)))) 
(prec_appl (pr_appl f) (pr_appl g) n1 (\lambda (i: nat).(ms (S i)))))) (let 
n1 \def (ns O) in (nat_ind (\lambda (n2: nat).(eq nat (prec_appl (pr_appl f) 
(pr_appl g) n2 (\lambda (i: nat).(ns (S i)))) (prec_appl (pr_appl f) (pr_appl 
g) n2 (\lambda (i: nat).(ms (S i)))))) (H2 (\lambda (i: nat).(ns (S i))) 
(\lambda (i: nat).(ms (S i))) (\lambda (i: nat).(\lambda (H6: (lt i (pred 
n0))).(H5 (S i) (lt_x_pred_y i n0 H6))))) (\lambda (n2: nat).(\lambda (IHn0: 
(eq nat (prec_appl (pr_appl f) (pr_appl g) n2 (\lambda (i: nat).(ns (S i)))) 
(prec_appl (pr_appl f) (pr_appl g) n2 (\lambda (i: nat).(ms (S i)))))).(H4 
(\lambda (i: nat).(match i with [O \Rightarrow (prec_appl (pr_appl f) 
(pr_appl g) n2 (\lambda (i0: nat).(ns (S i0)))) | (S n3) \Rightarrow (match 
n3 with [O \Rightarrow n2 | (S j) \Rightarrow (ns (S j))])])) (\lambda (i: 
nat).(match i with [O \Rightarrow (prec_appl (pr_appl f) (pr_appl g) n2 
(\lambda (i0: nat).(ms (S i0)))) | (S n3) \Rightarrow (match n3 with [O 
\Rightarrow n2 | (S j) \Rightarrow (ms (S j))])])) (\lambda (i: nat).(\lambda 
(H6: (lt i (S n0))).(nat_ind (\lambda (n3: nat).((lt n3 (S n0)) \to (eq nat 
(match n3 with [O \Rightarrow (prec_appl (pr_appl f) (pr_appl g) n2 (\lambda 
(i0: nat).(ns (S i0)))) | (S n4) \Rightarrow (match n4 with [O \Rightarrow n2 
| (S j) \Rightarrow (ns (S j))])]) (match n3 with [O \Rightarrow (prec_appl 
(pr_appl f) (pr_appl g) n2 (\lambda (i0: nat).(ms (S i0)))) | (S n4) 
\Rightarrow (match n4 with [O \Rightarrow n2 | (S j) \Rightarrow (ms (S 
j))])])))) (\lambda (_: (lt O (S n0))).IHn0) (\lambda (i0: nat).(\lambda (_: 
(((lt i0 (S n0)) \to (eq nat (match i0 with [O \Rightarrow (prec_appl 
(pr_appl f) (pr_appl g) n2 (\lambda (i1: nat).(ns (S i1)))) | (S n3) 
\Rightarrow (match n3 with [O \Rightarrow n2 | (S j) \Rightarrow (ns (S 
j))])]) (match i0 with [O \Rightarrow (prec_appl (pr_appl f) (pr_appl g) n2 
(\lambda (i1: nat).(ms (S i1)))) | (S n3) \Rightarrow (match n3 with [O 
\Rightarrow n2 | (S j) \Rightarrow (ms (S j))])]))))).(\lambda (H7: (lt (S 
i0) (S n0))).(let H_y \def (H5 i0 (lt_S_n i0 n0 H7)) in (nat_ind (\lambda 
(n3: nat).((eq nat (ns n3) (ms n3)) \to (eq nat (match n3 with [O \Rightarrow 
n2 | (S j) \Rightarrow (ns (S j))]) (match n3 with [O \Rightarrow n2 | (S j) 
\Rightarrow (ms (S j))])))) (\lambda (_: (eq nat (ns O) (ms O))).(refl_equal 
nat n2)) (\lambda (i1: nat).(\lambda (_: (((eq nat (ns i1) (ms i1)) \to (eq 
nat (match i1 with [O \Rightarrow n2 | (S j) \Rightarrow (ns (S j))]) (match 
i1 with [O \Rightarrow n2 | (S j) \Rightarrow (ms (S j))]))))).(\lambda (H8: 
(eq nat (ns (S i1)) (ms (S i1)))).H8))) i0 H_y))))) i H6)))))) n1)) (ms O) 
(H5 O H0))))))))))))) h n H))).

theorem pr_arity_comp_proj_zero:
 \forall (n: nat).(pr_arity (pr_comp pr_proj pr_zero) n)
\def
 \lambda (n: nat).(pr_arity_comp n n pr_proj pr_zero (pr_arity_zero n) 
(\lambda (i: nat).(\lambda (H: (lt i n)).(pr_arity_proj n i H)))).

*)

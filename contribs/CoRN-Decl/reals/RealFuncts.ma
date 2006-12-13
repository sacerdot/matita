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

set "baseuri" "cic:/matita/CoRN-Decl/reals/RealFuncts".

include "CoRN.ma".

(* $Id: RealFuncts.v,v 1.4 2004/04/07 15:08:10 lcf Exp $ *)

include "reals/CReals1.ma".

(*#* * Continuity of Functions on Reals
*)

(* begin hide *)

(* UNEXPORTED
Set Implicit Arguments.
*)

(* UNEXPORTED
Unset Strict Implicit.
*)

(* end hide *)

(* UNEXPORTED
Section Continuity
*)

alias id "f" = "cic:/CoRN/reals/RealFuncts/Continuity/f.var".

alias id "f2" = "cic:/CoRN/reals/RealFuncts/Continuity/f2.var".

(*#*
Let [f] be a unary setoid operation on [IR] and
let [f2] be a binary setoid operation on [IR].

We use the following notations for intervals. [Intclr a b] for the
closed interval [[a,b]], [Intolr a b] for the
open interval [(a,b)], [Intcl a] for the
left-closed interval $[a,\infty)$#[a,&infin;)#, [Intol a] for the
left-open interval $(a,\infty)$#(a,&infin;)#, [Intcr b] for the
right-closed interval $(-\infty,b]$#(-&infin;,b]#.

Intervals like $[a,b]$#[a,b]# are defined for arbitrary reals [a,b] (being
$\emptyset$#&empty;# for [a [>] b]).
*)

inline "cic:/CoRN/reals/RealFuncts/Intclr.con".

inline "cic:/CoRN/reals/RealFuncts/Intolr.con".

inline "cic:/CoRN/reals/RealFuncts/Intol.con".

inline "cic:/CoRN/reals/RealFuncts/Intcl.con".

inline "cic:/CoRN/reals/RealFuncts/Intcr.con".

(*#* The limit of [f(x)] as [x] goes to [p = l], for both unary and binary
functions:

The limit of [f] in [p] is [l] if 
[[
forall e [>] Zero, exists d [>] Zero, forall (x : IR)
( [--]d [<] p[-]x [<] d) -> ( [--]e [<] [--]f(x) [<] e)
]]
*)

inline "cic:/CoRN/reals/RealFuncts/funLim.con".

(*#* The definition of limit of [f] in [p] using Cauchy sequences. *)

inline "cic:/CoRN/reals/RealFuncts/funLim_Cauchy.con".

(*#* The first definition implies the second one. *)

(*
 Ax_iom funLim_prop1 :(p,l:IR)(funLim p l)->(funLim_Cauchy p l).
Intros. Unfold funLim_Cauchy. Unfold funLim in H. Intros.
Elim (H e H1). Intros.
Elim s. Intros s_seq s_proof.
Decompose [and] H2.
Cut (Zero  [<]   x[/]TwoNZ).
Intro Hx2.
Elim (s_proof (x[/]TwoNZ) Hx2).
Intros N HN.
Exists N.
Intros.
Apply AbsSmall_minus.
Apply H5.
Generalize (HN m H3).
Intro HmN.
*)

(*#* The limit of [f] in [(p,p')] is [l] if
[[
forall e [>] Zero, exists d [>] Zero, forall (x : IR)
( [--]d [<] p[-]x [<] d) -> ( [--]d' [<] p'[-]y [<] d') -> ( [--]e [<] l[-]f(x,y) [<] e
]]
*)

inline "cic:/CoRN/reals/RealFuncts/funLim2.con".

(*#* The function [f] is continuous at [p] if the limit of [f(x)] as
[x] goes to [p] is [f(p)].  This is the [eps [/] delta] definition.
We also give the definition with limits of Cauchy sequences.
*)

inline "cic:/CoRN/reals/RealFuncts/continAt.con".

inline "cic:/CoRN/reals/RealFuncts/continAtCauchy.con".

inline "cic:/CoRN/reals/RealFuncts/continAt2.con".

(*
Ax_iom continAt_prop1 :(p:IR)(continAt p)->(continAtCauchy p).
*)

inline "cic:/CoRN/reals/RealFuncts/contin.con".

inline "cic:/CoRN/reals/RealFuncts/continCauchy.con".

inline "cic:/CoRN/reals/RealFuncts/contin2.con".

(*#*
Continuous on a closed, resp.%\% open, resp.%\% left open, resp.%\% left closed
interval *)

inline "cic:/CoRN/reals/RealFuncts/continOnc.con".

inline "cic:/CoRN/reals/RealFuncts/continOno.con".

inline "cic:/CoRN/reals/RealFuncts/continOnol.con".

inline "cic:/CoRN/reals/RealFuncts/continOncl.con".

(*
Section Sequence_and_function_limits.

_**
If $\lim_{x->p} (f x) = l$, then for every sequence $p_n$ whose
limit is $p$, $\lim_{n->\infty} f (p_n) =l$.
 *_

Lemma funLim_SeqLimit:
  (p,l:IR)(fl:(funLim p l))
    (pn:nat->IR)(sl:(SeqLimit pn p)) (SeqLimit ( [n:nat] (f (pn n))) l).
Proof.
Intros; Unfold seqLimit.
Intros eps epos.
Elim (fl ? epos); Intros del dh; Elim dh; Intros H0 H1.
Elim (sl ? H0); Intros N Nh.
Exists N. Intros m leNm.
Apply AbsSmall_minus.
Apply H1.
Apply AbsSmall_minus.
Apply (Nh ? leNm).
Qed.

_**** Is the converse constructively provable? **
Lemma SeqLimit_funLim:
  (p,l:IR)((pn:nat->IR)(sl:(SeqLimit pn p)) (SeqLimit ( [n:nat] (f (pn n))) l))->
    (funLim p l).
****_

_**
Now the same Lemma in terms of Cauchy sequences: if $\lim_{x->p} (f x) = l$,
then for every Cauchy sequence $s_n$ whose
limit is $p$, $\lim_{n->\infty} f (s_n) =l$.
 *_

Ax_iom funLim_isCauchy:
  (p,l:IR)(funLim p l)->(s:CauchySeqR)((Lim s)  [=]   p)->
	(e:IR)(Zero  [<]  e)->(Ex [N:nat] (m:nat)(le N m)
			 ->(AbsSmall e ((s m) [-] (s N)))).

End Sequence_and_function_limits.

Section Monotonic_functions.

Definition str_monot  := (x,y:IR)(x  [<]  y)->((f x)  [<]  (f y)).

Definition str_monotOnc  := [a,b:IR]
         (x,y:IR)(Intclr a b x)->(Intclr a b y)
                ->(x  [<]  y)->((f x)  [<]  (f y)).

Definition str_monotOncl  := [a:IR]
         (x,y:IR)(Intcl a x)->(Intcl a y)
                ->(x  [<]  y)->((f x)  [<]  (f y)).

Definition str_monotOnol  := [a:IR]
         (x,y:IR)(Intol a x)->(Intol a y)
                ->(x  [<]  y)->((f x)  [<]  (f y)).

_** Following probably not needed for the FTA proof;
it stated that strong monotonicity on a closed interval implies that the
intermediate value theorem holds on this interval. For FTA we need IVT on
$[0,\infty>$.
*_

Ax_iom strmonc_imp_ivt :(a,b:IR)(str_monotOnc a b)
           ->(x,y:IR)(x  [<]  y)->(Intclr a b x)->(Intclr a b y)
               ->((f x)  [<]  Zero)->(Zero  [<]  (f y))
                   ->(EX z:IR | (Intclr x y z)/\((f z)  [=]  Zero)).
_**
$\forall c\in\RR (f\mbox{ strongly monotonic on }[c,\infty>)
\rightarrow \forall a,b\in\RR(c <a)\rightarrow( c< b)\rightarrow\ (f (a)<0)
\rightarrow\ (0:<f(b))
         \rightarrow \forall x,y\in\RR (a\leq x\leq b)\rightarrow
	(a\leq y\leq b)\rightarrow (x<y)
                \rightarrow \exists z\in\RR(x\leq z\leq y)\wedge(f(z)\noto 0))$
*_

Ax_iom strmon_ivt_prem : (c:IR)(str_monotOncl c)->
  (a,b:IR)(Intcl c a)->(Intcl c b)->((f a)  [<]   Zero)->(Zero   [<]  (f b))
       ->(x,y:IR)(Intclr a b x)->(Intclr a b y)->(x  [<]  y)
              ->(EX z:IR | (Intclr x y z)/\((f z)  [#]  Zero)).

_** The following is lemma 5.8 from the skeleton

$\forall c\in\RR (f\mbox{ strongly monotonic on }[c,\infty>)
\rightarrow \forall a,b\in\RR(a<b) \rightarrow(c <a)\rightarrow( c< b)
\rightarrow(f (a)<0)\rightarrow (0:<f(b))
         \rightarrow \exists z\in\RR(a\leq z\leq b)\wedge(f(z)= 0))$
*_

Ax_iom strmoncl_imp_ivt : (c:IR)(str_monotOncl c)
           ->(a,b:IR)(a  [<]  b)->(Intcl c a)->(Intcl c b)
               ->((f a)  [<]  Zero)->(Zero  [<]  (f b))
                   ->(EX z:IR | (Intclr a b z)/\ ((f z)  [=]  Zero)).
End Monotonic_functions.

*)

(* UNEXPORTED
End Continuity
*)

(* begin hide *)

(* UNEXPORTED
Set Strict Implicit.
*)

(* UNEXPORTED
Unset Implicit Arguments.
*)

(* end hide *)


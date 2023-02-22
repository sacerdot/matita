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

set "baseuri" "cic:/matita/CoRN-Decl/reals/NRootIR".

include "CoRN.ma".

(* $Id: NRootIR.v,v 1.5 2004/04/23 10:01:05 lcf Exp $ *)

(*#* printing NRoot %\ensuremath{\sqrt[n]{\cdot}}% *)

(*#* printing sqrt %\ensuremath{\sqrt{\cdot}}% *)

include "reals/OddPolyRootIR.ma".

(*#* * Roots of Real Numbers *)

(* UNEXPORTED
Section NRoot
*)

(*#* ** Existence of roots

%\begin{convention}% Let [n] be a natural number and [c] a nonnegative real.
[p] is the auxiliary polynomial [_X_[^]n[-] (_C_ c)].
%\end{convention}%
*)

alias id "n" = "cic:/CoRN/reals/NRootIR/NRoot/n.var".

alias id "n_pos" = "cic:/CoRN/reals/NRootIR/NRoot/n_pos.var".

alias id "c" = "cic:/CoRN/reals/NRootIR/NRoot/c.var".

alias id "c_nonneg" = "cic:/CoRN/reals/NRootIR/NRoot/c_nonneg.var".

(* begin hide *)

inline "cic:/CoRN/reals/NRootIR/NRoot/p.con" "NRoot__".

(* end hide *)

inline "cic:/CoRN/reals/NRootIR/CnrootIR.con".

(* UNEXPORTED
End NRoot
*)

(*#* We define the root of order [n] for any nonnegative real number and 
prove its main properties: 
 - $\left(\sqrt[n]x\right)^n=x$#(sqrt(n) x)^n =x#;
 - $0\leq\sqrt[n]x$#0&le;sqrt(n)x#;
 - if [Zero [<] x] then $0<\sqrt[n]x$#0&lt;sqrt(n)x#;
 - $\sqrt[n]{x^n}=x$#sqrt(n) x^n =x#;
 - the nth root is monotonous;
 - in particular, if [x [<] One] then $\sqrt[n]x<1$#sqrt(n) x&lt;1#.

[(nroot ??)] will be written as [NRoot].
*)

(* UNEXPORTED
Section Nth_Root
*)

inline "cic:/CoRN/reals/NRootIR/nroot.con".

inline "cic:/CoRN/reals/NRootIR/NRoot.con".

inline "cic:/CoRN/reals/NRootIR/NRoot_power.con".

(* UNEXPORTED
Hint Resolve NRoot_power: algebra.
*)

inline "cic:/CoRN/reals/NRootIR/NRoot_nonneg.con".

inline "cic:/CoRN/reals/NRootIR/NRoot_pos.con".

inline "cic:/CoRN/reals/NRootIR/NRoot_power'.con".

inline "cic:/CoRN/reals/NRootIR/NRoot_pres_less.con".

inline "cic:/CoRN/reals/NRootIR/NRoot_less_one.con".

inline "cic:/CoRN/reals/NRootIR/NRoot_cancel.con".

(*#* %\begin{convention}% Let [x,y] be nonnegative real numbers.
%\end{convention}% *)

alias id "x" = "cic:/CoRN/reals/NRootIR/Nth_Root/x.var".

alias id "y" = "cic:/CoRN/reals/NRootIR/Nth_Root/y.var".

alias id "Hx" = "cic:/CoRN/reals/NRootIR/Nth_Root/Hx.var".

alias id "Hy" = "cic:/CoRN/reals/NRootIR/Nth_Root/Hy.var".

inline "cic:/CoRN/reals/NRootIR/NRoot_wd.con".

inline "cic:/CoRN/reals/NRootIR/NRoot_unique.con".

(* UNEXPORTED
End Nth_Root
*)

(* UNEXPORTED
Implicit Arguments NRoot [x n].
*)

(* UNEXPORTED
Hint Resolve NRoot_power NRoot_power': algebra.
*)

inline "cic:/CoRN/reals/NRootIR/NRoot_resp_leEq.con".

(*#**********************************)

(* UNEXPORTED
Section Square_root
*)

(*#**********************************)

(*#* ** Square root *)

inline "cic:/CoRN/reals/NRootIR/sqrt.con".

inline "cic:/CoRN/reals/NRootIR/sqrt_sqr.con".

(* UNEXPORTED
Hint Resolve sqrt_sqr: algebra.
*)

inline "cic:/CoRN/reals/NRootIR/sqrt_nonneg.con".

inline "cic:/CoRN/reals/NRootIR/sqrt_wd.con".

(* UNEXPORTED
Hint Resolve sqrt_wd: algebra_c.
*)

inline "cic:/CoRN/reals/NRootIR/sqrt_to_nonneg.con".

inline "cic:/CoRN/reals/NRootIR/sqrt_to_nonpos.con".

inline "cic:/CoRN/reals/NRootIR/sqrt_mult.con".

(* UNEXPORTED
Hint Resolve sqrt_mult: algebra.
*)

inline "cic:/CoRN/reals/NRootIR/sqrt_mult_wd.con".

inline "cic:/CoRN/reals/NRootIR/sqrt_less.con".

inline "cic:/CoRN/reals/NRootIR/sqrt_less'.con".

inline "cic:/CoRN/reals/NRootIR/sqrt_resp_leEq.con".

inline "cic:/CoRN/reals/NRootIR/sqrt_resp_less.con".

(* UNEXPORTED
End Square_root
*)

(* UNEXPORTED
Hint Resolve sqrt_wd: algebra_c.
*)

(* UNEXPORTED
Hint Resolve sqrt_sqr sqrt_mult: algebra.
*)

(* UNEXPORTED
Section Absolute_Props
*)

(*#* ** More on absolute value

With the help of square roots, we can prove some more properties of absolute 
values in [IR].
*)

inline "cic:/CoRN/reals/NRootIR/AbsIR_sqrt_sqr.con".

(* UNEXPORTED
Hint Resolve AbsIR_sqrt_sqr: algebra.
*)

inline "cic:/CoRN/reals/NRootIR/AbsIR_resp_mult.con".

inline "cic:/CoRN/reals/NRootIR/AbsIR_mult_pos.con".

inline "cic:/CoRN/reals/NRootIR/AbsIR_mult_pos'.con".

inline "cic:/CoRN/reals/NRootIR/AbsIR_nexp.con".

inline "cic:/CoRN/reals/NRootIR/AbsIR_nexp_op.con".

inline "cic:/CoRN/reals/NRootIR/AbsIR_less_square.con".

inline "cic:/CoRN/reals/NRootIR/AbsIR_leEq_square.con".

inline "cic:/CoRN/reals/NRootIR/AbsIR_division.con".

(*#* Some special cases. *)

inline "cic:/CoRN/reals/NRootIR/AbsIR_recip.con".

inline "cic:/CoRN/reals/NRootIR/AbsIR_div_two.con".

(*#* Cauchy-Schwartz for IR and variants on that subject. *)

inline "cic:/CoRN/reals/NRootIR/triangle_IR.con".

inline "cic:/CoRN/reals/NRootIR/triangle_SumIR.con".

inline "cic:/CoRN/reals/NRootIR/triangle_IR_minus.con".

inline "cic:/CoRN/reals/NRootIR/weird_triangleIR.con".

inline "cic:/CoRN/reals/NRootIR/triangle_IR_minus'.con".

inline "cic:/CoRN/reals/NRootIR/triangle_SumxIR.con".

inline "cic:/CoRN/reals/NRootIR/triangle_Sum2IR.con".

inline "cic:/CoRN/reals/NRootIR/AbsIR_str_bnd_AbsIR.con".

inline "cic:/CoRN/reals/NRootIR/AbsIR_bnd_AbsIR.con".

(* UNEXPORTED
End Absolute_Props
*)

(* UNEXPORTED
Section Consequences
*)

(*#* **Cauchy sequences

With these results, we can also prove that the sequence of reciprocals of a 
Cauchy sequence that is never zero and whose Limit is not zero is also a 
Cauchy sequence.
*)

inline "cic:/CoRN/reals/NRootIR/Cauchy_Lim_recip.con".

inline "cic:/CoRN/reals/NRootIR/Cauchy_recip.con".

inline "cic:/CoRN/reals/NRootIR/Lim_recip.con".

(* UNEXPORTED
End Consequences
*)


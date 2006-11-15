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

set "baseuri" "cic:/matita/CoRN-Decl/complex/NRootCC".

(* $Id: NRootCC.v,v 1.9 2004/04/23 10:00:55 lcf Exp $ *)

(*#* printing sqrt_Half %\ensuremath{\sqrt{\frac12}}% *)

(*#* printing sqrt_I %\ensuremath{\sqrt{\imath}}% *)

(*#* printing nroot_I %\ensuremath{\sqrt[n]{\imath}}% *)

(*#* printing nroot_minus_I %\ensuremath{\sqrt[n]{-\imath}}% *)

(* INCLUDE
CComplex
*)

(* INCLUDE
Wf_nat
*)

(* INCLUDE
ArithRing
*)

(*#* * Roots of Complex Numbers

Properties of non-zero complex numbers
*)

(* UNEXPORTED
Section CC_ap_zero.
*)

inline cic:/CoRN/complex/NRootCC/cc_ap_zero.con.

inline cic:/CoRN/complex/NRootCC/C_cc_ap_zero.con.

(* UNEXPORTED
End CC_ap_zero.
*)

(*#* Weird lemma. *)

(* UNEXPORTED
Section Imag_to_Real.
*)

inline cic:/CoRN/complex/NRootCC/imag_to_real.con.

(* UNEXPORTED
End Imag_to_Real.
*)

(*#* ** Roots of the imaginary unit *)

(* UNEXPORTED
Section NRootI.
*)

inline cic:/CoRN/complex/NRootCC/sqrt_Half.con.

inline cic:/CoRN/complex/NRootCC/sqrt_I.con.

inline cic:/CoRN/complex/NRootCC/sqrt_I_nexp.con.

inline cic:/CoRN/complex/NRootCC/nroot_I_nexp_aux.con.

inline cic:/CoRN/complex/NRootCC/nroot_I.con.

inline cic:/CoRN/complex/NRootCC/nroot_I_nexp.con.

(* UNEXPORTED
Hint Resolve nroot_I_nexp: algebra.
*)

inline cic:/CoRN/complex/NRootCC/nroot_minus_I.con.

inline cic:/CoRN/complex/NRootCC/nroot_minus_I_nexp.con.

(* UNEXPORTED
End NRootI.
*)

(*#* ** Roots of complex numbers *)

(* UNEXPORTED
Section NRootCC_1.
*)

(*#* We define the nth root of a complex number with a non zero imaginary part.
*)

(* UNEXPORTED
Section NRootCC_1_ap_real.
*)

(*#*
%\begin{convention}% Let [a,b : IR] and [b_ : (b [#] Zero)].
Define [c2 := a[^]2[+]b[^]2], [c := sqrt c2], [a'2 := (c[+]a) [*]Half],
[a' := sqrt a'2], [b'2 := (c[-]a) [*]Half] and [b' := sqrt b'2].
%\end{convention}%
*)

inline cic:/CoRN/complex/NRootCC/a.var.

inline cic:/CoRN/complex/NRootCC/b.var.

inline cic:/CoRN/complex/NRootCC/b_.var.

(* begin hide *)

inline cic:/CoRN/complex/NRootCC/c2.con.

(* end hide *)

inline cic:/CoRN/complex/NRootCC/nrCC1_c2pos.con.

(* begin hide *)

inline cic:/CoRN/complex/NRootCC/c.con.

inline cic:/CoRN/complex/NRootCC/a'2.con.

(* end hide *)

inline cic:/CoRN/complex/NRootCC/nrCC1_a'2pos.con.

(* begin hide *)

inline cic:/CoRN/complex/NRootCC/a'.con.

inline cic:/CoRN/complex/NRootCC/b'2.con.

(* end hide *)

inline cic:/CoRN/complex/NRootCC/nrCC1_b'2pos.con.

(* begin hide *)

inline cic:/CoRN/complex/NRootCC/b'.con.

(* end hide *)

inline cic:/CoRN/complex/NRootCC/nrCC1_a3.con.

inline cic:/CoRN/complex/NRootCC/nrCC1_a4.con.

(* UNEXPORTED
Hint Resolve nrCC1_a4: algebra.
*)

inline cic:/CoRN/complex/NRootCC/nrCC1_a5.con.

inline cic:/CoRN/complex/NRootCC/nrCC1_a6.con.

inline cic:/CoRN/complex/NRootCC/nrCC1_a6'.con.

(* UNEXPORTED
Hint Resolve nrCC1_a5: algebra.
*)

inline cic:/CoRN/complex/NRootCC/nrCC1_a7_upper.con.

inline cic:/CoRN/complex/NRootCC/nrCC1_a7_lower.con.

(* UNEXPORTED
Hint Resolve nrCC1_a3 nrCC1_a7_upper nrCC1_a7_lower: algebra.
*)

inline cic:/CoRN/complex/NRootCC/nrootCC_1_upper.con.

inline cic:/CoRN/complex/NRootCC/nrootCC_1_lower.con.

inline cic:/CoRN/complex/NRootCC/nrootCC_1_ap_real.con.

(* UNEXPORTED
End NRootCC_1_ap_real.
*)

(*#* We now define the nth root of a complex number with a non zero real part.
*)

(* UNEXPORTED
Section NRootCC_1_ap_imag.
*)

(*#*
%\begin{convention}% Let [a,b : IR] and [a_ : (a [#] Zero)] and define
[c' := (a[+I*]b) [*][--]II := a'[+I*]b'].
%\end{convention}%
*)

inline cic:/CoRN/complex/NRootCC/a.var.

inline cic:/CoRN/complex/NRootCC/b.var.

inline cic:/CoRN/complex/NRootCC/a_.var.

(* begin hide *)

inline cic:/CoRN/complex/NRootCC/c'.con.

inline cic:/CoRN/complex/NRootCC/a'.con.

inline cic:/CoRN/complex/NRootCC/b'.con.

(* end hide *)

(* UNEXPORTED
Hint Resolve sqrt_I_nexp: algebra.
*)

inline cic:/CoRN/complex/NRootCC/nrootCC_1_ap_imag.con.

(* UNEXPORTED
End NRootCC_1_ap_imag.
*)

(*#* We now define the roots of arbitrary non zero complex numbers. *)

inline cic:/CoRN/complex/NRootCC/nrootCC_1.con.

(* UNEXPORTED
End NRootCC_1.
*)

(* UNEXPORTED
Section NRootCC_2.
*)

(*#*
%\begin{convention}% Let [n : nat] and [c,z : CC] and [c_:(c [#] Zero)].
%\end{convention}%
*)

inline cic:/CoRN/complex/NRootCC/n.var.

inline cic:/CoRN/complex/NRootCC/c.var.

inline cic:/CoRN/complex/NRootCC/z.var.

inline cic:/CoRN/complex/NRootCC/c_.var.

inline cic:/CoRN/complex/NRootCC/nrootCC_2'.con.

inline cic:/CoRN/complex/NRootCC/nrootCC_2.con.

(* UNEXPORTED
End NRootCC_2.
*)

(* UNEXPORTED
Section NRootCC_3.
*)

inline cic:/CoRN/complex/NRootCC/Im_poly.con.

inline cic:/CoRN/complex/NRootCC/nrCC3_a1.con.

inline cic:/CoRN/complex/NRootCC/nrCC3_a2.con.

(*#*
%\begin{convention}% Let [a,b : IR], [b_ : (b [#] Zero)] and [n : nat].
%\end{convention}%
*)

inline cic:/CoRN/complex/NRootCC/a.var.

inline cic:/CoRN/complex/NRootCC/b.var.

inline cic:/CoRN/complex/NRootCC/b_.var.

inline cic:/CoRN/complex/NRootCC/n.var.

inline cic:/CoRN/complex/NRootCC/nrCC3_poly''.con.

inline cic:/CoRN/complex/NRootCC/nrCC3_a3.con.

inline cic:/CoRN/complex/NRootCC/nrCC3_a4.con.

inline cic:/CoRN/complex/NRootCC/nrCC3_a5.con.

inline cic:/CoRN/complex/NRootCC/nrCC3_a6.con.

inline cic:/CoRN/complex/NRootCC/nrCC3_poly'.con.

(* UNEXPORTED
Hint Resolve nrCC3_a3: algebra.
*)

inline cic:/CoRN/complex/NRootCC/nrCC3_a7.con.

inline cic:/CoRN/complex/NRootCC/nrCC3_a8.con.

(* UNEXPORTED
Hint Resolve nth_coeff_p_mult_c_: algebra.
*)

(* UNEXPORTED
Hint Resolve nrCC3_a6: algebra.
*)

inline cic:/CoRN/complex/NRootCC/nrCC3_a9.con.

inline cic:/CoRN/complex/NRootCC/nrootCC_3_poly.con.

(* UNEXPORTED
Hint Resolve nrCC3_a1 nrCC3_a7: algebra.
*)

inline cic:/CoRN/complex/NRootCC/nrootCC_3_.con.

(* UNEXPORTED
Hint Resolve nrootCC_3_: algebra.
*)

(* UNEXPORTED
Hint Resolve calculate_Im: algebra.
*)

inline cic:/CoRN/complex/NRootCC/nrootCC_3.con.

(* UNEXPORTED
Hint Resolve nrCC3_a2: algebra.
*)

(* UNEXPORTED
Hint Resolve nrCC3_a9: algebra.
*)

inline cic:/CoRN/complex/NRootCC/nrootCC_3_degree.con.

(* UNEXPORTED
End NRootCC_3.
*)

(* UNEXPORTED
Section NRootCC_3'.
*)

(*#*
%\begin{convention}% Let [c:IR], [n:nat] and [n_:(lt (0) n)].
%\end{convention}%
*)

inline cic:/CoRN/complex/NRootCC/c.var.

inline cic:/CoRN/complex/NRootCC/n.var.

inline cic:/CoRN/complex/NRootCC/n_.var.

inline cic:/CoRN/complex/NRootCC/nrootCC_3'_poly.con.

inline cic:/CoRN/complex/NRootCC/nrootCC_3'.con.

inline cic:/CoRN/complex/NRootCC/nrootCC_3'_degree.con.

(* UNEXPORTED
End NRootCC_3'.
*)

(* UNEXPORTED
Section NRootCC_4.
*)

(* UNEXPORTED
Section NRootCC_4_ap_real.
*)

(*#*
%\begin{convention}% Let [a,b : IR], [b_ : (b [#] Zero)], [n : nat] and
[n_:(odd n)]; define [c := a[+I*]b].
%\end{convention}%
*)

inline cic:/CoRN/complex/NRootCC/a.var.

inline cic:/CoRN/complex/NRootCC/b.var.

inline cic:/CoRN/complex/NRootCC/b_.var.

inline cic:/CoRN/complex/NRootCC/n.var.

inline cic:/CoRN/complex/NRootCC/n_.var.

(* begin hide *)

inline cic:/CoRN/complex/NRootCC/c.con.

(* end hide *)

(* UNEXPORTED
Section NRootCC_4_solutions.
*)

(* UNEXPORTED
Hint Resolve nrootCC_3: algebra.
*)

inline cic:/CoRN/complex/NRootCC/nrCC4_a1.con.

(*#*
%\begin{convention}% Let [r2',c2 : IR] and [r2'_ : (r2' [#] Zero)].
%\end{convention}%
*)

inline cic:/CoRN/complex/NRootCC/r2'.var.

inline cic:/CoRN/complex/NRootCC/c2.var.

inline cic:/CoRN/complex/NRootCC/r2'_.var.

(* UNEXPORTED
Hint Resolve nrootCC_3': algebra.
*)

inline cic:/CoRN/complex/NRootCC/nrCC4_a1'.con.

(* UNEXPORTED
End NRootCC_4_solutions.
*)

(* UNEXPORTED
Section NRootCC_4_equations.
*)

(*#*
%\begin{convention}% Let [r,y2 : IR] be such that
[(r[+I*]One) [^]n[*] (CC_conj c) [-] (r[+I*][--]One) [^]n[*]c [=] Zero]
and [(y2[*] (r[^] (2) [+]One)) [^]n [=] a[^] (2) [+]b[^] (2)].
%\end{convention}%
*)

inline cic:/CoRN/complex/NRootCC/r.var.

inline cic:/CoRN/complex/NRootCC/r_property.var.

inline cic:/CoRN/complex/NRootCC/y2.var.

inline cic:/CoRN/complex/NRootCC/y2_property.var.

inline cic:/CoRN/complex/NRootCC/nrCC4_a2.con.

inline cic:/CoRN/complex/NRootCC/nrCC4_a3.con.

inline cic:/CoRN/complex/NRootCC/nrCC4_a4.con.

inline cic:/CoRN/complex/NRootCC/nrCC4_y.con.

inline cic:/CoRN/complex/NRootCC/y.con.

inline cic:/CoRN/complex/NRootCC/nrCC4_x.con.

inline cic:/CoRN/complex/NRootCC/x.con.

inline cic:/CoRN/complex/NRootCC/nrCC4_a5.con.

inline cic:/CoRN/complex/NRootCC/nrCC4_a6.con.

inline cic:/CoRN/complex/NRootCC/nrCC4_z.con.

inline cic:/CoRN/complex/NRootCC/z.con.

inline cic:/CoRN/complex/NRootCC/nrCC4_a7.con.

(* UNEXPORTED
Hint Resolve nrCC4_a6: algebra.
*)

inline cic:/CoRN/complex/NRootCC/nrCC4_a8.con.

inline cic:/CoRN/complex/NRootCC/nrCC4_a9.con.

(* UNEXPORTED
End NRootCC_4_equations.
*)

inline cic:/CoRN/complex/NRootCC/nrCC4_a10.con.

inline cic:/CoRN/complex/NRootCC/nrootCC_4_ap_real.con.

(* UNEXPORTED
End NRootCC_4_ap_real.
*)

(* UNEXPORTED
Section NRootCC_4_ap_imag.
*)

(*#*
%\begin{convention}% Let [a,b : IR] and [n : nat] with [a [#] Zero]
and [(odd n)]; define [c' := (a[+I*]b) [*]II := a'[+I*]b'].
%\end{convention}%
*)

inline cic:/CoRN/complex/NRootCC/a.var.

inline cic:/CoRN/complex/NRootCC/b.var.

inline cic:/CoRN/complex/NRootCC/a_.var.

inline cic:/CoRN/complex/NRootCC/n.var.

inline cic:/CoRN/complex/NRootCC/n_.var.

(* begin hide *)

inline cic:/CoRN/complex/NRootCC/c'.con.

inline cic:/CoRN/complex/NRootCC/a'.con.

inline cic:/CoRN/complex/NRootCC/b'.con.

(* end hide *)

inline cic:/CoRN/complex/NRootCC/nrootCC_4_ap_real'.con.

(* UNEXPORTED
Hint Resolve nroot_minus_I_nexp: algebra.
*)

inline cic:/CoRN/complex/NRootCC/nrootCC_4_ap_imag.con.

(* UNEXPORTED
End NRootCC_4_ap_imag.
*)

inline cic:/CoRN/complex/NRootCC/nrootCC_4.con.

(* UNEXPORTED
End NRootCC_4.
*)

(*#* Finally, the general definition of nth root. *)

(* UNEXPORTED
Section NRootCC_5.
*)

inline cic:/CoRN/complex/NRootCC/nrCC_5a2.con.

inline cic:/CoRN/complex/NRootCC/nrCC_5a3.con.

(* UNEXPORTED
Hint Resolve nrCC_5a3: algebra.
*)

(*#*
%\begin{convention}% Let [c : CC] with [c [#] Zero].
%\end{convention}%
*)

inline cic:/CoRN/complex/NRootCC/c.var.

inline cic:/CoRN/complex/NRootCC/c_.var.

inline cic:/CoRN/complex/NRootCC/nrCC_5a4.con.

inline cic:/CoRN/complex/NRootCC/nrootCC_5.con.

(* UNEXPORTED
End NRootCC_5.
*)

(*#* Final definition *)

inline cic:/CoRN/complex/NRootCC/CnrootCC.con.


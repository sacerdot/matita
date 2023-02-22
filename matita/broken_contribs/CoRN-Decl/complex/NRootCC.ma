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

include "CoRN.ma".

(* $Id: NRootCC.v,v 1.9 2004/04/23 10:00:55 lcf Exp $ *)

(*#* printing sqrt_Half %\ensuremath{\sqrt{\frac12}}% *)

(*#* printing sqrt_I %\ensuremath{\sqrt{\imath}}% *)

(*#* printing nroot_I %\ensuremath{\sqrt[n]{\imath}}% *)

(*#* printing nroot_minus_I %\ensuremath{\sqrt[n]{-\imath}}% *)

include "complex/CComplex.ma".

(*#* * Roots of Complex Numbers

Properties of non-zero complex numbers
*)

(* UNEXPORTED
Section CC_ap_zero
*)

inline "cic:/CoRN/complex/NRootCC/cc_ap_zero.con".

inline "cic:/CoRN/complex/NRootCC/C_cc_ap_zero.con".

(* UNEXPORTED
End CC_ap_zero
*)

(*#* Weird lemma. *)

(* UNEXPORTED
Section Imag_to_Real
*)

inline "cic:/CoRN/complex/NRootCC/imag_to_real.con".

(* UNEXPORTED
End Imag_to_Real
*)

(*#* ** Roots of the imaginary unit *)

(* UNEXPORTED
Section NRootI
*)

inline "cic:/CoRN/complex/NRootCC/sqrt_Half.con".

inline "cic:/CoRN/complex/NRootCC/sqrt_I.con".

inline "cic:/CoRN/complex/NRootCC/sqrt_I_nexp.con".

inline "cic:/CoRN/complex/NRootCC/nroot_I_nexp_aux.con".

inline "cic:/CoRN/complex/NRootCC/nroot_I.con".

inline "cic:/CoRN/complex/NRootCC/nroot_I_nexp.con".

(* UNEXPORTED
Hint Resolve nroot_I_nexp: algebra.
*)

inline "cic:/CoRN/complex/NRootCC/nroot_minus_I.con".

inline "cic:/CoRN/complex/NRootCC/nroot_minus_I_nexp.con".

(* UNEXPORTED
End NRootI
*)

(*#* ** Roots of complex numbers *)

(* UNEXPORTED
Section NRootCC_1
*)

(*#* We define the nth root of a complex number with a non zero imaginary part.
*)

(* UNEXPORTED
Section NRootCC_1_ap_real
*)

(*#*
%\begin{convention}% Let [a,b : IR] and [b_ : (b [#] Zero)].
Define [c2 := a[^]2[+]b[^]2], [c := sqrt c2], [a'2 := (c[+]a) [*]Half],
[a' := sqrt a'2], [b'2 := (c[-]a) [*]Half] and [b' := sqrt b'2].
%\end{convention}%
*)

alias id "a" = "cic:/CoRN/complex/NRootCC/NRootCC_1/NRootCC_1_ap_real/a.var".

alias id "b" = "cic:/CoRN/complex/NRootCC/NRootCC_1/NRootCC_1_ap_real/b.var".

alias id "b_" = "cic:/CoRN/complex/NRootCC/NRootCC_1/NRootCC_1_ap_real/b_.var".

(* begin hide *)

inline "cic:/CoRN/complex/NRootCC/NRootCC_1/NRootCC_1_ap_real/c2.con" "NRootCC_1__NRootCC_1_ap_real__".

(* end hide *)

inline "cic:/CoRN/complex/NRootCC/nrCC1_c2pos.con".

(* begin hide *)

inline "cic:/CoRN/complex/NRootCC/NRootCC_1/NRootCC_1_ap_real/c.con" "NRootCC_1__NRootCC_1_ap_real__".

inline "cic:/CoRN/complex/NRootCC/NRootCC_1/NRootCC_1_ap_real/a'2.con" "NRootCC_1__NRootCC_1_ap_real__".

(* end hide *)

inline "cic:/CoRN/complex/NRootCC/nrCC1_a'2pos.con".

(* begin hide *)

inline "cic:/CoRN/complex/NRootCC/NRootCC_1/NRootCC_1_ap_real/a'.con" "NRootCC_1__NRootCC_1_ap_real__".

inline "cic:/CoRN/complex/NRootCC/NRootCC_1/NRootCC_1_ap_real/b'2.con" "NRootCC_1__NRootCC_1_ap_real__".

(* end hide *)

inline "cic:/CoRN/complex/NRootCC/nrCC1_b'2pos.con".

(* begin hide *)

inline "cic:/CoRN/complex/NRootCC/NRootCC_1/NRootCC_1_ap_real/b'.con" "NRootCC_1__NRootCC_1_ap_real__".

(* end hide *)

inline "cic:/CoRN/complex/NRootCC/nrCC1_a3.con".

inline "cic:/CoRN/complex/NRootCC/nrCC1_a4.con".

(* UNEXPORTED
Hint Resolve nrCC1_a4: algebra.
*)

inline "cic:/CoRN/complex/NRootCC/nrCC1_a5.con".

inline "cic:/CoRN/complex/NRootCC/nrCC1_a6.con".

inline "cic:/CoRN/complex/NRootCC/nrCC1_a6'.con".

(* UNEXPORTED
Hint Resolve nrCC1_a5: algebra.
*)

inline "cic:/CoRN/complex/NRootCC/nrCC1_a7_upper.con".

inline "cic:/CoRN/complex/NRootCC/nrCC1_a7_lower.con".

(* UNEXPORTED
Hint Resolve nrCC1_a3 nrCC1_a7_upper nrCC1_a7_lower: algebra.
*)

inline "cic:/CoRN/complex/NRootCC/nrootCC_1_upper.con".

inline "cic:/CoRN/complex/NRootCC/nrootCC_1_lower.con".

inline "cic:/CoRN/complex/NRootCC/nrootCC_1_ap_real.con".

(* UNEXPORTED
End NRootCC_1_ap_real
*)

(*#* We now define the nth root of a complex number with a non zero real part.
*)

(* UNEXPORTED
Section NRootCC_1_ap_imag
*)

(*#*
%\begin{convention}% Let [a,b : IR] and [a_ : (a [#] Zero)] and define
[c' := (a[+I*]b) [*][--]II := a'[+I*]b'].
%\end{convention}%
*)

alias id "a" = "cic:/CoRN/complex/NRootCC/NRootCC_1/NRootCC_1_ap_imag/a.var".

alias id "b" = "cic:/CoRN/complex/NRootCC/NRootCC_1/NRootCC_1_ap_imag/b.var".

alias id "a_" = "cic:/CoRN/complex/NRootCC/NRootCC_1/NRootCC_1_ap_imag/a_.var".

(* begin hide *)

inline "cic:/CoRN/complex/NRootCC/NRootCC_1/NRootCC_1_ap_imag/c'.con" "NRootCC_1__NRootCC_1_ap_imag__".

inline "cic:/CoRN/complex/NRootCC/NRootCC_1/NRootCC_1_ap_imag/a'.con" "NRootCC_1__NRootCC_1_ap_imag__".

inline "cic:/CoRN/complex/NRootCC/NRootCC_1/NRootCC_1_ap_imag/b'.con" "NRootCC_1__NRootCC_1_ap_imag__".

(* end hide *)

(* UNEXPORTED
Hint Resolve sqrt_I_nexp: algebra.
*)

inline "cic:/CoRN/complex/NRootCC/nrootCC_1_ap_imag.con".

(* UNEXPORTED
End NRootCC_1_ap_imag
*)

(*#* We now define the roots of arbitrary non zero complex numbers. *)

inline "cic:/CoRN/complex/NRootCC/nrootCC_1.con".

(* UNEXPORTED
End NRootCC_1
*)

(* UNEXPORTED
Section NRootCC_2
*)

(*#*
%\begin{convention}% Let [n : nat] and [c,z : CC] and [c_:(c [#] Zero)].
%\end{convention}%
*)

alias id "n" = "cic:/CoRN/complex/NRootCC/NRootCC_2/n.var".

alias id "c" = "cic:/CoRN/complex/NRootCC/NRootCC_2/c.var".

alias id "z" = "cic:/CoRN/complex/NRootCC/NRootCC_2/z.var".

alias id "c_" = "cic:/CoRN/complex/NRootCC/NRootCC_2/c_.var".

inline "cic:/CoRN/complex/NRootCC/nrootCC_2'.con".

inline "cic:/CoRN/complex/NRootCC/nrootCC_2.con".

(* UNEXPORTED
End NRootCC_2
*)

(* UNEXPORTED
Section NRootCC_3
*)

inline "cic:/CoRN/complex/NRootCC/Im_poly.con".

inline "cic:/CoRN/complex/NRootCC/nrCC3_a1.con".

inline "cic:/CoRN/complex/NRootCC/nrCC3_a2.con".

(*#*
%\begin{convention}% Let [a,b : IR], [b_ : (b [#] Zero)] and [n : nat].
%\end{convention}%
*)

alias id "a" = "cic:/CoRN/complex/NRootCC/NRootCC_3/a.var".

alias id "b" = "cic:/CoRN/complex/NRootCC/NRootCC_3/b.var".

alias id "b_" = "cic:/CoRN/complex/NRootCC/NRootCC_3/b_.var".

alias id "n" = "cic:/CoRN/complex/NRootCC/NRootCC_3/n.var".

inline "cic:/CoRN/complex/NRootCC/nrCC3_poly''.con".

inline "cic:/CoRN/complex/NRootCC/nrCC3_a3.con".

inline "cic:/CoRN/complex/NRootCC/nrCC3_a4.con".

inline "cic:/CoRN/complex/NRootCC/nrCC3_a5.con".

inline "cic:/CoRN/complex/NRootCC/nrCC3_a6.con".

inline "cic:/CoRN/complex/NRootCC/nrCC3_poly'.con".

(* UNEXPORTED
Hint Resolve nrCC3_a3: algebra.
*)

inline "cic:/CoRN/complex/NRootCC/nrCC3_a7.con".

inline "cic:/CoRN/complex/NRootCC/nrCC3_a8.con".

(* UNEXPORTED
Hint Resolve nth_coeff_p_mult_c_: algebra.
*)

(* UNEXPORTED
Hint Resolve nrCC3_a6: algebra.
*)

inline "cic:/CoRN/complex/NRootCC/nrCC3_a9.con".

inline "cic:/CoRN/complex/NRootCC/nrootCC_3_poly.con".

(* UNEXPORTED
Hint Resolve nrCC3_a1 nrCC3_a7: algebra.
*)

inline "cic:/CoRN/complex/NRootCC/nrootCC_3_.con".

(* UNEXPORTED
Hint Resolve nrootCC_3_: algebra.
*)

(* UNEXPORTED
Hint Resolve calculate_Im: algebra.
*)

inline "cic:/CoRN/complex/NRootCC/nrootCC_3.con".

(* UNEXPORTED
Hint Resolve nrCC3_a2: algebra.
*)

(* UNEXPORTED
Hint Resolve nrCC3_a9: algebra.
*)

inline "cic:/CoRN/complex/NRootCC/nrootCC_3_degree.con".

(* UNEXPORTED
End NRootCC_3
*)

(* UNEXPORTED
Section NRootCC_3'
*)

(*#*
%\begin{convention}% Let [c:IR], [n:nat] and [n_:(lt (0) n)].
%\end{convention}%
*)

alias id "c" = "cic:/CoRN/complex/NRootCC/NRootCC_3'/c.var".

alias id "n" = "cic:/CoRN/complex/NRootCC/NRootCC_3'/n.var".

alias id "n_" = "cic:/CoRN/complex/NRootCC/NRootCC_3'/n_.var".

inline "cic:/CoRN/complex/NRootCC/nrootCC_3'_poly.con".

inline "cic:/CoRN/complex/NRootCC/nrootCC_3'.con".

inline "cic:/CoRN/complex/NRootCC/nrootCC_3'_degree.con".

(* UNEXPORTED
End NRootCC_3'
*)

(* UNEXPORTED
Section NRootCC_4
*)

(* UNEXPORTED
Section NRootCC_4_ap_real
*)

(*#*
%\begin{convention}% Let [a,b : IR], [b_ : (b [#] Zero)], [n : nat] and
[n_:(odd n)]; define [c := a[+I*]b].
%\end{convention}%
*)

alias id "a" = "cic:/CoRN/complex/NRootCC/NRootCC_4/NRootCC_4_ap_real/a.var".

alias id "b" = "cic:/CoRN/complex/NRootCC/NRootCC_4/NRootCC_4_ap_real/b.var".

alias id "b_" = "cic:/CoRN/complex/NRootCC/NRootCC_4/NRootCC_4_ap_real/b_.var".

alias id "n" = "cic:/CoRN/complex/NRootCC/NRootCC_4/NRootCC_4_ap_real/n.var".

alias id "n_" = "cic:/CoRN/complex/NRootCC/NRootCC_4/NRootCC_4_ap_real/n_.var".

(* begin hide *)

inline "cic:/CoRN/complex/NRootCC/NRootCC_4/NRootCC_4_ap_real/c.con" "NRootCC_4__NRootCC_4_ap_real__".

(* end hide *)

(* UNEXPORTED
Section NRootCC_4_solutions
*)

(* UNEXPORTED
Hint Resolve nrootCC_3: algebra.
*)

inline "cic:/CoRN/complex/NRootCC/nrCC4_a1.con".

(*#*
%\begin{convention}% Let [r2',c2 : IR] and [r2'_ : (r2' [#] Zero)].
%\end{convention}%
*)

alias id "r2'" = "cic:/CoRN/complex/NRootCC/NRootCC_4/NRootCC_4_ap_real/NRootCC_4_solutions/r2'.var".

alias id "c2" = "cic:/CoRN/complex/NRootCC/NRootCC_4/NRootCC_4_ap_real/NRootCC_4_solutions/c2.var".

alias id "r2'_" = "cic:/CoRN/complex/NRootCC/NRootCC_4/NRootCC_4_ap_real/NRootCC_4_solutions/r2'_.var".

(* UNEXPORTED
Hint Resolve nrootCC_3': algebra.
*)

inline "cic:/CoRN/complex/NRootCC/nrCC4_a1'.con".

(* UNEXPORTED
End NRootCC_4_solutions
*)

(* UNEXPORTED
Section NRootCC_4_equations
*)

(*#*
%\begin{convention}% Let [r,y2 : IR] be such that
[(r[+I*]One) [^]n[*] (CC_conj c) [-] (r[+I*][--]One) [^]n[*]c [=] Zero]
and [(y2[*] (r[^] (2) [+]One)) [^]n [=] a[^] (2) [+]b[^] (2)].
%\end{convention}%
*)

alias id "r" = "cic:/CoRN/complex/NRootCC/NRootCC_4/NRootCC_4_ap_real/NRootCC_4_equations/r.var".

alias id "r_property" = "cic:/CoRN/complex/NRootCC/NRootCC_4/NRootCC_4_ap_real/NRootCC_4_equations/r_property.var".

alias id "y2" = "cic:/CoRN/complex/NRootCC/NRootCC_4/NRootCC_4_ap_real/NRootCC_4_equations/y2.var".

alias id "y2_property" = "cic:/CoRN/complex/NRootCC/NRootCC_4/NRootCC_4_ap_real/NRootCC_4_equations/y2_property.var".

inline "cic:/CoRN/complex/NRootCC/nrCC4_a2.con".

inline "cic:/CoRN/complex/NRootCC/nrCC4_a3.con".

inline "cic:/CoRN/complex/NRootCC/nrCC4_a4.con".

inline "cic:/CoRN/complex/NRootCC/nrCC4_y.con".

inline "cic:/CoRN/complex/NRootCC/NRootCC_4/NRootCC_4_ap_real/NRootCC_4_equations/y.con" "NRootCC_4__NRootCC_4_ap_real__NRootCC_4_equations__".

inline "cic:/CoRN/complex/NRootCC/nrCC4_x.con".

inline "cic:/CoRN/complex/NRootCC/NRootCC_4/NRootCC_4_ap_real/NRootCC_4_equations/x.con" "NRootCC_4__NRootCC_4_ap_real__NRootCC_4_equations__".

inline "cic:/CoRN/complex/NRootCC/nrCC4_a5.con".

inline "cic:/CoRN/complex/NRootCC/nrCC4_a6.con".

inline "cic:/CoRN/complex/NRootCC/nrCC4_z.con".

inline "cic:/CoRN/complex/NRootCC/NRootCC_4/NRootCC_4_ap_real/NRootCC_4_equations/z.con" "NRootCC_4__NRootCC_4_ap_real__NRootCC_4_equations__".

inline "cic:/CoRN/complex/NRootCC/nrCC4_a7.con".

(* UNEXPORTED
Hint Resolve nrCC4_a6: algebra.
*)

inline "cic:/CoRN/complex/NRootCC/nrCC4_a8.con".

inline "cic:/CoRN/complex/NRootCC/nrCC4_a9.con".

(* UNEXPORTED
End NRootCC_4_equations
*)

inline "cic:/CoRN/complex/NRootCC/nrCC4_a10.con".

inline "cic:/CoRN/complex/NRootCC/nrootCC_4_ap_real.con".

(* UNEXPORTED
End NRootCC_4_ap_real
*)

(* UNEXPORTED
Section NRootCC_4_ap_imag
*)

(*#*
%\begin{convention}% Let [a,b : IR] and [n : nat] with [a [#] Zero]
and [(odd n)]; define [c' := (a[+I*]b) [*]II := a'[+I*]b'].
%\end{convention}%
*)

alias id "a" = "cic:/CoRN/complex/NRootCC/NRootCC_4/NRootCC_4_ap_imag/a.var".

alias id "b" = "cic:/CoRN/complex/NRootCC/NRootCC_4/NRootCC_4_ap_imag/b.var".

alias id "a_" = "cic:/CoRN/complex/NRootCC/NRootCC_4/NRootCC_4_ap_imag/a_.var".

alias id "n" = "cic:/CoRN/complex/NRootCC/NRootCC_4/NRootCC_4_ap_imag/n.var".

alias id "n_" = "cic:/CoRN/complex/NRootCC/NRootCC_4/NRootCC_4_ap_imag/n_.var".

(* begin hide *)

inline "cic:/CoRN/complex/NRootCC/NRootCC_4/NRootCC_4_ap_imag/c'.con" "NRootCC_4__NRootCC_4_ap_imag__".

inline "cic:/CoRN/complex/NRootCC/NRootCC_4/NRootCC_4_ap_imag/a'.con" "NRootCC_4__NRootCC_4_ap_imag__".

inline "cic:/CoRN/complex/NRootCC/NRootCC_4/NRootCC_4_ap_imag/b'.con" "NRootCC_4__NRootCC_4_ap_imag__".

(* end hide *)

inline "cic:/CoRN/complex/NRootCC/nrootCC_4_ap_real'.con".

(* UNEXPORTED
Hint Resolve nroot_minus_I_nexp: algebra.
*)

inline "cic:/CoRN/complex/NRootCC/nrootCC_4_ap_imag.con".

(* UNEXPORTED
End NRootCC_4_ap_imag
*)

inline "cic:/CoRN/complex/NRootCC/nrootCC_4.con".

(* UNEXPORTED
End NRootCC_4
*)

(*#* Finally, the general definition of nth root. *)

(* UNEXPORTED
Section NRootCC_5
*)

inline "cic:/CoRN/complex/NRootCC/nrCC_5a2.con".

inline "cic:/CoRN/complex/NRootCC/nrCC_5a3.con".

(* UNEXPORTED
Hint Resolve nrCC_5a3: algebra.
*)

(*#*
%\begin{convention}% Let [c : CC] with [c [#] Zero].
%\end{convention}%
*)

alias id "c" = "cic:/CoRN/complex/NRootCC/NRootCC_5/c.var".

alias id "c_" = "cic:/CoRN/complex/NRootCC/NRootCC_5/c_.var".

inline "cic:/CoRN/complex/NRootCC/nrCC_5a4.con".

inline "cic:/CoRN/complex/NRootCC/nrootCC_5.con".

(* UNEXPORTED
End NRootCC_5
*)

(*#* Final definition *)

inline "cic:/CoRN/complex/NRootCC/CnrootCC.con".


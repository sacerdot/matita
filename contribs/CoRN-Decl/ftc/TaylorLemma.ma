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

set "baseuri" "cic:/matita/CoRN-Decl/ftc/TaylorLemma".

include "CoRN.ma".

(* $Id: TaylorLemma.v,v 1.8 2004/04/23 10:01:01 lcf Exp $ *)

include "ftc/Rolle.ma".

(* UNEXPORTED
Opaque Min.
*)

(* UNEXPORTED
Section Taylor_Defs.
*)

(*#* *Taylor's Theorem

We now prove Taylor's theorem for the remainder of the Taylor
series.  This proof is done in two steps: first, we prove the lemma
for a proper compact interval; next we generalize the result to two
arbitrary (eventually equal) points in a proper interval.

** First case

We assume two different points [a] and [b] in the domain of [F] and
define the nth order derivative of [F] in the interval
[[Min(a,b),Max(a,b)]].
*)

inline "cic:/CoRN/ftc/TaylorLemma/a.var".

inline "cic:/CoRN/ftc/TaylorLemma/b.var".

inline "cic:/CoRN/ftc/TaylorLemma/Hap.var".

(* begin hide *)

inline "cic:/CoRN/ftc/TaylorLemma/Hab'.con".

inline "cic:/CoRN/ftc/TaylorLemma/Hab.con".

inline "cic:/CoRN/ftc/TaylorLemma/I.con".

(* end hide *)

inline "cic:/CoRN/ftc/TaylorLemma/F.var".

inline "cic:/CoRN/ftc/TaylorLemma/Ha.var".

inline "cic:/CoRN/ftc/TaylorLemma/Hb.var".

(* begin show *)

inline "cic:/CoRN/ftc/TaylorLemma/fi.con".

(* end show *)

(*#*
This last local definition is simply:
$f_i=f^{(i)}$#f<sub>i</sub>=f<sup>(i)</sup>#.
*)

(* begin hide *)

inline "cic:/CoRN/ftc/TaylorLemma/Taylor_lemma1.con".

(* end hide *)

(*#*
Now we can define the Taylor sequence around [a].  The auxiliary
definition gives, for any [i], the function expressed by the rule
%\[g(x)=\frac{f^{(i)}
(a)}{i!}*(x-a)^i.\]%#g(x)=f<sup>(i)</sup>(a)/i!*(x-a)<sup>i</sup>.#
We denote by [A] and [B] the elements of [[Min(a,b),Max(a,b)]]
corresponding to [a] and [b].
*)

(* begin hide *)

inline "cic:/CoRN/ftc/TaylorLemma/TL_compact_a.con".

inline "cic:/CoRN/ftc/TaylorLemma/TL_compact_b.con".

(* end hide *)

(* begin show *)

inline "cic:/CoRN/ftc/TaylorLemma/funct_i.con".

(* end show *)

(* begin hide *)

inline "cic:/CoRN/ftc/TaylorLemma/funct_i'.con".

inline "cic:/CoRN/ftc/TaylorLemma/TL_a_i.con".

inline "cic:/CoRN/ftc/TaylorLemma/TL_b_i.con".

inline "cic:/CoRN/ftc/TaylorLemma/TL_x_i.con".

inline "cic:/CoRN/ftc/TaylorLemma/TL_a_i'.con".

inline "cic:/CoRN/ftc/TaylorLemma/TL_b_i'.con".

inline "cic:/CoRN/ftc/TaylorLemma/TL_x_i'.con".

inline "cic:/CoRN/ftc/TaylorLemma/Taylor_lemma2.con".

inline "cic:/CoRN/ftc/TaylorLemma/Taylor_lemma2'.con".

inline "cic:/CoRN/ftc/TaylorLemma/Taylor_lemma3.con".

inline "cic:/CoRN/ftc/TaylorLemma/Taylor_lemma3'.con".

(* end hide *)

(*#*
Adding the previous expressions up to a given bound [n] gives us the
Taylor sum of order [n].
*)

inline "cic:/CoRN/ftc/TaylorLemma/Taylor_seq'.con".

(* begin hide *)

inline "cic:/CoRN/ftc/TaylorLemma/Taylor_seq'_aux.con".

inline "cic:/CoRN/ftc/TaylorLemma/TL_lemma_a.con".

(* end hide *)

(*#*
It is easy to show that [b] is in the domain of this series, which allows us to write down the Taylor remainder around [b].
*)

inline "cic:/CoRN/ftc/TaylorLemma/TL_lemma_b.con".

(* begin hide *)

inline "cic:/CoRN/ftc/TaylorLemma/TL_lemma_a'.con".

inline "cic:/CoRN/ftc/TaylorLemma/TL_lemma_b'.con".

(* end hide *)

inline "cic:/CoRN/ftc/TaylorLemma/Taylor_rem.con".

(* begin hide *)

inline "cic:/CoRN/ftc/TaylorLemma/g.con".

(* UNEXPORTED
Opaque Taylor_seq'_aux Taylor_rem.
*)

(* UNEXPORTED
Transparent Taylor_rem.
*)

(* UNEXPORTED
Opaque Taylor_seq'.
*)

(* UNEXPORTED
Transparent Taylor_seq' Taylor_seq'_aux.
*)

(* UNEXPORTED
Opaque funct_i'.
*)

(* UNEXPORTED
Opaque funct_i.
*)

inline "cic:/CoRN/ftc/TaylorLemma/Taylor_lemma4.con".

(* UNEXPORTED
Transparent funct_i funct_i'.
*)

(* UNEXPORTED
Opaque Taylor_seq'_aux.
*)

(* UNEXPORTED
Transparent Taylor_seq'_aux.
*)

(* UNEXPORTED
Opaque FSumx.
*)

(* UNEXPORTED
Opaque funct_i'.
*)

inline "cic:/CoRN/ftc/TaylorLemma/Taylor_lemma5.con".

(* UNEXPORTED
Transparent funct_i' FSumx.
*)

inline "cic:/CoRN/ftc/TaylorLemma/funct_aux.con".

inline "cic:/CoRN/ftc/TaylorLemma/Taylor_lemma6.con".

(* UNEXPORTED
Ltac Lazy_Included :=
  repeat first
   [ apply included_IR
   | apply included_FPlus
   | apply included_FInv
   | apply included_FMinus
   | apply included_FMult
   | apply included_FNth
   | apply included_refl ].
*)

(* UNEXPORTED
Ltac Lazy_Eq :=
  repeat first
   [ apply bin_op_wd_unfolded
   | apply un_op_wd_unfolded
   | apply cg_minus_wd
   | apply div_wd
   | apply csf_wd_unfolded ]; Algebra.
*)

inline "cic:/CoRN/ftc/TaylorLemma/Taylor_lemma7.con".

inline "cic:/CoRN/ftc/TaylorLemma/Taylor_lemma8.con".

(* UNEXPORTED
Opaque funct_aux.
*)

(* UNEXPORTED
Transparent funct_aux.
*)

inline "cic:/CoRN/ftc/TaylorLemma/Taylor_lemma9.con".

inline "cic:/CoRN/ftc/TaylorLemma/g'.con".

(* UNEXPORTED
Opaque Taylor_rem funct_aux.
*)

inline "cic:/CoRN/ftc/TaylorLemma/Taylor_lemma10.con".

(* UNEXPORTED
Transparent Taylor_rem funct_aux.
*)

(* end hide *)

(*#*
Now Taylor's theorem.

%\begin{convention}% Let [e] be a positive real number.
%\end{convention}%
*)

inline "cic:/CoRN/ftc/TaylorLemma/e.var".

inline "cic:/CoRN/ftc/TaylorLemma/He.var".

(* begin hide *)

inline "cic:/CoRN/ftc/TaylorLemma/Taylor_lemma11.con".

(* end hide *)

(* begin show *)

inline "cic:/CoRN/ftc/TaylorLemma/deriv_Sn'.con".

(* end show *)

(* begin hide *)

inline "cic:/CoRN/ftc/TaylorLemma/TLH.con".

(* end hide *)

(* UNEXPORTED
Opaque funct_aux.
*)

(* UNEXPORTED
Opaque Taylor_rem.
*)

(* UNEXPORTED
Transparent Taylor_rem funct_aux.
*)

inline "cic:/CoRN/ftc/TaylorLemma/Taylor_lemma.con".

(* UNEXPORTED
End Taylor_Defs.
*)


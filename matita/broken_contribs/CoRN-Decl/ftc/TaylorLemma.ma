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
Section Taylor_Defs
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

alias id "a" = "cic:/CoRN/ftc/TaylorLemma/Taylor_Defs/a.var".

alias id "b" = "cic:/CoRN/ftc/TaylorLemma/Taylor_Defs/b.var".

alias id "Hap" = "cic:/CoRN/ftc/TaylorLemma/Taylor_Defs/Hap.var".

(* begin hide *)

inline "cic:/CoRN/ftc/TaylorLemma/Taylor_Defs/Hab'.con" "Taylor_Defs__".

inline "cic:/CoRN/ftc/TaylorLemma/Taylor_Defs/Hab.con" "Taylor_Defs__".

inline "cic:/CoRN/ftc/TaylorLemma/Taylor_Defs/I.con" "Taylor_Defs__".

(* end hide *)

alias id "F" = "cic:/CoRN/ftc/TaylorLemma/Taylor_Defs/F.var".

alias id "Ha" = "cic:/CoRN/ftc/TaylorLemma/Taylor_Defs/Ha.var".

alias id "Hb" = "cic:/CoRN/ftc/TaylorLemma/Taylor_Defs/Hb.var".

(* begin show *)

inline "cic:/CoRN/ftc/TaylorLemma/Taylor_Defs/fi.con" "Taylor_Defs__".

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

inline "cic:/CoRN/ftc/TaylorLemma/Taylor_Defs/TL_compact_a.con" "Taylor_Defs__".

inline "cic:/CoRN/ftc/TaylorLemma/Taylor_Defs/TL_compact_b.con" "Taylor_Defs__".

(* NOTATION
Notation A := (Build_subcsetoid_crr IR _ _ TL_compact_a).
*)

(* NOTATION
Notation B := (Build_subcsetoid_crr IR _ _ TL_compact_b).
*)

(* end hide *)

(* begin show *)

inline "cic:/CoRN/ftc/TaylorLemma/Taylor_Defs/funct_i.con" "Taylor_Defs__".

(* end show *)

(* begin hide *)

inline "cic:/CoRN/ftc/TaylorLemma/Taylor_Defs/funct_i'.con" "Taylor_Defs__".

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

inline "cic:/CoRN/ftc/TaylorLemma/Taylor_Defs/Taylor_seq'_aux.con" "Taylor_Defs__".

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

inline "cic:/CoRN/ftc/TaylorLemma/Taylor_Defs/g.con" "Taylor_Defs__".

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

inline "cic:/CoRN/ftc/TaylorLemma/Taylor_Defs/funct_aux.con" "Taylor_Defs__".

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

inline "cic:/CoRN/ftc/TaylorLemma/Taylor_Defs/g'.con" "Taylor_Defs__".

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

alias id "e" = "cic:/CoRN/ftc/TaylorLemma/Taylor_Defs/e.var".

alias id "He" = "cic:/CoRN/ftc/TaylorLemma/Taylor_Defs/He.var".

(* begin hide *)

inline "cic:/CoRN/ftc/TaylorLemma/Taylor_lemma11.con".

(* end hide *)

(* begin show *)

inline "cic:/CoRN/ftc/TaylorLemma/Taylor_Defs/deriv_Sn'.con" "Taylor_Defs__".

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
End Taylor_Defs
*)


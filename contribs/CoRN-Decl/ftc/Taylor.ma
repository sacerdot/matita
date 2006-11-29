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

set "baseuri" "cic:/matita/CoRN-Decl/ftc/Taylor".

include "CoRN.ma".

(* $Id: Taylor.v,v 1.10 2004/04/23 10:01:01 lcf Exp $ *)

include "ftc/TaylorLemma.ma".

(* UNEXPORTED
Opaque Min Max N_Deriv.
*)

(* UNEXPORTED
Section More_Taylor_Defs
*)

(*#* **General case

The generalization to arbitrary intervals just needs a few more definitions.

%\begin{convention}% Let [I] be a proper interval, [F:PartIR] and
[a,b:IR] be points of [I].
%\end{convention}%
*)

inline "cic:/CoRN/ftc/Taylor/More_Taylor_Defs/I.var" "More_Taylor_Defs__".

inline "cic:/CoRN/ftc/Taylor/More_Taylor_Defs/pI.var" "More_Taylor_Defs__".

inline "cic:/CoRN/ftc/Taylor/More_Taylor_Defs/F.var" "More_Taylor_Defs__".

(* begin show *)

inline "cic:/CoRN/ftc/Taylor/More_Taylor_Defs/deriv_Sn.con" "More_Taylor_Defs__".

(* end show *)

inline "cic:/CoRN/ftc/Taylor/More_Taylor_Defs/a.var" "More_Taylor_Defs__".

inline "cic:/CoRN/ftc/Taylor/More_Taylor_Defs/b.var" "More_Taylor_Defs__".

inline "cic:/CoRN/ftc/Taylor/More_Taylor_Defs/Ha.var" "More_Taylor_Defs__".

inline "cic:/CoRN/ftc/Taylor/More_Taylor_Defs/Hb.var" "More_Taylor_Defs__".

(* begin show *)

inline "cic:/CoRN/ftc/Taylor/More_Taylor_Defs/fi.con" "More_Taylor_Defs__".

inline "cic:/CoRN/ftc/Taylor/More_Taylor_Defs/funct_i.con" "More_Taylor_Defs__".

(* end show *)

inline "cic:/CoRN/ftc/Taylor/Taylor_Seq'.con".

(* begin hide *)

inline "cic:/CoRN/ftc/Taylor/TaylorB.con".

(* end hide *)

inline "cic:/CoRN/ftc/Taylor/Taylor_Rem.con".

(* begin hide *)

inline "cic:/CoRN/ftc/Taylor/Taylor_Sumx_lemma.con".

inline "cic:/CoRN/ftc/Taylor/Taylor_lemma_ap.con".

(* end hide *)

inline "cic:/CoRN/ftc/Taylor/Taylor'.con".

(* UNEXPORTED
End More_Taylor_Defs
*)

(* UNEXPORTED
Section Taylor_Theorem
*)

(*#*
And finally the ``nice'' version, when we know the expression of the
derivatives of [F].

%\begin{convention}% Let [f] be the sequence of derivatives of [F] of
order up to [n] and [F'] be the nth-derivative of [F].
%\end{convention}%
*)

inline "cic:/CoRN/ftc/Taylor/Taylor_Theorem/I.var" "Taylor_Theorem__".

inline "cic:/CoRN/ftc/Taylor/Taylor_Theorem/pI.var" "Taylor_Theorem__".

inline "cic:/CoRN/ftc/Taylor/Taylor_Theorem/F.var" "Taylor_Theorem__".

inline "cic:/CoRN/ftc/Taylor/Taylor_Theorem/n.var" "Taylor_Theorem__".

inline "cic:/CoRN/ftc/Taylor/Taylor_Theorem/f.var" "Taylor_Theorem__".

inline "cic:/CoRN/ftc/Taylor/Taylor_Theorem/goodF.var" "Taylor_Theorem__".

inline "cic:/CoRN/ftc/Taylor/Taylor_Theorem/goodF'.var" "Taylor_Theorem__".

inline "cic:/CoRN/ftc/Taylor/Taylor_Theorem/derF.var" "Taylor_Theorem__".

inline "cic:/CoRN/ftc/Taylor/Taylor_Theorem/F'.var" "Taylor_Theorem__".

inline "cic:/CoRN/ftc/Taylor/Taylor_Theorem/derF'.var" "Taylor_Theorem__".

inline "cic:/CoRN/ftc/Taylor/Taylor_Theorem/a.var" "Taylor_Theorem__".

inline "cic:/CoRN/ftc/Taylor/Taylor_Theorem/b.var" "Taylor_Theorem__".

inline "cic:/CoRN/ftc/Taylor/Taylor_Theorem/Ha.var" "Taylor_Theorem__".

inline "cic:/CoRN/ftc/Taylor/Taylor_Theorem/Hb.var" "Taylor_Theorem__".

(* begin show *)

inline "cic:/CoRN/ftc/Taylor/Taylor_Theorem/funct_i.con" "Taylor_Theorem__".

inline "cic:/CoRN/ftc/Taylor/Taylor_Seq.con".

inline "cic:/CoRN/ftc/Taylor/Taylor_Theorem/deriv_Sn.con" "Taylor_Theorem__".

(* end show *)

inline "cic:/CoRN/ftc/Taylor/Taylor_aux.con".

(* UNEXPORTED
Transparent N_Deriv.
*)

inline "cic:/CoRN/ftc/Taylor/Taylor.con".

(* UNEXPORTED
End Taylor_Theorem
*)


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
Section More_Taylor_Defs.
*)

(*#* **General case

The generalization to arbitrary intervals just needs a few more definitions.

%\begin{convention}% Let [I] be a proper interval, [F:PartIR] and
[a,b:IR] be points of [I].
%\end{convention}%
*)

inline "cic:/CoRN/ftc/Taylor/I.var".

inline "cic:/CoRN/ftc/Taylor/pI.var".

inline "cic:/CoRN/ftc/Taylor/F.var".

(* begin show *)

inline "cic:/CoRN/ftc/Taylor/deriv_Sn.con".

(* end show *)

inline "cic:/CoRN/ftc/Taylor/a.var".

inline "cic:/CoRN/ftc/Taylor/b.var".

inline "cic:/CoRN/ftc/Taylor/Ha.var".

inline "cic:/CoRN/ftc/Taylor/Hb.var".

(* begin show *)

inline "cic:/CoRN/ftc/Taylor/fi.con".

inline "cic:/CoRN/ftc/Taylor/funct_i.con".

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
End More_Taylor_Defs.
*)

(* UNEXPORTED
Section Taylor_Theorem.
*)

(*#*
And finally the ``nice'' version, when we know the expression of the
derivatives of [F].

%\begin{convention}% Let [f] be the sequence of derivatives of [F] of
order up to [n] and [F'] be the nth-derivative of [F].
%\end{convention}%
*)

inline "cic:/CoRN/ftc/Taylor/I.var".

inline "cic:/CoRN/ftc/Taylor/pI.var".

inline "cic:/CoRN/ftc/Taylor/F.var".

inline "cic:/CoRN/ftc/Taylor/n.var".

inline "cic:/CoRN/ftc/Taylor/f.var".

inline "cic:/CoRN/ftc/Taylor/goodF.var".

inline "cic:/CoRN/ftc/Taylor/goodF'.var".

inline "cic:/CoRN/ftc/Taylor/derF.var".

inline "cic:/CoRN/ftc/Taylor/F'.var".

inline "cic:/CoRN/ftc/Taylor/derF'.var".

inline "cic:/CoRN/ftc/Taylor/a.var".

inline "cic:/CoRN/ftc/Taylor/b.var".

inline "cic:/CoRN/ftc/Taylor/Ha.var".

inline "cic:/CoRN/ftc/Taylor/Hb.var".

(* begin show *)

inline "cic:/CoRN/ftc/Taylor/funct_i.con".

inline "cic:/CoRN/ftc/Taylor/Taylor_Seq.con".

inline "cic:/CoRN/ftc/Taylor/deriv_Sn.con".

(* end show *)

inline "cic:/CoRN/ftc/Taylor/Taylor_aux.con".

(* UNEXPORTED
Transparent N_Deriv.
*)

inline "cic:/CoRN/ftc/Taylor/Taylor.con".

(* UNEXPORTED
End Taylor_Theorem.
*)


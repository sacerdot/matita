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

set "baseuri" "cic:/matita/CoRN-Decl/ftc/StrongIVT".

include "CoRN.ma".

(* $Id: StrongIVT.v,v 1.5 2004/04/23 10:01:01 lcf Exp $ *)

include "ftc/WeakIVT.ma".

include "ftc/CalculusTheorems.ma".

(* UNEXPORTED
Section IVT'
*)

(*#* ** Strong IVT for partial functions

The IVT can be generalized to arbitrary partial functions; in the first
part, we will simply do that, repeating the previous construction.

The same notations and conventions apply as before.
*)

alias id "a" = "cic:/CoRN/ftc/StrongIVT/IVT'/a.var".

alias id "b" = "cic:/CoRN/ftc/StrongIVT/IVT'/b.var".

alias id "Hab'" = "cic:/CoRN/ftc/StrongIVT/IVT'/Hab'.var".

alias id "Hab" = "cic:/CoRN/ftc/StrongIVT/IVT'/Hab.var".

(* begin hide *)

inline "cic:/CoRN/ftc/StrongIVT/IVT'/I.con" "IVT'__".

inline "cic:/CoRN/ftc/StrongIVT/IVT'/I'.con" "IVT'__".

(* end hide *)

alias id "F" = "cic:/CoRN/ftc/StrongIVT/IVT'/F.var".

alias id "contF" = "cic:/CoRN/ftc/StrongIVT/IVT'/contF.var".

(* begin hide *)

inline "cic:/CoRN/ftc/StrongIVT/IVT'/incF.con" "IVT'__".

(* end hide *)

(* begin show *)

alias id "incrF" = "cic:/CoRN/ftc/StrongIVT/IVT'/incrF.var".

(* end show *)

(* begin hide *)

inline "cic:/CoRN/ftc/StrongIVT/IVT'/Ha.con" "IVT'__".

inline "cic:/CoRN/ftc/StrongIVT/IVT'/Hb.con" "IVT'__".

inline "cic:/CoRN/ftc/StrongIVT/IVT'/HFab'.con" "IVT'__".

(* end hide *)

(* begin show *)

alias id "z" = "cic:/CoRN/ftc/StrongIVT/IVT'/z.var".

alias id "Haz" = "cic:/CoRN/ftc/StrongIVT/IVT'/Haz.var".

alias id "Hzb" = "cic:/CoRN/ftc/StrongIVT/IVT'/Hzb.var".

(* end show *)

inline "cic:/CoRN/ftc/StrongIVT/IVT'_seq_lemma.con".

(* end hide *)

inline "cic:/CoRN/ftc/StrongIVT/IVT'_aux_seq_type.ind".

inline "cic:/CoRN/ftc/StrongIVT/IVT'_iter.con".

inline "cic:/CoRN/ftc/StrongIVT/IVT'_seq.con".

inline "cic:/CoRN/ftc/StrongIVT/a'_seq.con".

inline "cic:/CoRN/ftc/StrongIVT/b'_seq.con".

inline "cic:/CoRN/ftc/StrongIVT/a'_seq_I.con".

inline "cic:/CoRN/ftc/StrongIVT/b'_seq_I.con".

inline "cic:/CoRN/ftc/StrongIVT/a'_seq_less_b'_seq.con".

inline "cic:/CoRN/ftc/StrongIVT/a'_seq_less_z.con".

inline "cic:/CoRN/ftc/StrongIVT/z_less_b'_seq.con".

inline "cic:/CoRN/ftc/StrongIVT/a'_seq_mon.con".

inline "cic:/CoRN/ftc/StrongIVT/b'_seq_mon.con".

inline "cic:/CoRN/ftc/StrongIVT/a'_seq_b'_seq_dist_n.con".

inline "cic:/CoRN/ftc/StrongIVT/a'_seq_b'_seq_dist.con".

inline "cic:/CoRN/ftc/StrongIVT/a'_seq_Cauchy.con".

inline "cic:/CoRN/ftc/StrongIVT/b'_seq_Cauchy.con".

inline "cic:/CoRN/ftc/StrongIVT/IVT'/xa.con" "IVT'__".

inline "cic:/CoRN/ftc/StrongIVT/IVT'/xb.con" "IVT'__".

inline "cic:/CoRN/ftc/StrongIVT/a'_seq_b'_seq_lim.con".

inline "cic:/CoRN/ftc/StrongIVT/xa'_in_interval.con".

inline "cic:/CoRN/ftc/StrongIVT/IVT'_I.con".

(* UNEXPORTED
End IVT'
*)

(*#* **Other formulations

We now generalize the various statements of the intermediate value
theorem to more widely applicable forms.
*)

inline "cic:/CoRN/ftc/StrongIVT/Weak_IVT.con".

inline "cic:/CoRN/ftc/StrongIVT/IVT_inc.con".

(* UNEXPORTED
Transparent Min.
*)

inline "cic:/CoRN/ftc/StrongIVT/IVT_dec.con".

inline "cic:/CoRN/ftc/StrongIVT/IVT'_inc.con".

(* UNEXPORTED
Transparent Min.
*)

inline "cic:/CoRN/ftc/StrongIVT/IVT'_dec.con".


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

include "CoRN_notation.ma".

(* $Id: StrongIVT.v,v 1.5 2004/04/23 10:01:01 lcf Exp $ *)

include "ftc/WeakIVT.ma".

include "ftc/CalculusTheorems.ma".

(* UNEXPORTED
Section IVT'.
*)

(*#* ** Strong IVT for partial functions

The IVT can be generalized to arbitrary partial functions; in the first
part, we will simply do that, repeating the previous construction.

The same notations and conventions apply as before.
*)

inline "cic:/CoRN/ftc/StrongIVT/a.var".

inline "cic:/CoRN/ftc/StrongIVT/b.var".

inline "cic:/CoRN/ftc/StrongIVT/Hab'.var".

inline "cic:/CoRN/ftc/StrongIVT/Hab.var".

(* begin hide *)

inline "cic:/CoRN/ftc/StrongIVT/I.con".

inline "cic:/CoRN/ftc/StrongIVT/I'.con".

(* end hide *)

inline "cic:/CoRN/ftc/StrongIVT/F.var".

inline "cic:/CoRN/ftc/StrongIVT/contF.var".

(* begin hide *)

inline "cic:/CoRN/ftc/StrongIVT/incF.con".

(* end hide *)

(* begin show *)

inline "cic:/CoRN/ftc/StrongIVT/incrF.var".

(* end show *)

(* begin hide *)

inline "cic:/CoRN/ftc/StrongIVT/Ha.con".

inline "cic:/CoRN/ftc/StrongIVT/Hb.con".

inline "cic:/CoRN/ftc/StrongIVT/HFab'.con".

(* end hide *)

(* begin show *)

inline "cic:/CoRN/ftc/StrongIVT/z.var".

inline "cic:/CoRN/ftc/StrongIVT/Haz.var".

inline "cic:/CoRN/ftc/StrongIVT/Hzb.var".

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

inline "cic:/CoRN/ftc/StrongIVT/xa.con".

inline "cic:/CoRN/ftc/StrongIVT/xb.con".

inline "cic:/CoRN/ftc/StrongIVT/a'_seq_b'_seq_lim.con".

inline "cic:/CoRN/ftc/StrongIVT/xa'_in_interval.con".

inline "cic:/CoRN/ftc/StrongIVT/IVT'_I.con".

(* UNEXPORTED
End IVT'.
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


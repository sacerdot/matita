(**************************************************************************)
(*       ___	                                                            *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||       A.Asperti, C.Sacerdoti Coen,                          *)
(*      ||A||       E.Tassi, S.Zacchiroli                                 *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU Lesser General Public License Version 2.1         *)
(*                                                                        *)
(**************************************************************************)

include "Z/compare.ma".
include "Z/times.ma".
include "nat/iteration2.ma".

(* a fraction is a list of Z-coefficients for primes, in natural
order. The last coefficient must eventually be different from 0 *)

axiom Q:Type.
axiom Qopp:Q \to Q.
axiom Qinv:Q \to Q.
axiom Qplus:Q \to Q \to Q.
axiom Qtimes:Q \to Q \to Q.
axiom QO:Q.
axiom Q1:Q.
axiom Qlt:Q \to Q \to Prop.

axiom num: Q \to Z.
axiom denom: Q \to nat.
axiom frac: Z \to nat \to Q.

(* plus *)
axiom symmetric_Qplus: symmetric ? Qplus.
axiom associative_Qplus: associative ? Qplus.
axiom Qplus_QO: \forall q:Q.Qplus q QO = q.
axiom Qplus_Qopp: \forall q:Q.Qplus q (Qopp q) = QO.

(* times *)
axiom symmetric_Qtimes: symmetric ? Qtimes.
axiom associative_Qtimes: associative ? Qtimes.
axiom Qtimes_Q1: \forall q:Q.Qtimes q Q1 = q.
axiom Qtimes_Qinv: \forall q:Q.q \neq QO \to Qtimes q (Qinv q) = Q1.

(* plus times *)
axiom distributive_Qtimes_Qplus: distributive ? Qtimes Qplus.

axiom frac_num_denom: \forall q.frac (num q) (denom q) = q.
axiom frac_O: \forall n. frac O n = QO.
axiom frac_n: \forall n. n\neq O \to frac n n = Q1.
axiom Qtimes_frac : \forall a,b,c,d.Qtimes (frac a b) (frac c d) =
(frac (a * c) (b * d)). 
alias symbol "times" = "natural times".
axiom Qplus_frac:\forall a,b,c,d.Qplus (frac a b) (frac c d) =
(frac (a * d + b * c) (b * d)).
axiom Qlt_fracl:\forall a,b,c,d.Qlt (frac a b) (frac c d) \to
a*d \lt b*c. 
axiom Qlt_fracr:\forall a,b,c,d.a*d \lt b*c \to Qlt (frac a b) (frac c d).
axiom frac_Qopp: \forall a,b.Qopp(frac a b) = frac (Zopp a) b.
axiom frac_Qinv1: \forall a,b:nat.Qinv(frac a b) = frac b a.
axiom frac_Qinv2: \forall a,b:nat.Qinv(frac (Zopp a) b) = frac (Zopp b) a.

definition sigma_Q \def \lambda n,p,f.iter_p_gen n p Q f QO Qplus. 
(*
theorem geometric: \forall q.\exists k. 
Qlt q (sigma_Q k (\lambda x.true) (\lambda x. frac (S O) x)).
*)  

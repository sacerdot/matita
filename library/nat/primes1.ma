(**************************************************************************)
(*       ___	                                                            *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||       A.Asperti, C.Sacerdoti Coen,                          *)
(*      ||A||       E.Tassi, S.Zacchiroli                                 *)
(*      \   /                                                             *)
(*       \ /        Matita is distributed under the terms of the          *)
(*        v         GNU Lesser General Public License Version 2.1         *)
(*                                                                        *)
(**************************************************************************)

set "baseuri" "cic:/matita/nat/primes1".

include "datatypes/constructors.ma".
include "nat/primes.ma".

(* p is just an upper bound, acc is an accumulator *)
let rec n_divides_aux p n m acc \def
  match n \mod m with
  [ O \Rightarrow 
    match p with
      [ O \Rightarrow pair nat nat acc n
      | (S p) \Rightarrow n_divides_aux p (n / m) m (S acc)]
  | (S a) \Rightarrow pair nat nat acc n].

(* n_divides n m = <q,r> if m divides n q times, with remainder r *)
definition n_divides \def \lambda n,m:nat.n_divides_aux n n m O.

(*
theorem n_divides_to_Prop: \forall n,m,p,a. 
  match n_divides_aux p n m a with
  [ (pair q r) \Rightarrow n = m \sup a *r].
intros.
apply nat_case (n \mod m). *)


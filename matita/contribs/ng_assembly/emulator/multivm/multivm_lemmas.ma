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

(* ********************************************************************** *)
(*                          Progetto FreeScale                            *)
(*                                                                        *)
(*   Sviluppato da: Ing. Cosimo Oliboni, oliboni@cs.unibo.it              *)
(*   Sviluppo: 2008-2010                                                  *)
(*                                                                        *)
(* ********************************************************************** *)

include "emulator/multivm/multivm.ma".
include "common/nat_lemmas.ma".

nlemma breakpoint_err : ∀m,t,s,err,n.execute m t (TickERR ? s err) n = TickERR ? s err.
 #m; #t; #s; #err; #n;
 ncases n;
 ##[ ##2: #n1; ##]
 nnormalize;
 napply refl_eq.
nqed.

nlemma breakpoint_susp : ∀m,t,s,susp,n.execute m t (TickSUSP ? s susp) n = TickSUSP ? s susp.
 #m; #t; #s; #susp; #n;
 ncases n;
 ##[ ##2: #n1; ##]
 nnormalize;
 napply refl_eq.
nqed.

nlemma breakpoint :
 ∀m,t,n1,n2,s. execute m t s (n1 + n2) = execute m t (execute m t s n1) n2.
 #m; #t; #n1;
 nelim n1;
 ##[ ##1: nnormalize; #n2; #s; ncases s; nnormalize; ##[ ##1,2: #x ##] #y; napply refl_eq
 ##| ##2: #n3; #H; #n2; #s; ncases s;
          ##[ ##1: #x; #y; nnormalize; nrewrite > (breakpoint_err m t x y n2); napply refl_eq
          ##| ##2: #x; #y; nnormalize; nrewrite > (breakpoint_susp m t x y n2); napply refl_eq
          ##| ##3: #x; nrewrite > (Sn_p_n_to_S_npn n3 n2);
                   nchange with ((execute m t (tick m t x) (n3+n2)) =
                                 (execute m t (execute m t (tick m t x) n3) n2));
                   nrewrite > (H n2 (tick m t x));
                   napply refl_eq
          ##]
 ##]
nqed.

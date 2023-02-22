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

include "nat/order.ma".
include "datatypes/bool.ma".

naxiom decompose1: ¬(lt O O).
naxiom decompose2: ∀n. ¬(lt (S n) O).

ndefinition ltb: nat → nat → bool.
 #n; nelim n
  [ #m; ncases m
    [ napply false
    | #m'; napply true ]
##| #n'; #Hn'; #m; ncases m
    [ napply false
    | #m'; ncases (Hn' m')
       [ napply true
       | napply false]##]
nqed.

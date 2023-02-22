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

universe constraint Type[0] < Type[1].
universe constraint Type[1] < Type[2].
universe constraint CProp[0] < CProp[1].
universe constraint CProp[1] < CProp[2].
universe constraint Type[0] ≤ CProp[0].
universe constraint CProp[0] ≤ Type[0].
universe constraint Type[1] ≤ CProp[1].
universe constraint CProp[1] ≤ Type[1].
universe constraint Type[2] ≤ CProp[2].
universe constraint CProp[2] ≤ Type[2].
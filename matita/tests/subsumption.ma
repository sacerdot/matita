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
include "logic/equality.ma".

ntheorem foo :
  ∀U : Type.
  ∀a : U.
 ∀b : U.
  ∀f : U → U → U.
  ∀g : U → U → U.
  ∀H : ∀x.g x a = g a x.
  ∃y,z. f (g y b) y = f (g z a) a.
#U. #a. #b. #f. #g. #H.
napply (ex_intro ????);
##[ ##2: napply (ex_intro ????);
         ##[ ##2: nauto by H. ##| ##skip ##] ##| ##skip ##] nqed. 
         
ntheorem foo1 :
  ∀U : Type.
  ∀a : U.
 ∀b : U.
  ∀f : U → U → U.
  ∀g : U → U → U.
  ∀H : ∀x.g x a = g a x.
  ∃y,z. f y (g y b) = f a (g z a).
#U. #a. #b. #f. #g. #H.
napply (ex_intro ????);
##[ ##2: napply (ex_intro ????);
         ##[ ##2: nauto by H. ##| ##skip ##] ##| ##skip ##] nqed.
         
ntheorem foo2 :
  ∀U : Type.
  ∀a : U.
 ∀b : U.
  ∀f : U → U → U.
  ∀g : U → U → U.
  ∀H : ∀x.g x a = g a x.
  ∃y,z. f (g z a) (g y b) = f (g y b) (g z a).
#U. #a. #b. #f. #g. #H.
napply (ex_intro ????);
##[ ##2: napply (ex_intro ????);
         ##[ ##2: nauto by H. ##| ##skip ##] ##| ##skip ##] nqed.
                   
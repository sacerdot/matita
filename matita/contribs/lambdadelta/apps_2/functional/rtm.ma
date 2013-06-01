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

include "basic_2/grammar/term_vector.ma".
include "basic_2/grammar/genv.ma".
include "apps_2/functional/notation.ma".

(* REDUCTION AND TYPE MACHINE ***********************************************)

(* machine local environment *)
inductive xenv: Type[0] ≝
| XAtom: xenv                                    (* empty *)
| XQuad: xenv → bind2 → nat → xenv → term → xenv (* entry *)
.

interpretation "atom (ext. local environment)"
   'Star = XAtom.

interpretation "environment construction (quad)"
   'DxItem4 L I u K V = (XQuad L I u K V).

(* machine stack *)
definition stack: Type[0] ≝ list2 xenv term.

(* machine status *)
record rtm: Type[0] ≝
{ rg: genv;  (* global environment *)
  ru: nat;   (* current de Bruijn's level *)
  re: xenv;  (* extended local environment *)
  rs: stack; (* application stack *)
  rt: term   (* code *)
}.

(* initial state *)
definition rtm_i: genv → term → rtm ≝
                  λG,T. mk_rtm G 0 (⋆) (⟠) T.

(* update code *)
definition rtm_t: rtm → term → rtm ≝
                  λM,T. match M with
                  [ mk_rtm G u E _ _ ⇒ mk_rtm G u E (⟠) T
                  ].

(* update closure *)
definition rtm_u: rtm → xenv → term → rtm ≝
                  λM,E,T. match M with
                  [ mk_rtm G u _ _ _ ⇒ mk_rtm G u E (⟠) T
                  ].

(* get global environment *)
definition rtm_g: rtm → genv ≝
                  λM. match M with
                  [ mk_rtm G _ _ _ _ ⇒ G
                  ].

(* get local reference level *)
definition rtm_l: rtm → nat ≝
                  λM. match M with
                  [ mk_rtm _ u E _ _ ⇒ match E with
                     [ XAtom           ⇒ u
                     | XQuad _ _ u _ _ ⇒ u
                     ]
                  ].

(* get stack *)
definition rtm_s: rtm → stack ≝
                  λM. match M with
                  [ mk_rtm _ _ _ S _ ⇒ S
                  ].

(* get code *)
definition rtm_c: rtm → term ≝
                  λM. match M with
                  [ mk_rtm _ _ _ _ T ⇒ T
                  ].

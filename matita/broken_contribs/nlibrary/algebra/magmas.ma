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

include "sets/sets.ma".

nrecord magma_type : Type[1] ≝
 { mtcarr:> setoid;
   op: unary_morphism mtcarr (unary_morph_setoid mtcarr mtcarr)
 }.

nrecord magma (A: magma_type) : Type[1] ≝
 { mcarr:> ext_powerclass A;
   op_closed: ∀x,y. x ∈ mcarr → y ∈ mcarr → op A x y ∈ mcarr
 }.

alias symbol "hint_decl" = "hint_decl_Type2".
unification hint 0 ≔ 
  A : ? ⊢ carr1 (ext_powerclass_setoid A) ≡ ext_powerclass A. 

(*
ncoercion mcarr' : ∀A. ∀M: magma A. carr1 (qpowerclass_setoid (mtcarr A))
 ≝ λA.λM: magma A.mcarr ? M
 on _M: magma ? to carr1 (qpowerclass_setoid (mtcarr ?)).
*)

nrecord magma_morphism_type (A,B: magma_type) : Type[0] ≝
 { mmcarr:> unary_morphism A B;
   mmprop: ∀x,y:A. mmcarr (op ? x y) = op … (mmcarr x) (mmcarr y)
 }.

nrecord magma_morphism (A) (B) (Ma: magma A) (Mb: magma B) : Type[0] ≝
 { mmmcarr:> magma_morphism_type A B;
   mmclosed: ∀x:A. x ∈ mcarr ? Ma → mmmcarr x ∈ mcarr ? Mb
 }.

(*
ndefinition mm_image:
 ∀A,B. ∀Ma: magma A. ∀Mb: magma B. magma_morphism … Ma Mb → magma B.
 #A; #B; #Ma; #Mb; #f;
 napply mk_magma
  [ napply (image … f Ma)
  | #x; #y; nwhd in ⊢ (% → % → ?); *; #x0; *; #Hx0; #Hx1; *; #y0; *; #Hy0; #Hy1; nwhd;
    napply ex_intro
     [ napply (op … x0 y0) 
     | napply conj
        [ napply op_closed; nassumption
        | nrewrite < Hx1;
          nrewrite < Hy1;
          napply (mmprop … f)]##]
nqed.

ndefinition mm_counter_image:
 ∀A,B. ∀Ma: magma A. ∀Mb: magma B. magma_morphism … Ma Mb → magma A.
  #A; #B; #Ma; #Mb; #f;
  napply mk_magma
   [ napply (counter_image … f Mb)
   | #x; #y; nwhd in ⊢ (% → % → ?); *; #x0; *; #Hx0; #Hx1; *; #y0; *; #Hy0; #Hy1; nwhd;
     napply ex_intro
      [ napply (op … x0 y0)
      | napply conj
         [ napply op_closed; nassumption
         | nrewrite < Hx1;
           nrewrite < Hy1;
           napply (mmprop … f)]##]
nqed.
*)

ndefinition m_intersect: ∀A. magma A → magma A → magma A.
 #A; #M1; #M2;
 napply (mk_magma …)
  [ napply (intersect_is_ext_morph ? M1 M2)
  | #x; #y; nwhd in ⊢ (% → % → %); *; #Hx1; #Hx2; *; #Hy1; #Hy2;
    napply conj; napply op_closed; nassumption ]
nqed.
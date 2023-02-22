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

ninductive unit: Type[0] ≝ k: unit.

ninductive bool: unit → Type[0] ≝ true : bool k | false : bool k.

nlemma foo: true = false → False. #H; ndestruct;
nqed.

(* nlemma prova : ∀T:Type[0].∀a,b:T.∀e:a = b.
               ∀P:∀x,y:T.x=y→Prop.P a a (refl T a) → P a b e.
#T;#a;#b;#e;#P;#H;
nrewrite < e;*)

ninductive I1 : Type[0] ≝
| k1 : I1.

ninductive I2 : I1 → Type[0] ≝
| k2 : ∀x.I2 x.

ninductive I3 : ∀x:I1.I2 x → Type[0] ≝
| k3 : ∀x,y.I3 x y.

ninductive I4 : ∀x,y.I3 x y → Type[0] ≝
| k4 : ∀x,y.∀z:I3 x y.I4 x y z.

(*alias id "eq" = "cic:/matita/ng/logic/equality/eq.ind(1,0,2)".
alias id "refl" = "cic:/matita/ng/logic/equality/eq.con(0,1,2)".*)

ninductive II : Type[0] ≝
| kII1 : ∀x,y,z.∀w:I4 x y z.II
| kII2 : ∀x,y,z.∀w:I4 x y z.II.

(* nlemma foo : ∀a,b,c,d,e,f,g,h. kII1 a b c d = kII2 e f g h → True.
#a;#b;#c;#d;#e;#f;#g;#h;#H;
ndiscriminate H;
nqed. *)

nlemma faof : ∀a,b,c,d,e,f,g,h.∀Heq:kII1 a b c d = kII1 e f g h.
              ∀P:(∀a,b,c,d.kII1 a b c d = kII1 e f g h → Prop).
              P e f g h (refl ??) → P a b c d Heq.
#a;#b;#c;#d;#e;#f;#g;#h;#Heq;#P;#HP;
ndestruct;
napply HP;
nqed.
(* Questo documento fa parte della libreria digitale HELM (http://helm.cs.unibo.it)
   ed è distribuito ai sensi della licenza GNU GPL versione 2
*)

include "ground/arith/pnat_split.ma".
include "canale/albero/riferimento.ma".
include "canale/notazione/discriminatore.ma".

(* Discriminatore per i riferimenti *****************************************)

definition rsplit (X) (Y) (Z) (r) ≝
match r with
[ NRef x ⇒Z @ r
| DRef i ⇒psplit X Y (Z ∘ DRef) i
].

interpretation
  "discriminatore (riferimento)"
  'Discriminatore X r Y Z = (rsplit X Y Z r).

(* Riscritture di base ******************************************************)

lemma rsplit_nref (X) (Y) (Z) (x):
      Z @ NRef x = ❨x❩ Y |❪X❫ Z.
//
qed.

lemma rsplit_unit (X) (Y) (Z):
      Y = ❨⧣𝟏❩ Y |❪X❫ Z.
//
qed.

lemma rsplit_succ (X) (Y) (Z) (i):
      Z @ ⧣i = ❨⧣↑i❩ Y |❪X❫ Z.
//
qed.

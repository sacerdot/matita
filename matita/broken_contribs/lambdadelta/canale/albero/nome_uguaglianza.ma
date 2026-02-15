(* Questo documento fa parte della libreria digitale HELM (http://helm.cs.unibo.it)
   ed è distribuito ai sensi della licenza GNU GPL versione 2
*)

include "ground/arith/pnat_lt_tri.ma".
include "canale/albero/nome.ma".
include "canale/notazione/uguaglianza_computazionale.ma".

(* Uguaglianza computazionale per i nomi ************************************)

definition nuc (X) (x1) (x2) (Y) (Z) ≝
match x1 with
[ Nome p1 ⇒
  match x2 with
  [ Nome p2 ⇒ ptri X p1 p2 Z Y Z
  ]
].

interpretation
  "uguaglianza computazionale (nome)"
  'UguaglianzaComputazionale X x1 x2 Y Z = (nuc X x1 x2 Y Z).

(* Riscritture di base ******************************************************)

lemma nuc_unfold (X) (p1) (p2) (Y) (Z):
      ptri X p1 p2 Z Y Z = ❨!𝗑[p1] ⇔ 𝗑[p2]❩ Y | Z.
//
qed.

(* Riscritture avanzate *****************************************************)

lemma nuc_eq (X) (x) (Y) (Z):
      Y = ❨!x ⇔ x❩ Y |❪X❫ Z.
#X * #p #Y #Z //
qed.

lemma nuc_neq (X) (x1) (x2) (Y) (Z):
      x1 ⧸= x2 → Z = ❨!x1 ⇔ x2❩ Y |❪X❫ Z.
#X * #p1 * #p2 #Y #Z #Hnp
elim (pnat_split_lt_eq_gt p1 p2) #Hp
[ /2 width=1 by ptri_lt/
| elim Hnp -Hnp //
| /2 width=1 by ptri_gt/
]
qed.

(* Questo documento fa parte della libreria digitale HELM (http://helm.cs.unibo.it)
   ed è distribuito ai sensi della licenza GNU GPL versione 2
*)

include "canale/albero/nome_uguaglianza.ma".
include "canale/albero/riferimento.ma".

(* Uguaglianza computazionale per i riferimenti *****************************)

definition ruc (X) (r1) (r2) (Y) (Z) ≝
match r1 with
[ NRef x1 ⇒
  match r2 with
  [ NRef x2 ⇒ ❨!x1 ⇔ x2❩ Y |❪X❫ Z
  | DRef i2 ⇒ Z
  ]
| DRef i1 ⇒
  match r2 with
  [ NRef x2 ⇒ Z
  | DRef i2 ⇒ ptri X i1 i2 Z Y Z 
  ]
].

interpretation
  "uguaglianza computazionale (riferimento)"
  'UguaglianzaComputazionale X r1 r2 Y Z = (ruc X r1 r2 Y Z).

(* Riscritture di base ******************************************************)

lemma ruc_unfold_nref_bi (X) (x1) (x2) (Y) (Z):
      ❨!x1 ⇔ x2❩ Y | Z = ❨!NRef x1 ⇔ NRef x2❩ Y |❪X❫ Z.
//
qed.

lemma ruc_unfold_nref_dref (X) (x1:𝕍) (i2) (Y) (Z):
      Z = ❨!x1 ⇔ ⧣i2❩ Y |❪X❫ Z.
//
qed.

lemma ruc_unfold_dref_nref (X) (i1) (x2:𝕍) (Y) (Z):
      Z = ❨!⧣i1 ⇔ x2❩ Y |❪X❫ Z.
//
qed.

lemma ruc_unfold_dref_bi (X) (i1) (i2) (Y) (Z):
      ptri X i1 i2 Z Y Z = ❨!⧣i1 ⇔ ⧣i2❩ Y | Z.
//
qed.

(* Riscritture avanzate *****************************************************)

lemma ruc_eq (X) (r) (Y) (Z):
      Y = ❨!r ⇔ r❩ Y |❪X❫ Z.
#X * //
qed.

lemma ruc_neq (X) (r1) (r2) (Y) (Z):
      r1 ⧸= r2 → Z = ❨!r1 ⇔ r2❩ Y |❪X❫ Z.
#X * [ #x1 | #i1 ] * [1,3: #x2 |*: #i2 ] #Y #Z #Hnr
[ /3 width=1 by nuc_neq/
| //
| //
| elim (pnat_split_lt_eq_gt i1 i2) #Hi
  [ /2 width=1 by ptri_lt/
  | elim Hnr -Hnr //
  | /2 width=1 by ptri_gt/
  ]
]
qed.

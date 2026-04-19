(* Questo documento fa parte della libreria digitale HELM (http://helm.cs.unibo.it)
   ed è distribuito ai sensi della licenza GNU GPL versione 2
*)

include "canale/albero/nome.ma".
include "canale/notazione/riferimento.ma".

(* Categoria dei riferimenti ************************************************)

(* Nota: un riferimento può essere per nome o per profondità *)
(* Nota: metavariabili riferimento: r, s *)
(* Nota: metavariabili profondità: i, j *)
inductive riferimento: Type[0] ≝
| NRef: (𝕍) → riferimento
| DRef: (ℕ⁺) → riferimento
.

coercion NRef.

interpretation
  "riferimento (Categoria)"
  'CategoriaR = (riferimento).

interpretation
  "profondità (riferimento)"
  'RiferimentoProfondita i = (DRef i).

(* Inversioni di base *******************************************************)

lemma eq_inv_dref_bi (i1) (i2):
      (⧣i1 = ⧣i2) → i1 = i2.
#i1 #i2 #H0 destruct //
qed-.

(* Costruzioni **************************************************************)

lemma neq_nome_riferimento (x1) (x2):
      x1 ⧸=❪𝕍❫ x2 → x1 ⧸=❪ℝ❫ x2.
#x1 #x2 #Hnx #H0 destruct
/2 width=1 by/
qed-.

lemma eq_riferimento_dec (r1) (r2):
      Decidable (r1 =❪ℝ❫ r2).
* [ #x1 | #i1 ] * [1,3: #x2 |*: #i2 ]
[ elim (eq_nome_dec x1 x2) #Hx
  [ /2 width=1 by or_introl/
  | @or_intror #H0 destruct
    /2 width=1 by/
  ]
| @or_intror #H0 destruct
| @or_intror #H0 destruct
| elim (eq_pnat_dec i1 i2) #Hi
  [ /2 width=1 by or_introl/
  | @or_intror #H0 destruct
    /2 width=1 by/
  ]
]
qed-.

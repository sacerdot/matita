(* Questo documento fa parte della libreria digitale HELM (http://helm.cs.unibo.it)
   ed è distribuito ai sensi della licenza GNU GPL versione 2
*)

(* *)
(* Invocazione iniziale: "Pazienza su di me per guadagnare pace e perfezione!" *)

include "ground/arith/pnat.ma".
include "canale/notazione/nomi.ma".

(* Categoria dei nomi *******************************************************)

(* Nota: un nome ha la forma "𝗑[p]" in cui "p ∈ ℕ⁺" *)
(* Nota: metavariabili: x, y, z con grazie *)
inductive nome: Type[0] ≝
| Nome: ℕ⁺ → nome
.

interpretation
  "nome (categoria)"
  'CategoriaV = (nome).

interpretation
  "nome generico (nome)"
  'Nome p = (Nome p).

definition nome_f: 𝕍 ≝
𝗑[↑↑↑↑↑𝟏].

interpretation
  "nome f (nome)"
  'NomeF = (nome_f).

definition nome_g: 𝕍 ≝
𝗑[↑↑↑↑↑↑𝟏].

interpretation
  "nome g (nome)"
  'NomeG = (nome_g).

definition nome_x: 𝕍 ≝
𝗑[↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑𝟏].

interpretation
  "nome x (nome)"
  'NomeX = (nome_x).

definition nome_y: 𝕍 ≝
𝗑[↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑𝟏].

interpretation
  "nome y (nome)"
  'NomeY = (nome_y).

definition nome_z: 𝕍 ≝
𝗑[↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑𝟏].

interpretation
  "nome z (nome)"
  'NomeZ = (nome_z).

(* Costruzioni **************************************************************)

lemma eq_nome_dec (x1) (x2):
      Decidable (x1 =❪𝕍❫ x2).
* #p1 * #p2
elim (eq_pnat_dec p1 p2) #Hp
[ /2 width=1 by or_introl/
| @or_intror #H0 destruct
  /2 width=1 by/
]
qed-.  

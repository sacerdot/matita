(* Questo documento fa parte della libreria digitale HELM (http://helm.cs.unibo.it)
   ed è distribuito ai sensi della licenza GNU GPL versione 2
*)

include "canale/albero/nome.ma".
include "canale/notazione/indicizzazioni.ma".

(* Funzioni di indicizzazione ***********************************************)

(* Nota: indicizzazione diretta e inversa *)
record ix: Type[0] ≝
{ ix_d: 𝕍 → ℕ⁺
; ix_i: ℕ⁺ → 𝕍
; ix_id (x): x = ix_i @ ix_d @ x
; ix_di (p): p = ix_d @ ix_i @ p
}.

interpretation
  "indicizzazione ()"
  'CategoriaIX = (ix).

interpretation
  "funzione diretta (indicizzazione)"
  'SupRightArrowhead f = (ix_d f).

interpretation
  "funzione inversa (indicizzazione)"
  'SupLeftArrowhead f = (ix_i f).

(* Distruzioni di base ******************************************************)

lemma ix_d_inj (f) (x1) (x2):
      f˃ @❪𝕍,ℕ⁺❫ x1 = f˃ @ x2 → x1 = x2.
#f #x1 #x2 #Hx
>(ix_id f x1) >(ix_id f x2) //
qed-.

lemma ix_i_inj (f) (i1) (i2):
      f˂ @ i1 = f˂ @ i2 → i1 = i2.
#f #i1 #i2 #Hi
>(ix_di f i1) >(ix_di f i2) //
qed-.

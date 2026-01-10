(* Questo documento fa parte della libreria digitale HELM (http://helm.cs.unibo.it)
   ed è distribuito ai sensi della licenza GNU GPL versione 2
*)

include "canale/albero/nomi_uguaglianza.ma".
include "canale/albero/termine.ma".
include "canale/notazione/sostituzione.ma".

(* Sostituzione *************************************************************)

rec definition sost (y) (W) (U) on U: 𝕋 ≝
match U with
[ NRef x   ⇒ ❨y ⇔ x❩ W | U
| NAbs x T ⇒ ❨y ⇔ x❩ U | 𝛌x.(sost y W T)
| Appl T V ⇒ (sost y W T)❨sost y W V❩
].

interpretation
  "sostituzione (termine)"
  'Sostituzione y W U = (sost y W U).

(* Riscritture di base ******************************************************)

lemma sost_nref (W:𝕋) (y) (x):
      ❨y ⇔ x❩ W | x = [W / y] x.
//
qed.

lemma sost_nabs (W) (T) (y) (x):
      ❨y ⇔ x❩ 𝛌x.T | 𝛌x.[W / y]T = [W / y] 𝛌x.T.
//
qed.

lemma sost_appl (W) (T) (V) (y):
      ([W / y]T)❨[W / y]V❩ = [W / y] T❨V❩.
//
qed.

(* Riscritture avanzate *****************************************************)

lemma sost_nref_eq (W) (x):
      W = [W / x] x.
//
qed.

lemma sost_nref_neq (W) (y:𝕍) (x):
      y ⧸= x → x =❪𝕋❫ [W / y] x.
/2 width=1 by nuc_neq/
qed.

lemma sost_nabs_eq (W) (T) (x):
      (𝛌x.T) = [W / x] 𝛌x.T.
//
qed.

lemma sost_nabs_neq (W) (T) (y) (x):
      y ⧸= x → 𝛌x.[W / y]T = [W / y] 𝛌x.T.
/2 width=1 by nuc_neq/
qed.

lemma sost_eq (y) (T):
      T = [y / y] T.
#y #T elim T -T
[ #x elim (eq_nome_dec y x) #Hnyx //
  <(sost_nref_neq … Hnyx) //
| #x #T #IH elim (eq_nome_dec y x) #Hnyx //
  <(sost_nabs_neq … Hnyx) //
| #T #V #IHT #IHV
  <sost_appl //
]
qed.

(* Riscritture principali ***************************************************)

(* Nota: primo lemma di sostituzione *)
theorem sost_sost_eq (y) (V2) (V1) (T):
        [[V2 / y]V1 / y] T = [V2 / y] [V1 / y] T.
#y #V2 #V1 #T elim T -T
[ #x elim (eq_nome_dec y x) #Hnyx //
  <(sost_nref_neq … Hnyx)
  <(sost_nref_neq … Hnyx) <(sost_nref_neq … Hnyx) //
| #x #T #IH elim (eq_nome_dec y x) #Hnyx //
  <(sost_nabs_neq … Hnyx)
  <(sost_nabs_neq … Hnyx) <(sost_nabs_neq … Hnyx) //
| #T #V #IHT #IHV
  <sost_appl <sost_appl //
]
qed.

(* Questo documento fa parte della libreria digitale HELM (http://helm.cs.unibo.it)
   ed è distribuito ai sensi della licenza GNU GPL versione 2
*)

include "ground/notation/functions/upspoon_1.ma".
include "canale/albero/riferimento_discriminatore.ma".
include "canale/eminenza/trasformazione_successiva.ma".

(* Spinta dell'aggiornamento ************************************************)

definition upd_spinta (f: ℝ𝕋): ℝ𝕋 ≝
           λr. ❨r❩ (⧣𝟏) | (↑f).

interpretation
  "spinta (aggiornamento)"
  'UpSpoon f = (upd_spinta f).

(* Riscritture di base ******************************************************)

lemma upd_spinta_unfold (f) (r):
      ❨r❩ (⧣𝟏) | (↑f) = (⫯f) @ r.
//
qed.

(* Riscritture avanzate *****************************************************)

lemma upd_spinta_nref (f) (x:𝕍):
      (↑f) @ x =❪ℝ❫ (⫯f) @ x.
//
qed.

lemma upd_spinta_unit (f):
      (⧣𝟏) = (⫯f) @ ⧣𝟏.
//
qed.

lemma upd_spinta_succ (f) (i):
      (↑f) @ (⧣i) = (⫯f) @ ⧣↑i.
//
qed.

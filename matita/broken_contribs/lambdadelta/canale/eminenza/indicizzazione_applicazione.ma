(* Questo documento fa parte della libreria digitale HELM (http://helm.cs.unibo.it)
   ed è distribuito ai sensi della licenza GNU GPL versione 2
*)

include "canale/albero/termine.ma".
include "canale/eminenza/aggiornamento_spinta.ma".
include "canale/eminenza/indicizzazione_spinta.ma".

(* Applicazione dell'indicizzazione *****************************************)

rec definition ixd_appl (f) (U) on U: 𝕋 ≝
match U with
[ Refs r   ⇒ f @ r
| NAbs x T ⇒ (𝛌.(ixd_appl (⫯˃[x]f) T))
| Appl T V ⇒ (ixd_appl f T)❨ixd_appl f V❩
| AAbs T   ⇒ (𝛌.(ixd_appl (⫯f) T))
].

interpretation
  "applicazione (indicizzazione)"
  'AtSharpDx f T = (ixd_appl f T).

(* Riscritture di base ******************************************************)

lemma ixd_appl_refs (f:ℝ𝕋) (r):
      f @ r =❪𝕋❫ f＠⧣˃❨r❩.
//
qed.

lemma ixd_appl_nabs (f) (x) (T):
      (𝛌.(⫯˃[x]f＠⧣˃❨T❩) = f＠⧣˃❨𝛌x.T❩).
//
qed.

lemma ixd_appl_appl (f) (T) (V):
      f＠⧣˃❨T❩❨f＠⧣˃❨V❩❩ = f＠⧣˃❨T❨V❩❩.
//
qed.

lemma ixd_appl_aabs (f) (T):
      (𝛌.(⫯f＠⧣˃❨T❩) = f＠⧣˃❨𝛌.T❩).
//
qed.

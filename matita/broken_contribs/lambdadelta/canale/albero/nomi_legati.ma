(* Questo documento fa parte della libreria digitale HELM (http://helm.cs.unibo.it)
   ed è distribuito ai sensi della licenza GNU GPL versione 2
*)

include "canale/albero/nomi_ap_legati.ma".
include "canale/notazione/condizione_b.ma".

(* Nomi legati **************************************************************)

definition condizione_b0: relation2 (𝕍) (𝕋) ≝
           λ_,_. ⊤.

interpretation
  "nomi legati (condizione)"
  'CondizioneB = (condizione_b0).

interpretation
  "nomi legati (condizione applicata)"
  'CondizioneBAppl x T= (condizione_b0 x T).

interpretation
  "nomi legati (sottoinsieme di nomi)"
  'NomiLegati U = (ap_legati condizione_b0 condizione_b0 U).

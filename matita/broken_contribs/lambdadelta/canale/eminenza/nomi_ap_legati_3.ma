(* Questo documento fa parte della libreria digitale HELM (http://helm.cs.unibo.it)
   ed è distribuito ai sensi della licenza GNU GPL versione 2
*)

include "canale/albero/nomi_liberi.ma".
include "canale/albero/nomi_ap_legati.ma".
include "canale/eminenza/nomi_ap_liberi.ma".
include "canale/notazione/condizione_b.ma".

(* Nomi legati alla portata ristretta ***************************************)

definition condizione_b3_sx: 𝕍 → 𝕍 → 𝒫❨𝕍❩ → relation2 (𝕍) (𝕋) ≝
           λy1,y2,W,x,T. ∧∧ y1 ϵ ℱ[W/y2]T & y1 ⧸=x & y2 ⧸=x.

interpretation
  "nomi legati alla portata ristretta (condizione sinistra)"
  'CondizioneB y1 y2 W = (condizione_b3_sx y1 y2 W).

interpretation
  "nomi legati alla portata ristretta (condizione sinistra applicata)"
  'CondizioneBAppl y1 y2 W x T= (condizione_b3_sx y1 y2 W x T).

definition condizione_b3_dx: 𝕍 → relation2 (𝕍) (𝕋) ≝
           λy2,x,T. y2 ⧸=x.

interpretation
  "nomi legati alla portata ristretta (condizione destra)"
  'CondizioneB y2 = (condizione_b3_dx y2).

interpretation
  "nomi legati alla portata ristretta (condizione destra applicata)"
  'CondizioneBAppl y2 x T= (condizione_b3_dx y2 x T).

(* Nota: nomi legati in U diversi da y e con y libero nella portata ... *)
interpretation
  "nomi legati alla portata ristretta (sottoinsieme di nomi)"
  'NomiLegati y1 y2 W U = (ap_legati (condizione_b3_sx y1 y2 W) (condizione_b3_dx y2) U).

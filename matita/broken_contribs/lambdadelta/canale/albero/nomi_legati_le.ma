(* Questo documento fa parte della libreria digitale HELM (http://helm.cs.unibo.it)
   ed è distribuito ai sensi della licenza GNU GPL versione 2
*)

include "canale/albero/nomi_ap_legati_le.ma".
include "canale/albero/nomi_legati.ma".

(* Nomi legati **************************************************************)

(* Costruzioni con l'inclusione *********************************************)

lemma legati_nabs_ge (x) (T):
      ❴x❵ ∪ ℬT ⊆ ℬ𝛌x.T.
/2 width=1 by ap_legati_nabs_ge/
qed.

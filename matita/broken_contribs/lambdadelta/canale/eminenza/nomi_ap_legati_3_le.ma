(* Questo documento fa parte della libreria digitale HELM (http://helm.cs.unibo.it)
   ed è distribuito ai sensi della licenza GNU GPL versione 2
*)

include "canale/albero/nomi_ap_legati_le.ma".
include "canale/eminenza/nomi_ap_legati_3.ma".

(* Nomi legati alla portata ristretta ***************************************)

(* Costruzioni con l'inclusione *********************************************)

lemma ap_legati_3_nabs_ge_sx (y1) (y2) (W) (x) (T):
      y1 ϵ ℱ[W/y2]T → y1 ⧸=x → y2 ⧸= x → ❴x❵ ⊆ ℬ[y1,y2,W]𝛌x.T.
#y1 #y2 #W #x #T #Hy1 #Hny1x #Hny2x
/3 width=1 by ap_legati_nabs_ge_sx, and3_intro/
qed.

lemma ap_legati_3_nabs_ge_dx (y1) (y2) (W) (x) (T):
      y2 ⧸= x → ℬ[y1,y2,W]T ⊆ ℬ[y1,y2,W]𝛌x.T.
#y1 #y2 #W #x #T #Hny2x
/3 width=1 by ap_legati_nabs_ge_dx/
qed.

lemma ap_legati_3_nabs_inv_le (y1) (y2) (W) (x) (T) (U):
      (y1 ϵ ℱ[W/y2]T → y1 ⧸=x → y2 ⧸= x → ❴x❵ ⊆ U) →
      (y2 ⧸= x → ℬ[y1,y2,W]T ⊆ U) →
      ℬ[y1,y2,W]𝛌x.T ⊆ U.
#y1 #y2 #W #x #T #U #H1 #H2
@subset_le_or_sx
@subset_rest_le_gen [ * ]
/2 width=1 by/
qed.

(* Questo documento fa parte della libreria digitale HELM (http://helm.cs.unibo.it)
   ed è distribuito ai sensi della licenza GNU GPL versione 2
*)

include "canale/albero/nomi_ap_legati_le.ma".
include "canale/eminenza/nomi_ap_legati_1.ma".

(* Nomi legati alla portata *************************************************)

(* Costruzioni con l'inclusione *********************************************)

lemma ap_legati_1_nabs_ge_sx (y) (x) (T):
      y ⧸= x → y ϵ ℱT → ❴x❵ ⊆ ℬ[y]𝛌x.T.
#y #x #T #Hnyx #Hy
/3 width=1 by ap_legati_nabs_ge_sx, conj/
qed.

lemma ap_legati_1_nabs_ge_dx (y) (x) (T):
      ℬ[y]T ⊆ ℬ[y]𝛌x.T.
#y #x #T
/2 width=1 by ap_legati_nabs_ge_dx/
qed.

lemma ap_legati_1_nabs_ge (y) (x) (T):
      y ⧸= x → y ϵ ℱT → ❴x❵ ∪ ℬ[y]T ⊆ ℬ[y]𝛌x.T.
#y #x #T #Hnyx #Hy
/3 width=1 by ap_legati_nabs_ge, conj/
qed.

lemma ap_legati_1_nabs_inv_le (y) (x) (T) (U):
      (y ⧸= x → y ϵ ℱT → ❴x❵ ⊆ U) →
      ℬ[y]T ⊆ U →
      ℬ[y]𝛌x.T ⊆ U.
#y #x #T #U #H1 #H2
@subset_le_or_sx
@subset_rest_le_gen // * #Hnyx #Hy
/2 width=1 by/
qed.

lemma ap_legati_1_nabs_eq_le (x) (T):
      ℬ[x]𝛌x.T ⊆ ℬ[x]T.
#x #T
@ap_legati_1_nabs_inv_le [| // ] * //
qed.

lemma ap_legati_1_nabs_non_libero_le (y) (x) (T):
      y ⧸ϵ ℱT → ℬ[y]𝛌x.T ⊆ ℬ[y]T.
#y #x #T #Hny
@ap_legati_1_nabs_inv_le [| // ] #_ #Hy
elim Hny -Hny //
qed.

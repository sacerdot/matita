(* Questo documento fa parte della libreria digitale HELM (http://helm.cs.unibo.it)
   ed è distribuito ai sensi della licenza GNU GPL versione 2
*)

include "ground/subsets/subset_or_le.ma".
include "ground/subsets/subset_rest_le.ma".
include "canale/albero/nomi_ap_legati.ma".

(* Nomi legati alla portata *************************************************)

(* Costruzioni con l'inclusione *********************************************)

lemma ap_legati_nabs_ge_sx (R1) (R2) (x) (T):
      R1 x T → ❴x❵ ⊆ ℬ[R1,R2]𝛌x.T.
#R1 #R2 #x #T #HR1 #HR2 <ap_legati_nabs
/4 width=1 by subset_rest_ge_refl, subset_or_in_sx/
qed.

lemma ap_legati_nabs_ge_dx (R1) (R2) (x) (T):
      R2 x T → ℬ[R1,R2]T ⊆ ℬ[R1,R2]𝛌x.T.
#R1 #R2 #x #T #HR1 #HR2 <ap_legati_nabs
/4 width=1 by subset_rest_ge_refl, subset_or_in_dx/
qed.

lemma ap_legati_nabs_le (R1) (R2) (x) (T):
      ℬ[R1,R2]𝛌x.T ⊆ ❴x❵ ∪ ℬ[R1,R2]T.
#R1 #R2 #x #T <ap_legati_nabs
@subset_or_le_repl //
qed.

lemma ap_legati_nabs_ge (R1) (R2) (x) (T):
      R1 x T → R2 x T → ❴x❵ ∪ ℬ[R1,R2]T ⊆ ℬ[R1,R2]𝛌x.T.
#R1 #R2 #x #T #HR1 #HR2 <ap_legati_nabs
@subset_or_le_repl
/2 width=1 by subset_rest_ge_refl/
qed.

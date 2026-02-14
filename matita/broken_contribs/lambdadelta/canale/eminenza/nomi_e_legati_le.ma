(* Questo documento fa parte della libreria digitale HELM (http://helm.cs.unibo.it)
   ed è distribuito ai sensi della licenza GNU GPL versione 2
*)

include "ground/subsets/subset_or_le.ma".
include "ground/subsets/subset_rest_le.ma".
include "canale/eminenza/nomi_e_legati.ma".

(* Nomi ∃-legati ************************************************************)

(* Costruzioni con l'inclusione *********************************************)

lemma e_legati_nabs_ge (y) (x) (T):
      ℬ﹖[y]T ⊆ ℬ﹖[y]𝛌x.T.
/2 width=1 by subset_or_in_dx/
qed.

lemma e_legati_nabs_libero_ge (y) (x) (T):
      y ⧸= x → y ϵ ℱT → ❴x❵ ⊆ ℬ﹖[y]𝛌x.T.
#y #x #T #Hy #Hny <e_legati_nabs
/4 width=1 by subset_rest_ge_refl, subset_le_or_dx_refl_sx/
qed.

lemma e_legati_nabs_libero_le (y) (x) (T):
      ℬ﹖[y]𝛌x.T ⊆ ❴x❵ ∪ ℬ﹖[y]T.
#y #x #T <e_legati_nabs
@subset_or_le_repl //
@(subset_le_trans … @ subset_rest_le_refl …) //
qed.

lemma e_legati_nabs_eq_le (x) (T):
      ℬ﹖[x]𝛌x.T ⊆ ℬ﹖[x]T.
#x #T <e_legati_nabs
/3 width=4 by subset_nrest_le, subset_le_or_sx_refl_dx/
qed.

lemma e_legati_nabs_non_libero_le (y) (x) (T):
      y ⧸ϵ ℱT → ℬ﹖[y]𝛌x.T ⊆ ℬ﹖[y]T.
#y #x #T #Hny <e_legati_nabs
@subset_le_or_sx_refl_dx
@(subset_le_trans … @ subset_rest_le_refl …)
/2 width=4 by subset_rest_le/
qed.

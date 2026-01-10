(* Questo documento fa parte della libreria digitale HELM (http://helm.cs.unibo.it)
   ed è distribuito ai sensi della licenza GNU GPL versione 2
*)

include "ground/subsets/subset_le.ma".
include "canale/eminenza/nomi_leganti.ma".

(* Nomi leganti *************************************************************)

(* Costruzioni con l'inclusione *********************************************)

lemma leganti_nabs_libero_ge (y) (x) (T):
      y ϵ ℱT → ❴x❵ ∪ ℬ[y]T ⊆ ℬ[y]𝛌x.T.
#y #x #T #Hy #z #Hz
/3 width=1 by subset_or_in_sx, conj/
qed.

lemma leganti_nabs_libero_le (y) (x) (T):
      y ϵ ℱT → ℬ[y]𝛌x.T ⊆ ❴x❵ ∪ ℬ[y]T.
#y #x #T #Hy #z * * #H1z #H2z //
elim H1z -H1z -H2z //
qed.

lemma leganti_nabs_nlibero_ge (y) (x) (T):
      y ⧸ϵ ℱT → ℬ[y]T ⊆ ℬ[y]𝛌x.T.
#y #x #T #Hy #z #Hz
/3 width=1 by subset_or_in_dx, conj/
qed.

lemma leganti_nabs_nlibero_le (y) (x) (T):
      y ⧸ϵ ℱT → ℬ[y]𝛌x.T ⊆ ℬ[y]T.
#y #x #T #Hny #z * * #H1z #H2z //
elim Hny -Hny -H2z //
qed.

(* Costruzioni avanzate con l'inclusione ************************************)

lemma leganti_nabs_ge (y) (x) (T):
      ℬ[y]T ⊆ ℬ[y]𝛌x.T.
#y #x #T elim (in_liberi_dec T y) #Hy
[ @(subset_le_trans ????? (leganti_nabs_libero_ge … Hy)) -Hy
  /2 width=1 by subset_or_in_dx/
| /3 width=1 by leganti_nabs_nlibero_ge/
]
qed.

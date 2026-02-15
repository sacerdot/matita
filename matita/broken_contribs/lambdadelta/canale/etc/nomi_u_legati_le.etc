(* Questo documento fa parte della libreria digitale HELM (http://helm.cs.unibo.it)
   ed è distribuito ai sensi della licenza GNU GPL versione 2
*)

include "ground/subsets/subset_le.ma".
include "canale/eminenza/nomi_u_legati.ma".

(* Nomi ∃-legati ************************************************************)

(* Costruzioni con l'inclusione *********************************************)

lemma u_legati_nabs_ge (y) (x) (T):
      ℬ﹗[y]T ⊆ ℬ﹗[y]𝛌x.T.
/2 width=1 by subset_or_in_dx/
qed.

lemma u_legati_nabs_libero_ge (y) (x) (T):
      y ϵ ℱT → y ⧸= x → ❴x❵ ⊆ ℬ﹗[y]𝛌x.T.
#y #x #T #Hy #Hny #z #Hz
>(subset_in_inv_single ??? Hz) -z
/3 width=1 by subset_or_in_sx, and3_intro/
qed.

lemma u_legati_nabs_libero_le (y) (x) (T):
      ℬ﹗[y]𝛌x.T ⊆ ❴x❵ ∪ ℬ﹗[y]T.
#y #x #T #z *
[ * #Hy #Hny #H0 destruct
  /2 width=1 by subset_or_in_sx/
| /2 width=1 by subset_or_in_dx/
]
qed.

lemma u_legati_nabs_nlibero_le (y) (x) (T):
      y ⧸ϵ ℱT → ℬ﹗[y]𝛌x.T ⊆ ℬ﹗[y]T.
#y #x #T #Hny #z *
[ * #H0 #_ #_
  elim Hny -Hny //
| //
]
qed.

lemma u_legati_nabs_eq_le (x) (T):
      ℬ﹗[x]𝛌x.T ⊆ ℬ﹗[x]T.
#x #T #z *
[ * #_ #H0 #_ elim H0 -H0 //
| //
]
qed.

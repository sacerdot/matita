(* Questo documento fa parte della libreria digitale HELM (http://helm.cs.unibo.it)
   ed è distribuito ai sensi della licenza GNU GPL versione 2
*)

include "ground/subsets/subset_or.ma".
include "ground/subsets/subset_nimply.ma".
include "ground/subsets/subset_listed_1.ma".
include "canale/albero/termine.ma".
include "canale/notazione/nomi_liberi.ma".

(* Nomi liberi **************************************************************)

rec definition liberi (U) on U: 𝒫❨𝕍❩ ≝
match U with
[ NRef x   ⇒ ❴x❵
| NAbs x T ⇒ (liberi T) ⧵ ❴x❵
| Appl T V ⇒ (liberi T) ∪ (liberi V)
].

interpretation
  "nomi liberi (sottoinsieme di nomi)"
  'NomiLiberi T = (liberi T).

(* Riscritture **************************************************************)

lemma liberi_nref (x:𝕍): ❴x❵ = ℱx.
//
qed.

lemma liberi_nabs (x) (T): ℱT ⧵ ❴x❵ = ℱ𝛌x.T.
//
qed.

lemma liberi_appl (T) (V): ℱT ∪ ℱV = ℱT❨V❩.
//
qed.

(* Costruzioni avanzate *****************************************************)

lemma in_liberi_dec (T) (y):
      Decidable (y ϵ ℱT).
#T elim T -T
[ #x #y <liberi_nref
  /3 width=1 by eq_nome_dec, subset_in_single_dec/
| #x #T #IH #y <liberi_nabs
  /4 width=1 by eq_nome_dec, subset_in_single_dec, subset_in_nimp_dec/
| #T #V #IHT #IHV #y <liberi_appl
  /2 width=1 by subset_in_or_dec/
]
qed-.

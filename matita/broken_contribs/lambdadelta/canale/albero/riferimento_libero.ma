(* Questo documento fa parte della libreria digitale HELM (http://helm.cs.unibo.it)
   ed è distribuito ai sensi della licenza GNU GPL versione 2
*)

include "ground/subsets/subset_listed_1.ma".
include "canale/albero/riferimento.ma".
include "canale/notazione/nomi_liberi.ma".

(* Riferimento libero *******************************************************)

definition libero (r): 𝒫❨𝕍❩ ≝
match r with
[ NRef x ⇒ ❴x❵
| DRef _ ⇒ (Ⓕ)
].

interpretation
  "nome libero (sottoinsieme di nomi)"
  'NomiLiberi r = (libero r).

(* Riscritture **************************************************************)

lemma libero_nref (x:𝕍): ❴x❵ = ℱx.
//
qed.

lemma libero_dref (i): Ⓕ = ℱ⧣i.
//
qed.

(* Inversioni avanzate ******************************************************)

lemma in_libero_inv_gen (x) (r):
      x ϵℱr → x =❪ℝ❫ r.
#y *
[ #x <libero_nref #H0
  >(subset_in_inv_single ??? H0) -y //
| #i <libero_dref #H0
  elim (subset_nin_inv_empty ?? H0)
]
qed-.

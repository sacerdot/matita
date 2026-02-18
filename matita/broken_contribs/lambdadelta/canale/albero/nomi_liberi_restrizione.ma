(* Questo documento fa parte della libreria digitale HELM (http://helm.cs.unibo.it)
   ed è distribuito ai sensi della licenza GNU GPL versione 2
*)

include "ground/subsets/subset_rest_le.ma".
include "canale/albero/nomi_liberi.ma".

(* Restrizione con nomi liberi **********************************************)

lemma liberi_rest_refs_le (A) (y) (r:ℝ) (u:𝒫❨A❩): (**)
      ❨yϵ(liberi r)❩u ⊆ ❨y=❪ℝ❫r❩u.
#A #y #r #u
@subset_rest_le_gen #Hy
@(subset_rest_le_inv_gen … @ subset_le_refl …)
/2 width=1 by in_libero_inv_gen/
qed.

lemma liberi_rest_refs_ge (A) (y:𝕍) (r) (u:𝒫❨A❩): (**)
      ❨y=❪ℝ❫r❩u ⊆ ❨yϵ(liberi r)❩u.
#A #y #r #u
@subset_rest_le_gen #H0 destruct
@(subset_rest_le_inv_gen … @ subset_le_refl …) //
qed.

lemma liberi_rest_nabs_le (A) (y) (x) (T) (u:𝒫❨A❩): (**)
      ❨yϵℱ𝛌x.T❩u ⊆ ❨y⧸=x❩❨yϵℱT❩u.
#A #y #x #T #u #a <liberi_nabs * * #Hy #Hny #Ha
lapply (subset_nin_inv_single ??? Hny) -Hny #Hny
/3 width=1 by subset_and_in/
qed.

lemma liberi_rest_nabs_ge (A) (y) (x) (T) (u:𝒫❨A❩): (**)
      ❨y⧸=x❩❨yϵℱT❩u ⊆ ❨yϵℱ𝛌x.T❩u.
#A #y #x #T #u #a <liberi_nabs * #Hny * #Hy #Ha
lapply (subset_nin_single ??? Hny) -Hny #Hny
/4 width=1 by subset_and_in, subset_in_nimp/
qed.

lemma liberi_rest_appl_le (A) (y) (T) (V) (u:𝒫❨A❩): (**)
      ❨yϵℱT❨V❩❩u ⊆ (❨yϵℱT❩u) ∪ (❨yϵℱV❩u).
#A #y #T #V #u #a <liberi_appl * * #Hy #Ha
/3 width=1 by subset_and_in, subset_or_in_dx, subset_or_in_sx/
qed.

lemma liberi_rest_appl_ge (A) (y) (T) (V) (u:𝒫❨A❩): (**)
      (❨yϵℱT❩u) ∪ (❨yϵℱV❩u) ⊆ ❨yϵℱT❨V❩❩u.
#A #y #T #V #u #a <liberi_appl * * #Hy #Ha
/3 width=1 by subset_and_in, subset_or_in_dx, subset_or_in_sx/
qed.

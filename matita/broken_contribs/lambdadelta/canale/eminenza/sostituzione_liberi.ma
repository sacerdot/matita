(* Questo documento fa parte della libreria digitale HELM (http://helm.cs.unibo.it)
   ed è distribuito ai sensi della licenza GNU GPL versione 2
*)

include "ground/subsets/subset_nimply_ol_le.ma".
include "ground/subsets/subset_nimply_or_le.ma".
include "ground/subsets/subset_listed_ol_1.ma".
include "canale/albero/nomi_liberi.ma".
include "canale/eminenza/sostituzione.ma".

(* Sostituzione *************************************************************)

(* Riscritture con nomi liberi **********************************************)

lemma sost_non_libero (y) (V) (T):
      y ⧸ϵ ℱT → T = [V/y]T.
#y #V #T elim T -T
[ #r elim (eq_riferimento_dec y r) #Hnyr destruct
  [ <liberi_nref #Hny
    elim Hny -Hny //
  | /2 width=1 by sost_refs_neq/
  ]
| #x #T #IH <liberi_nabs #Hny
  elim (eq_nome_dec y x) #Hnyx //
  <sost_nabs_neq //
  <IH -IH //
  /5 width=1 by subset_in_inv_single, subset_in_nimp/
| #T #V #IHT #IHV <liberi_appl #Hny
  <sost_appl <IHT -IHT
   [ <IHV -IHV //
     /3 width=1 by subset_or_in_dx/
   | /3 width=1 by subset_or_in_sx/
   ]
| #T #IH <liberi_aabs #Hny
  <sost_aabs <IH //
]
qed.

lemma liberi_sost_le_non_libero (x) (V) (T):
      x ⧸ϵ ℱT → ℱ[V/x]T ⊆ ℱT ⧵ ❴x❵.
#x #V #T #Hx
<(sost_non_libero … Hx)
/3 width=5 by subset_nol_inv_single_dx, subset_le_nimp_dx_refl_sx_fwd/
qed.

(* Costruzioni coi nomi liberi **********************************************)

lemma liberi_sost_ge_dx (x) (V) (T):
      ℱT ⧵ ❴x❵ ⊆ ℱ[V/x]T.
#y #W #T elim T -T
[ #r elim (eq_riferimento_dec y r) #Hnyr destruct
  [ <liberi_nref
    @(subset_le_trans … @ subset_le_nimp_refl_empty …) //
  | <(sost_refs_neq … Hnyr) -Hnyr //
  ]
| #x #T #IH <liberi_nabs
  elim (eq_nome_dec y x) #Hnyx destruct
  [ <sost_nabs_eq <liberi_nabs //
  | <(sost_nabs_neq … Hnyx) -Hnyx <liberi_nabs
    @(subset_le_trans … @ subset_le_nimp_comm_dx …)
    /2 width=5 by subset_le_nimp_bi/
  ]
| #T #V #IHT #IHV <liberi_appl <sost_appl <liberi_appl
  @(subset_le_trans … @ subset_le_nimp_or_sx …)
  /2 width=5 by subset_or_le_repl/
| #T #IH <liberi_aabs <sost_aabs <liberi_aabs //
]
qed.

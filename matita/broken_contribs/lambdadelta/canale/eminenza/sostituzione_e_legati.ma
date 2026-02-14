(* Questo documento fa parte della libreria digitale HELM (http://helm.cs.unibo.it)
   ed è distribuito ai sensi della licenza GNU GPL versione 2
*)

include "ground/subsets/subset_ol.ma".
include "canale/eminenza/nomi_e_legati_le.ma".
include "canale/eminenza/sostituzione_liberi.ma".

(* Sostituzione *************************************************************)

(* Riscritture principali coi nomi ∃-legati *********************************)

(* Nota: terzo lemma della sostituzione sequenziale *)
theorem sost_sost_neq_non_e_legato (y2) (y1) (V2) (V1) (T):
        y2 ⧸= y1 → y1 ⧸ϵ ℱV2 → y2 ⧸ϵ ℬ﹖[y1]T →
        [[V2 / y2]V1 / y1] [V2 / y2] T = [V2 / y2] [V1 / y1] T.
#y2 #y1 #V2 #V1 #T elim T -T
[ #r #Hny21 #Hny1 #_
  elim (eq_riferimento_dec y1 r) #Hny1r destruct
  [ <(sost_refs_neq … @ neq_nome_riferimento … Hny21)
    <sost_refs_eq <sost_refs_eq //
  | <(sost_refs_neq … Hny1r)
    elim (eq_riferimento_dec y2 r) #Hny2r destruct
    [ <sost_refs_eq <sost_non_libero //
    | <(sost_refs_neq … Hny2r) <(sost_refs_neq … Hny1r) //
    ]
  ]
| #x #T #IH #Hny21 #Hny1 #Hny2
  elim (eq_nome_dec y1 x) #Hny1x destruct
  [ <sost_nabs_eq <(sost_nabs_neq … Hny21) <sost_nabs_eq //
  | <(sost_nabs_neq … Hny1x)
    elim (eq_nome_dec y2 x) #Hny2x destruct
    [ <sost_nabs_eq <sost_nabs_eq <(sost_nabs_neq … Hny1x)
      elim (in_liberi_dec T y1) #Hy1
      [ <(sost_non_libero … x) //
        /3 width=1 by e_legati_nabs_libero_ge/
      | <(sost_non_libero … Hy1) <(sost_non_libero … Hy1) //
      ]
    | <(sost_nabs_neq … Hny2x) <(sost_nabs_neq … Hny2x)
      <(sost_nabs_neq … Hny1x) <IH -IH //
      /3 width=1 by subset_or_in_dx/
    ]
  ]
| #T #V #IHT #IHV #Hny21 #Hny1 <e_legati_appl #Hny2
  <sost_appl <sost_appl
  <IHT -IHT /2 width=6 by subset_nin_inv_or_sx/
  <IHV -IHV /2 width=6 by subset_nin_inv_or_dx/
| #T #IH #Hny21 #Hny1 <e_legati_aabs #Hny2
  <sost_aabs <sost_aabs <IH -IH //
]
qed.

(* Nota: lemma della sostituzione sequenziale normale *)
theorem sost_sost_neq_normale (y2) (y1) (V2) (V1) (T):
        y2 ⧸= y1 → y1 ⧸ϵ ℱV2 → ℬ﹖[y1]T ⧸≬ ℱV1 →
        [[V2 / y2]V1 / y1] [V2 / y2] T = [V2 / y2] [V1 / y1] T.
#y2 #y1 #V2 #V1 #T #Hny21 #Hny1 #HN1
elim (in_liberi_dec V1 y2) #Hy2
[ @(sost_sost_neq_non_e_legato … Hny21 Hny1)
  /3 width=3 by subset_ol_i/
| <(sost_non_libero … Hy2)
  @(sost_sost_neq_non_libero … Hny21 Hny1) //
]
qed.

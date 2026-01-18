(* Questo documento fa parte della libreria digitale HELM (http://helm.cs.unibo.it)
   ed è distribuito ai sensi della licenza GNU GPL versione 2
*)

include "canale/eminenza/barendregt.ma".
include "canale/eminenza/sostituzione.ma".

(* Sostituzione *************************************************************)

(* Riscritture con nomi liberi **********************************************)

lemma sost_non_libero (y) (V) (T):
      y ⧸ϵ ℱT → T = [V / y] T.
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

(* Riscritture principali con barendregt ************************************)

(* Nota: secondo lemma di sostituzione *)
theorem sost_sost_neq (y2) (y1) (V2) (V1) (T):
        y2 ⧸= y1 → y1 ⧸ϵ ℱV2 → ℬ[y1]T ⧸≬ ℱV1 →
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
| #x #T #IH #Hny21 #Hny1 #HB1
  elim (eq_nome_dec y1 x) #Hny1x destruct
  [ <sost_nabs_eq <(sost_nabs_neq … Hny21) <sost_nabs_eq //
  | <(sost_nabs_neq … Hny1x)
    elim (eq_nome_dec y2 x) #Hny2x destruct
    [ <sost_nabs_eq <sost_nabs_eq <(sost_nabs_neq … Hny1x)
      elim (in_liberi_dec T y1) #Hy1
      [ <(sost_non_libero … x) //
       /5 width=3 by leganti_nabs_libero_ge, subset_or_in_sx, subset_ol_i/
      | <(sost_non_libero … Hy1) <(sost_non_libero … Hy1) //
      ]
    | <(sost_nabs_neq … Hny2x) <(sost_nabs_neq … Hny2x)
      <(sost_nabs_neq … Hny1x) <IH -IH //
      #H0 @HB1 -HB1 @(subset_ol_le_repl … H0) //
    ]
  ]
| #T #V #IHT #IHV #Hny21 #Hny1 <leganti_appl #HB1
  <sost_appl <sost_appl <IHT -IHT //
  [ <IHV -IHV // ]
  #H0 @HB1 -HB1 @(subset_ol_le_repl … H0) //
| #T #IH #Hny21 #Hny1 <leganti_aabs #HB1
  <sost_aabs <sost_aabs <IH -IH //
]
qed.

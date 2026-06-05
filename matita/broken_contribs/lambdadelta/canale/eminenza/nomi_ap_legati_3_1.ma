(* Questo documento fa parte della libreria digitale HELM (http://helm.cs.unibo.it)
   ed è distribuito ai sensi della licenza GNU GPL versione 2
*)

include "canale/eminenza/nomi_ap_liberi_le.ma".
include "canale/eminenza/nomi_ap_legati_3.ma".

(* Nomi legati alla portata ristretta ***************************************)

(* Distruzioni coi legati alla portata **************************************)

lemma in_ap_legati_3_des_gen (y) (y1) (y2) (W) (U):
      y ϵ ℬ[y1,y2,W]U →
      ∧∧ y1 ϵ W & y1 ⧸=y & y ϵ ℬ[y2]U.
#y #y1 #y2 #W #U elim U -U
[ #r <ap_legati_refs #H0
  elim (subset_nin_inv_empty ?? H0)
| #x #T #IH * #H0
  elim (subset_rest_inv_gen ???? H0) -H0
  [ * #Hy1 #Hny1x #Hny2x #Hy
    lapply (subset_in_inv_single ??? Hy) -Hy #H0 destruct
    lapply (ap_liberi_le … Hy1) -Hy1 #Hy1
    elim (subset_rest_inv_gen ???? Hy1) -Hy1 #Hy2 #Hy1
    @(and3_intro … Hy1 Hny1x)
    @(ap_legati_1_nabs_ge_sx … Hny2x) //
  | #Hny2x #Hy
    elim (IH Hy) -IH -Hy #Hy1 #Hny1 #Hy
    @(and3_intro … Hy1 Hny1)
    /2 width=1 by ap_legati_1_nabs_ge_dx/
  ]
| #T #V #IHT #IHV <ap_legati_appl <ap_legati_appl * #Hy
  [ elim (IHT Hy) -IHT -IHV -Hy #Hy1 #Hny1 #Hy
    @(and3_intro … Hy1 Hny1)
    /2 width=1 by subset_or_in_sx/
  | elim (IHV Hy) -IHT -IHV -Hy #Hy1 #Hny1 #Hy
    @(and3_intro … Hy1 Hny1)
    /2 width=1 by subset_or_in_dx/
  ]
| #T #IH <ap_legati_aabs <ap_legati_aabs #Hy
  /2 width=1 by/
]
qed-.

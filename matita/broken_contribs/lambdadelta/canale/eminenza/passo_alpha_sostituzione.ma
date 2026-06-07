(* Questo documento fa parte della libreria digitale HELM (http://helm.cs.unibo.it)
   ed è distribuito ai sensi della licenza GNU GPL versione 2
*)

include "canale/eminenza/nomi_ap_legati_3_1.ma".
include "canale/eminenza/sostituzione_ap_legati_3.ma".
include "canale/eminenza/passo_alpha_liberi.ma".

(* Passo alpha **************************************************************)

(* Distruzioni avanzate con la sostituzione *********************************)

lemma astep_des_sost_sx_side (x1) (x2:𝕍) (T1) (X2):
      (⦋x2/x1⦌T1 ⪰α X2) → x1 ⧸= x2 → x1 ⧸ϵ ℬ[x2]X2 → X2 = ⦋x2/x1⦌⦋x1/x2⦌X2.
#x1 #x2 #T1 #X2 #H0 #Hnx12
@sost_sost_inversa #Hnx1
lapply (astep_liberi_ge … H0 … Hnx1) -X2 #Hnx1
/3 width=2 by in_liberi_sost_des_refs_refl/
qed-.

lemma astep_des_sost_sx_main (x1) (x2:𝕍):
      x1 ⧸= x2 → ∀T1,X2:𝕋. x2 ⧸ϵ ℱT1 → x2 ⧸ϵ ℬ[x1]T1 → x1 ⧸ϵ ℬ[x2]X2 →
      (⦋x2/x1⦌T1 ⪰α X2) → T1 ⪰α ⦋x1/x2⦌X2.
#x1 #x2 #Hnx12 #T1 elim T1 -T1
[ #r #X2 #H1nx2 #_ #_ -Hnx12
  elim (eq_riferimento_dec x1 r) #Hnx1r destruct
  [ <sost_refs_eq #H0
    lapply (astep_inv_refs_sx … H0) -H0 #H0 destruct
    <sost_refs_eq //
  | <(sost_refs_neq … Hnx1r) #H0
    lapply (astep_inv_refs_sx … H0) -H0 #H0 destruct
    <sost_refs_neq /2 width=1 by/
  ]
| #x #T1 #IH #X2 #H1nx2 #H2nx2 #Hnx1
  elim (in_liberi_dec (𝛌x.T1) x1) #Hx1
  [ lapply (in_liberi_sost_refl … H2nx2 Hx1) #Hx2 #H0
    lapply (astep_liberi_le … H0 … Hx2) #H2x2
    elim (in_liberi_inv_nabs … Hx1) -Hx1 #Hx1 #H0nx1
    <(sost_nabs_neq … H0nx1) in H0; #H0
    elim (astep_inv_nabst_sx … H0) -H0 *
    [ #Y2 #HY2 #H0 destruct -Hx2 -Hnx12 -H0nx1
      elim (in_liberi_inv_nabs … H2x2) -H2x2 #_ #H0nx2
      <(sost_nabs_neq … H0nx2)
      /5 width=1 by astep_nabs, in_liberi_nabs, ap_legati_nabs_ge_dx/
    | #Y2 #y #Hnxy #H1ny #H2ny #HY2 #H0 destruct
      <(sost_nabs_neq … H0nx1) in Hx2; #Hx2
      elim (in_liberi_inv_nabs … Hx2) -Hx2 #_ #H0nx2
      elim (in_liberi_inv_nabs … H2x2) -H2x2 #Hx2 #Hnx2y
      lapply (in_inv_liberi_sost_nref_neq … Hnx2y Hx2) -Hx2 #Hx2
      <(sost_nabs_neq … Hnx2y)
      <sost_sost_neq_non_libero
      [2,3,4: /3 width=5 by subset_nin_single/ ] -Hnx2y
      @(astep_step … Hnxy)
      [ #H0 @H1ny -H1ny -H0nx1
        @(in_inv_liberi_sost_nref_neq … H0) -H0 #H0 destruct
        @Hnx1 -Hnx1
        @ap_legati_1_nabs_ge [1,3: /2 width=1 by subset_or_in_sx/ ]
        @liberi_sost_ge_dx
        /3 width=5 by subset_nin_single, subset_in_nimp/
      | #H0 elim (ap_legati_1_sost_le … H0) -H0 #H0
        [ lapply (subset_rest_le_refl ???? H0) -H0 <ap_legati_refs #H0
          /2 width=3 by subset_nin_inv_empty/
        | elim (in_ap_legati_3_des_gen … H0) -H0 <liberi_nref #H0 #_ #_
          lapply (subset_in_inv_single ??? H0) -H0 #H0 destruct
          /2 width=1 by/
        | /2 width=1 by/
        ]
      | @(IH … HY2) -IH -HY2
        [ /3 width=1 by in_liberi_nabs/
        | /3 width=1 by ap_legati_1_nabs_ge_dx/
        | /4 width=1 by ap_legati_1_sost_ge_dx, ap_legati_1_nabs_ge_dx/
        ]
      ]
    ]
  | -IH -H2nx2 -Hnx1 -Hnx12
    <(sost_non_libero … Hx1) -Hx1 #H0
    <sost_non_libero [ // ]
    /3 width=3 by astep_liberi_ge/
  ]
| #V1 #T1 #IHV #IHT #X2 #H1nx2 #H2nx2 #Hnx1 #H0
  elim (subset_nin_inv_or ???? H1nx2) -H1nx2 #H1nx2V #H1nx2T
  elim (subset_nin_inv_or ???? H2nx2) -H2nx2 #H2nx2V #H2nx2T
  elim (astep_inv_appl_sx … H0) -H0 #V2 #T2 #HV12 #HT12 #H0 destruct
  elim (subset_nin_inv_or ???? Hnx1) -Hnx1 #Hnx1V #Hnx1T
  /3 width=1 by astep_appl/
| #T1 #IH #X2 #H1nx2 #H2nx2 #Hnx1 #H0
  elim (astep_inv_aabs_sx … H0) -H0 #T2 #HT12 #H0 destruct
  /4 width=1 by astep_aabs/
]
qed-.

(* Questo documento fa parte della libreria digitale HELM (http://helm.cs.unibo.it)
   ed è distribuito ai sensi della licenza GNU GPL versione 2
*)

include "ground/xoa/ex_3_1.ma".
include "ground/subsets/subset_or_ol.ma".
include "ground/subsets/subset_listed_ol.ma".
include "canale/eminenza/nomi_ap_legati_3_1.ma".
include "canale/eminenza/sostituzione_ap_legati_3.ma".
include "canale/eminenza/passo_alpha_liberi.ma".

(* Passo alpha **************************************************************)

lemma in_liberi_sost_refl (x2) (x1) (T):
      x2 ⧸ϵ ℬ[x1]T → x1 ϵ ℱT → x2 ϵ ℱ⦋x2/x1⦌T.
#x2 #x1 #T #Hnx2 #Hx1
/5 width=1 by liberi_sost_ge_sx, ap_liberi_ge, subset_rest_ge_refl, subset_in_nimp/
qed.

(* Inversioni avanzate ******************************************************)

lemma astep_des_sost_sx_side (x1) (x2:𝕍) (T1) (X2):
      (⦋x2/x1⦌T1 ⪰α X2) → x1 ⧸= x2 → x1 ⧸ϵ ℬ[x2]X2 → X2 = ⦋x2/x1⦌⦋x1/x2⦌X2.
#x1 #x2 #T1 #X2 #H0 #Hnx12
@sost_sost_inversa #Hnx1
lapply (astep_liberi_ge … H0 … Hnx1) -X2 #Hnx1
/3 width=2 by in_liberi_sost_des_refs_refl/
qed-.

lemma in_inv_liberi_sost_nref_neq (x1:𝕍) (x2) (y) (Y2:𝕋):
      y ⧸= x1 → y ϵ ℱ⦋x1/x2⦌Y2 → y ϵ ℱY2.
#x1 #x2 #y #Y2 #Hnyx1 #Hy
elim (liberi_sost_le … Hy) -Hy [| * // ] #Hy
lapply (ap_liberi_le … Hy) -Hy #Hy
lapply (subset_rest_le_refl ???? Hy) -Hy #Hy
elim Hnyx1 -Hnyx1
<(subset_in_inv_single ??? Hy) -x1 //
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
      [2,3,4: /3 width=5 by subset_nin_single/ ] -H0nx1 -Hnx2y
      @(astep_step … Hnxy)
      [ #H0 @H1ny -H1ny
        @(in_inv_liberi_sost_nref_neq … H0) -H0 #H0 destruct
        @Hnx1 -Hnx1
        @ap_legati_1_nabs_ge [1,3: /2 width=1 by subset_or_in_sx/ ]
        @liberi_sost_ge_dx
        /3 width=5 by subset_nin_single, subset_in_nimp/
      | #H0 elim (ap_legati_1_sost_le … H0) -H0 #H0
        [ lapply (subset_rest_le_refl ???? H0) -H0 <ap_legati_refs #H0
          /2 width=3 by subset_nin_inv_empty/
        | elim (in_ap_legati_3_des_gen … H0) -H0 #H0 #_ #Hy
        | /2 width=1 by/
        ]
      |
      ]
    ]
  | -IH -H2nx2 -Hnx1 -Hnx12
    <(sost_non_libero … Hx1) -Hx1 #H0
    <sost_non_libero [ // ]
    /3 width=3 by astep_liberi_ge/
  ]
(*

lemma astep_inv_sost_sx (x1) (T1) (x2:𝕍) (X2):
      ∃∃T2.  x2 ⧸ϵ ℬ[x1]T2.
#x1 #T1 elim T1 -T1
[ #r #x2 #X2
  elim (eq_riferimento_dec x1 r) #Hnxr destruct
  [ <sost_refs_eq #H0 #Hnx2 #Hnx1
    lapply (astep_inv_refs_sx … H0) -H0 #H0 destruct
    /3 width=4 by ex3_intro/
  | <(sost_refs_neq … Hnxr) #H0 #Hnx2 #Hnx1
    lapply (astep_inv_refs_sx … H0) -H0 #H0 destruct
    /3 width=4 by ruc_neq, ex3_intro, astep_refs/
  ]
| #x #T1 #IH #x2 #X2
  <sost_nabs_spinta #H0 <ap_legati_nabs #Hnx2 #Hnx1
  elim (subset_nin_inv_or ???? Hnx2) -Hnx2 #H1nx2 #H2nx2
  elim (astep_inv_nabst_sx … H0) -H0 *
  [ #Y2 #HY2 #H0 destruct <ap_legati_nabs in Hnx1; #Hnx1
    elim (subset_nin_inv_or ???? Hnx1) -Hnx1 #H1nx1 #H2nx1
    elim (IH … HY2) -IH -HY2
    [ #T2 #HT12 #HT2 #H0 destruct
      @(ex3_intro … (𝛌x.T2))
      [ /2 width=1 by astep_nabs/
      | <ap_legati_nabs
        @subset_nin_or
        [ @(subset_nin_ge_trans ???? H1nx2)
          @subset_rest_le_repl
          @subset_rest_le_gen #Hx1
          @(subset_rest_le_inv_gen … @ subset_le_refl …)
          /2 width=3 by astep_liberi_ge/
        | elim (eq_nome_dec x1 x) #Hnx1x destruct
          [ @nin_ap_legati_gen #Hnx2x
            (* 1 *)
          | <nuc_neq in HT2; //
          ]
        ]
      | //
      ]
    | elim (eq_nome_dec x1 x) #Hnx1x destruct
      [ /2 width by sestesso_nin_ap_legati/
      | <nuc_neq //
      ]
    | elim (eq_nome_dec x1 x) #Hnx1x destruct
      [ /2 width by sestesso_nin_ap_legati/
      | <nuc_neq //
      ]
    ]
  | (* 2 *)
  ]
| (* 3 *)
| (* 4 *)
]
(*
    @(ex3_intro … (𝛌x.T2))
    [ /2 width=1 by astep_nabs/
    | <ap_legati_nabs
    | <sost_nabs_eq //



  elim (eq_nome_dec x1 x) #Hnx destruct
  [ <sost_nabs_eq #H0 <ap_legati_nabs #Hnx2 #Hnx1
    elim (astep_inv_nabst_sx … H0) -H0 *
    [ #T2 #HT12 #H0 destruct
      @(ex3_intro … (𝛌x.T2))
      [ /2 width=1 by astep_nabs/
      | <ap_legati_nabs
      | <sost_nabs_eq //
(*
      /3 width=6 by _/

      /3 width=5 by astep_nabs, sost_nabs_eq, ex3_2_intro/
    | #T2 #x2 #Hnx12 #H1nx2 #H2nx2 #HT12 #H0 destruct
      @ex3_2_intro
      [3: @astep_riflessiva |1: skip
      |4: @(astep_step … Hnx12 H1nx2 H2nx2 HT12) |2: skip
      | <(sost_nabs_neq … Hnx12)
        <sost_sost_eq
        <(sost_refs_neq … @ neq_nome_riferimento … Hnx12) //
      ]
    ]
  | <(sost_nabs_neq … Hnx1) #H0 #HB
    elim (astep_inv_nabst_sx … H0) -H0 *
    [ #X3 #HX3 #H0 destruct
      elim (IH … HX3) -IH -HX3
      [2: #H0 @HB -HB @(subset_ol_le_repl … H0) // ]
      #V2 #T2 #HV12 #HT12 #H0 destruct
      /3 width=5 by sost_nabs_neq, ex3_2_intro, astep_nabs/
    | #X3 #x2 #Hnx12 #H1nx2 #H2nx2 #HX3 #H0 destruct
      elim (IH … HX3) -IH -HX3
      [2: #H0 @HB -HB @(subset_ol_le_repl … H0) // ]
      #V2 #T2 #HV12 #HT12 #H0 destruct
      elim (eq_nome_dec x x2) #Hnx2 destruct
      [
      | @(ex3_2_intro … HV12)
        [2: @(astep_step … Hnx12 … HT12) |1: skip
        | <(sost_nabs_neq … Hnx2)
          <sost_sost_neq
*)
| #T1 #V1 #IHT #IHV #X2
  <sost_appl #H0 <leganti_appl #HB #HV
  elim (astep_inv_appl_sx … H0) -H0 #X0 #Y0 #HX0 #HY0 #H0 destruct
  lapply (subset_nol_des_or_sx_sx … HB) #HBT
  lapply (subset_nol_des_or_sx_dx … HB) -HB #HBV
  elim (IHT … HX0 HBT HV) -IHT -HX0 -HBT #T2 #HT12 #HBT #H0 destruct
  elim (IHV … HY0 HBV HV) -IHV -HY0 -HBV -HV #V2 #HV12 #HBV #H0 destruct
  /3 width=7 by astep_appl, subset_nol_or_sx, ex3_intro/
| #T1 #IH #X2
  <sost_aabs #H0 <leganti_aabs #HB #HV
  elim (astep_inv_aabs_sx … H0) -H0 #X0 #HX0 #H0 destruct
  elim (IH … HX0 HB HV) -IH -HX0 -HB -HV #T2 #HT12 #HB #H0 destruct
  /3 width=4 by astep_aabs, ex3_intro/
]
*)
*)
(* Costruzioni principali ***************************************************)
(*
theorem astep_transitiva:
        Transitive … astep.
#T1 #T0 #HT10 elim HT10 -T1 -T0
[ //
| #T1 #T0 #x #_ #IH #X2 #H0
  elim (astep_inv_nabst_sx … H0) -H0 *
  [ #T2 #HT02 #H0 destruct
    /3 width=1 by astep_nabs/
  | #T2 #x2 #Hnx #H1nx2 #H2nx2 #HT02 #H0 destruct
    /3 width=1 by astep_step/
  ]
| #T1 #T0 #x1 #x0 #Hnx10 #H1nx0 #H2nx0 #_ #IH #X2 #H0
  elim (astep_inv_nabst_sx … H0) -H0 *
  [ #T2 #HT02 #H0 destruct
*)

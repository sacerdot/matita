(* Questo documento fa parte della libreria digitale HELM (http://helm.cs.unibo.it)
   ed è distribuito ai sensi della licenza GNU GPL versione 2
*)

include "ground/subsets/subset_help.ma".
include "canale/eminenza/nomi_u_legati_le.ma".
include "canale/eminenza/sostituzione_liberi.ma".

(* Sostituzione *************************************************************)

(* Costruzioni avanzate coi nomi liberi *************************************)

axiom subset_le_nimp_and_dx (A) (u:𝒫❨A❩) (v1) (v2): (**)
      u ⧵ (v1 ∩ v2) ⊆ (u ⧵ v1) ∪ (u ⧵ v2).
(*
#A #u #v1 #v2 #a * #Ha #H0
*)

axiom subset_ge_nimp_and_dx (A) (u:𝒫❨A❩) (v1) (v2): (**)
      (u ⧵ v1) ∪ (u ⧵ v2) ⊆ u ⧵ (v1 ∩ v2).
(*
#A #u #v1 #v2 #a * * #Ha #Hna
*)


(*
lemma liberi_sost_ge_sx (x) (V) (T):
      x ϵ ℱT → ℱV ⧵ ℬ﹗[x]T ⊆ ℱ[V/x]T.
#y #W #T elim T -T
[ #r #H0 <(in_liberi_inv_refs … H0) -r
  <sost_refs_eq
  /2 width=2 by subset_le_nimp_sx_refl_sx/
| #x #T #IH <liberi_nabs * #Hy #H0
  lapply (subset_nin_inv_single ??? H0) -H0 #Hnyx
  <(sost_nabs_neq … Hnyx) <liberi_nabs
  lapply (u_legati_nabs_libero_ge … Hy Hnyx) -Hnyx #HB1
  lapply (u_legati_nabs_ge y x T) #HB2
  @(subset_le_trans ????? @ subset_le_nimp_bi … (IH Hy) @ subset_le_refl …) -IH -Hy
  @(subset_le_trans ????? @ subset_le_nimp_or_dx …)
  /3 width=5 by subset_le_nimp_bi, subset_le_or_sx/
| #T #V #IHT #IHV <liberi_appl #Hy <u_legati_appl <sost_appl <liberi_appl
  @(subset_le_trans … @ subset_le_nimp_and_dx …)
  
  elim Hy -Hy #Hy [ lapply (IHT ?) | lapply (IHV ?) ] // -IHT -IHV -Hy #HB
  @(subset_le_trans … @ subset_le_trans ????? HB) -HB
  [1,3: @subset_le_nimp_bi ] // (**) (* auto fails *)
| #T #IH <liberi_aabs #Hy <u_legati_aabs <sost_aabs <liberi_aabs
  /2 width=1 by/
]
qed.
*)

lemma liberi_sost_le (x) (V) (T):
      ℱ[V/x]T ⊆ (ℱV ⧵ ℬ﹗[x]T) ∪ (ℱT ⧵ ❴x❵).
#y #W #T elim T -T
[ #r <u_legati_refs
  elim (in_liberi_dec r y) #H0
  [ <(in_liberi_inv_refs … H0) -r <sost_refs_eq
    /3 width=1 by subset_or_in_sx, subset_le_nimp_dx_refl_empty/
  | /3 width=3 by liberi_sost_le_non_libero, subset_dx_le_or/
  ]
| #x #T #IH
  elim (in_liberi_dec (𝛌x.T) y)
  [ <liberi_nabs * #Hy #H0
    lapply (subset_nin_inv_single ??? H0) -H0 #Hnyx
    <(sost_nabs_neq … Hnyx) -Hnyx <liberi_nabs
    @(subset_le_trans … @ subset_le_nimp_bi … IH @ subset_le_refl …) -IH -Hy
    @(subset_le_trans … @ subset_le_nimp_or_sx …)
    @subset_or_le_repl [| // ]
    @(subset_le_trans … @ subset_le_nimp_comm_dx …)
    @(subset_le_trans … @ subset_ge_nimp_or_dx …)
    @subset_le_nimp_bi // (**) (* auto fails *)
  | /3 width=3 by liberi_sost_le_non_libero, subset_dx_le_or/
  ]
| #T #V #IHT #IHV <sost_appl <liberi_appl <u_legati_appl <liberi_appl
  @(subset_le_trans … @ subset_or_le_repl … IHT … IHV) -IHT -IHV
  @(subset_le_trans … @ subset_le_help_1 …)
  @subset_or_le_repl // (**) (* auto fails *)
| #T #IH <sost_aabs <liberi_aabs <u_legati_aabs <liberi_aabs //
]
qed.

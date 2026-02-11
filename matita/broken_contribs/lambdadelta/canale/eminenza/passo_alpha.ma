(* Questo documento fa parte della libreria digitale HELM (http://helm.cs.unibo.it)
   ed è distribuito ai sensi della licenza GNU GPL versione 2
*)

include "ground/xoa/ex_5_2.ma".
include "ground/xoa/ex_3_2.ma".
include "canale/eminenza/nomi_e_legati.ma".
include "canale/eminenza/sostituzione.ma".
include "canale/notazione/conversione_alpha.ma".

(* Passo alpha **************************************************************)

inductive astep: relation2 (𝕋) (𝕋) ≝
| astep_refs (r:ℝ):
  astep r r
| astep_nabs (T1) (T2) (x):
  astep T1 T2 → astep (𝛌x.T1) (𝛌x.T2)
| astep_step (T1) (T2) (x1) (x2):
  x1 ⧸= x2 → x2 ⧸ϵ ℱT2 → x2 ⧸ϵ ℬ﹖[x1]T2 →
  astep T1 T2 → astep (𝛌x1.T1) (𝛌x2.[x2/x1]T2)
| astep_appl (T1) (T2) (V1) (V2):
  astep T1 T2 → astep V1 V2 → astep (T1❨V1❩) (T2❨V2❩)
| astep_aabs (T1) (T2):
  astep T1 T2 → astep (𝛌.T1) (𝛌.T2)
.

interpretation
  "passo alpha (termine)"
  'PassoAlpha T1 T2 = (astep T1 T2).

(* Inversioni di base *******************************************************)

lemma astep_inv_refs_sx (r:ℝ) (X2):
      r ⪰α X2 → r =❪𝕋❫ X2.
#z #X2
@(insert_eq_1 … (Refs z)) #X1 * -X1 -X2
[ //
| #T1 #T2 #x #HT #H0 destruct
| #T1 #T2 #x1 #x2 #_ #_ #_ #_ #H0 destruct
| #T1 #T2 #V1 #V2 #_ #_ #H0 destruct
| #T1 #T2 #_ #H0 destruct
]
qed-.

lemma astep_inv_nabst_sx (T1) (X2) (x):
      (𝛌x.T1) ⪰α X2 →
      ∨∨ ∃∃T2. T1 ⪰α T2 & X2 = 𝛌x.T2
       | ∃∃T2,y. x ⧸= y & y ⧸ϵ ℱ(T2:𝕋) & y ⧸ϵ ℬ﹖[x]T2 &
                 T1 ⪰α T2 & 𝛌y.[y/x]T2 = X2
.
#Z #X2 #z
@(insert_eq_1 … (𝛌z.Z)) #X1 * -X1 -X2
[ #r #H0 destruct
| #T1 #T2 #x #HT #H0 destruct
  /3 width=3 by ex2_intro, or_introl/
| #T1 #T2 #x1 #x2 #Hnx #H1nx #H2nx #HT #H0 destruct
  /3 width=7 by ex5_2_intro, or_intror/
| #T1 #T2 #V1 #V2 #_ #_ #H0 destruct
| #T1 #T2 #_ #H0 destruct
]
qed-.

lemma astep_inv_appl_sx (T1) (V1) (X2):
      T1❨V1❩ ⪰α X2 →
      ∃∃T2,V2. T1 ⪰α T2 & V1 ⪰α V2 & X2 = T2❨V2❩
.
#Z #Y #X2
@(insert_eq_1 … (Z❨Y❩)) #X1 * -X1 -X2
[ #r #H0 destruct
| #T1 #T2 #x #_ #H0 destruct
| #T1 #T2 #x1 #x2 #_ #_ #_ #_ #H0 destruct
| #T1 #T2 #V1 #V2 #HT #HV #H0 destruct
  /2 width=5 by ex3_2_intro/
| #T1 #T2 #_ #H0 destruct
]
qed-.

lemma astep_inv_aabs_sx (T1) (X2):
      (𝛌.T1) ⪰α X2 →
      ∃∃T2. T1 ⪰α T2 & X2 = 𝛌.T2
.
#Z #X2
@(insert_eq_1 … (𝛌.Z)) #X1 * -X1 -X2
[ #r #H0 destruct
| #T1 #T2 #x #_ #H0 destruct
| #T1 #T2 #x1 #x2 #_ #_ #_ #_ #H0 destruct
| #T1 #T2 #V1 #V2 #_ #_ #H0 destruct
| #T1 #T2 #HT #H0 destruct
  /2 width=3 by ex2_intro/
]
qed-.

(* Costruzioni avanzate *****************************************************)

lemma astep_riflessiva:
      reflexive … astep.
#T elim T -T
/3 width=1 by astep_refs, astep_nabs, astep_appl, astep_aabs/
qed.

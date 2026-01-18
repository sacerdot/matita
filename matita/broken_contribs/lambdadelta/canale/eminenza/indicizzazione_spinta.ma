(* Questo documento fa parte della libreria digitale HELM (http://helm.cs.unibo.it)
   ed è distribuito ai sensi della licenza GNU GPL versione 2
*)

include "canale/albero/riferimento_uguaglianza.ma".
include "canale/eminenza/trasformazione_successiva.ma".
include "canale/notazione/indicizzazione.ma".

(* Spinta dell'indicizzazione ***********************************************)

definition ixd_spinta (x:𝕍) (f: ℝ𝕋): ℝ𝕋 ≝
           λr. ❨x ⇔ r❩ (⧣𝟏) | (↑f) @ r.

interpretation
  "spinta (indicizzazione)"
  'UpSpoonDx x f = (ixd_spinta x f).

(* Riscritture di base ******************************************************)

lemma ixd_spinta_unfold (x:𝕍) (f) (r:ℝ):
      ❨x ⇔ r❩ (⧣𝟏) | (↑f) @ r = (⫯˃[x]f) @ r.
//
qed.

(* Riscritture avanzate *****************************************************)

lemma ixd_spinta_eq (x) (f):
      (⧣𝟏) = (⫯˃[x]f) @ x.
/2 width=1 by nuc_eq/
qed.

lemma ixd_spinta_neq (x:𝕍) (f) (r:ℝ):
      x ⧸=❪ℝ❫ r → (↑f) @ r = (⫯˃[x]f) @ r.
/2 width=5 by ruc_neq/
qed.

(* Riscritture principali ***************************************************)

theorem ixd_spinta_iniettiva (x) (f):
        rt_iniettiva f → rt_iniettiva (⫯˃[x]f).
#x #f #Hf #r1 #r2
elim (eq_riferimento_dec x r1) #Hnx1
elim (eq_riferimento_dec x r2) #Hnx2 destruct
[ //
| <ixd_spinta_eq <(ixd_spinta_neq … Hnx2) -Hnx2 #H0
  elim (neq_rt_succ_dx … H0)
| <ixd_spinta_eq <(ixd_spinta_neq … Hnx1) -Hnx1 #H0
  elim (neq_rt_succ_dx … @ sym_eq … H0)
| <(ixd_spinta_neq … Hnx1) <(ixd_spinta_neq … Hnx2) -Hnx1 -Hnx2 #H0
  /2 width=3 by rt_succ_iniettiva/
]
qed.

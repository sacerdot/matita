(* Questo documento fa parte della libreria digitale HELM (http://helm.cs.unibo.it)
   ed è distribuito ai sensi della licenza GNU GPL versione 2
*)

include "canale/eminenza/trasformazione_uniforme.ma".

(* Trasformazione successiva dei riferimenti ********************************)

definition rt_succ (f): ℝ𝕋 ≝
           (𝐮❨⁤𝟏❩∘f).

interpretation
  "successiva (trasformazione)"
  'UpArrow r = (rt_succ r).

(* Riscritture di base ******************************************************)

lemma rt_succ_unfold (f):
      (𝐮❨⁤𝟏❩∘f) = ↑f.
//
qed.

(* Riscritture avanzate *****************************************************)

lemma rt_succ_iniettiva (f):
      rt_iniettiva f → rt_iniettiva @ ↑f.
/3 width=5 by rt_uni_iniettiva, rt_iniettiva_dopo/
qed-.

(* Inversioni avanzate ******************************************************)

lemma neq_rt_succ_dx (f) (r):
      (⧣𝟏) ⧸= (↑f) @ r.
/2 width=2 by neq_rt_uni_unit_dx/
qed-.

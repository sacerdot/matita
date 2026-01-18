(* Questo documento fa parte della libreria digitale HELM (http://helm.cs.unibo.it)
   ed è distribuito ai sensi della licenza GNU GPL versione 2
*)

include "ground/lib/functions.ma".
include "canale/albero/riferimento.ma".
include "canale/notazione/trasformazione.ma".

(* Trasformazione dei riferimenti *******************************************)

definition trasformazione: Type[0] ≝ ℝ → ℝ.

interpretation
  "trasformazione (Categoria)"
  'CategoriaRT = (trasformazione).

definition rt_iniettiva: predicate (ℝ𝕋) ≝
           λf. ∀r1,r2. f @ r1 = f @ r2 → r1 = r2.

(* Riscritture principali ***************************************************)

theorem rt_iniettiva_dopo (g) (f):
        rt_iniettiva g → rt_iniettiva f → rt_iniettiva (g∘f).
#g #f #Hg #Hf #r1 #r2
<apply_dx_unfold <apply_dx_unfold #Hr
/3 width=5 by/
qed-.

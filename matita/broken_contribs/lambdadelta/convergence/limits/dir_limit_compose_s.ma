(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2.
*)

include "convergence/limits/dir_limit_s.ma".
include "convergence/notation/functions/compose_6.ma".

(* LIMIT FOR DIRECTION ******************************************************)

interpretation
   "applied function composition"
   'compose A B C f g x = (compose A B C f g x).

(* Properties with compose **************************************************)

theorem dir_limit_compose (X:ℂ𝟬𝗌) (Y:ℂ𝟬𝗌) (Z:ℂ𝟬𝗌) (f:X→Y) (g:Y→Z) (E) (D) (C):
        (𝗹𝗶𝗺[E] f ≘ D) → (𝗹𝗶𝗺[D] g ≘ C) → (𝗹𝗶𝗺[E] g∘f ≘ C).
#X #Y #Z #f #g #E #D #C #Hf #Hg
lapply (dir_limit_inv_alt … Hf) -Hf #Hf
lapply (dir_limit_inv_alt … Hg) -Hg #Hg
@mk_dir_limit_alt #w #Hw
elim (Hg … Hw) -Hg -Hw #v #Hv #Hg
elim (Hf … Hv) -Hf -Hv #u #Hu #Hf
/4 width=3 by ex2_intro/
qed.

theorem dir_limit_inv_compose (X:ℂ𝟬𝗌) (Y:ℂ𝟬𝗌) (Z:ℂ𝟬𝗌) (f:X→Y) (g:Y→Z) (E) (C):
        (𝗹𝗶𝗺[E] g∘f ≘ C) → (𝗹𝗶𝗺[f＠𝗌❨E❩] g ≘ C).
#X #Y #Z #f #g #E #C #Hgf
lapply (dir_limit_inv_alt … Hgf) -Hgf #Hgf
@mk_dir_limit_alt #w #Hw
elim (Hgf … Hw) -Hgf -Hw #u #Hu #Hgf
lapply (dir_img_s_in ?? f ?? Hu) -Hu #Hfu
@(ex2_intro … Hfu) -Hfu #y * #x #Hx #H0 destruct
/2 width=1 by/
qed-.

theorem dir_limit_inv_compose_inj (X:ℂ𝟬𝗌) (Y:ℂ𝟬𝗌) (Z:ℂ𝟬𝗌) (f:X→Y) (g:Y→Z) (E) (D):
        injective … g → (𝗹𝗶𝗺[E] g∘f ≘ g＠𝗌❨D❩) → (𝗹𝗶𝗺[E] f ≘ D).
#X #Y #Z #f #g #E #D #Hg #Hgf
lapply (dir_limit_inv_alt … Hgf) -Hgf #Hgf
@mk_dir_limit_alt #v #Hv
lapply (dir_img_s_in ?? g ?? Hv) -Hv #Hgv
elim (Hgf … Hgv) -Hgf -Hgv #u #Hu #Hgf
@(ex2_intro … Hu) -Hu #x #Hx
lapply (Hgf … Hx) -Hgf -Hx * #y #Hy #Hgfx
lapply (Hg … Hgfx) -Hg -Hgfx #H0 destruct //
qed-.

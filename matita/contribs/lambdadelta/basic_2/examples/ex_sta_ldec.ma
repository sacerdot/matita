include "basic_2/unfold/lstas.ma".

(* EXAMPLES *****************************************************************)

(* Static type assignment (iterated vs primitive): the declared variable ****)

(* basic_1: we have "L.ⓛⓝ⋆k1.⋆k2⦄ ⊢ #0 • ⓝ⋆k1.⋆k2". *)
theorem sta_ldec: ∀h,G,L,k1,k2. ⦃G, L.ⓛⓝ⋆k1.⋆k2⦄ ⊢ #0 •*[h, 1] ⋆k2.
/3 width=6 by lstas_sort, lstas_succ, lstas_cast, drop_pair/ qed-.

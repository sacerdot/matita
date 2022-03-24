
include "delayed_updating/unwind1/unwind.ma".
(*
include "ground/relocation/tr_compose_compose.ma".
include "ground/relocation/tr_compose_eq.ma".
*)
(* Advanced constructions with proj_rmap and stream_tls *********************)
(* COMMENT
lemma unwind_rmap_tls_d_dx (f) (p) (m) (n):
      ⇂*[m+n]▼[p]f ≗ ⇂*[m]▼[p◖𝗱n]f.
#f #p #m #n
<unwind_rmap_d_dx >nrplus_inj_dx
/2 width=1 by tr_tls_compose_uni_dx/
qed.
*)

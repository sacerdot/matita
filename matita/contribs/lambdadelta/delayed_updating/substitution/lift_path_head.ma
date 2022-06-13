include "delayed_updating/substitution/lift_eq.ma".
include "delayed_updating/syntax/path_head.ma".
include "delayed_updating/syntax/path_reverse.ma".
include "ground/relocation/xap.ma".

axiom tr_xap_succ_pos (f) (n):
      ↑↓(f＠❨↑n❩) = f＠❨↑n❩.

axiom tr_xap_plus (n1) (n2) (f):
      (⇂*[n2]f)＠❨n1❩+f＠❨n2❩ = f＠❨n1+n2❩.

axiom eq_inv_path_empty_head (p) (n):
      (𝐞) = ↳[n]p → 𝟎 = n.

lemma lift_path_head (f) (p) (q) (n):
      pᴿ = ↳[n](pᴿ●qᴿ) →
      ↳[↑[q●p]f＠❨n❩](↑[f](q●p))ᴿ = (↑[↑[q]f]p)ᴿ.
#f #p @(list_ind_rcons … p) -p
[ #q #n #H0
  <(eq_inv_path_empty_head … H0) -H0
  <path_head_zero //
| #p #l #IH #q #n @(nat_ind_succ …n) -n [| #m #_ ]
  [ <reverse_rcons <path_head_zero #H0 destruct
  | cases l [ #n ]
    [ <reverse_rcons <path_head_d_sn #H0
      elim (eq_inv_list_lcons_bi ????? H0) -H0 #_ #H0
      <list_append_assoc <lift_rmap_d_dx <lift_path_d_dx <reverse_rcons
      <tr_xap_succ_pos <path_head_d_sn >tr_xap_succ_pos
      <lift_path_d_dx >lift_rmap_append <reverse_rcons  
      @eq_f2 // <(IH … H0) -IH -H0
      @eq_f2 // <tr_xap_plus //

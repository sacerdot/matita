(* Main constructions *******************************************************)

theorem fbr_coafter_assoc:
        associative … fbr_coafter.
#f3 elim f3 -f3 //
* #f3 #IH
[ #f2 #f1
  <fbr_coafter_next_sn <fbr_coafter_next_sn //
| * // * #f2 * // [|*: #b3 #f3 ]
  <fbr_coafter_push_rcons
  [ <fbr_coafter_next_sn <fbr_coafter_id_dx <fbr_coafter_id_dx //
  | <fbr_coafter_next_sn <fbr_coafter_next_sn <fbr_coafter_push_rcons //
  | <fbr_coafter_push_rcons //
  ]
]
qed.

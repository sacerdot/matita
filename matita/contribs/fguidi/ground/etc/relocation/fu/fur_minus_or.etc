(*
lemma fur_minus_minus_refl (f) (r):
      f-r = f-r-r.
#f elim f -f //
* //
#k #f #IH * // * #r
[ <fur_minus_join_next <fur_minus_join_next
| <fur_minus_join_push <fur_minus_join_push
] <IH -IH //
qed.

lemma fur_minus_minus_comm (f) (r1) (r2):
      f-r1-r2 = f-r2-r1.
#f elim f -f //
* //
#k #f #IH * //
#p1 * //
#p2 <fur_minus_join_pos <fur_minus_join_pos <IH -IH //
qed.
*)

module L = List

module T = Table

(* true for a row specification *)
type 'a atom = 'a * bool * int option * int option

type 'a atoms = 'a atom list

let get_attr concat null a y x =
   let map y x (c, b, x1, x2) = match b, x1, x2 with
      | _    , None, None       -> c
      | false, None, Some c2    -> if x <= c2 then c else null
      | false, Some c1, None    -> if x >= c1 then c else null
      | false, Some c1, Some c2 -> if x >= c1 && x <= c2 then c else null
      | true , None, Some r2    -> if y <= r2 then c else null
      | true , Some r1, None    -> if y >= r1 then c else null
      | true , Some r1, Some r2 -> if y >= r1 && y <= r2 then c else null
   in
   concat (L.map (map y x) a)

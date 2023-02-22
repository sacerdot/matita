let id p = p
 
let register line next =
  let first = !line in
  line := fun k -> first @@ next @@ k

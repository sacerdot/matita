module T = Table

type 'a fold_cb = {
   open_table : 'a -> T.table -> 'a;
   close_table: 'a -> T.table -> 'a;
   map_key    : 'a -> T.key -> 'a;
   open_line  : bool -> 'a -> 'a;
   close_line : bool -> 'a -> 'a;
   open_entry : bool -> 'a -> 'a;   
   close_entry: bool -> 'a -> 'a -> 'a;
}

let map h g f a b = h a (g (f a) b)

let rec fold_table cb a t =
   let a = cb.open_table a t in
   let a = fold_entry cb a t.T.te in
   cb.close_table a t

and fold_entry cb a = function
   | T.Key k        -> cb.map_key a k
   | T.Line (r, ts) ->
      let a = cb.open_line r a in
      let a = List.fold_left (map (cb.close_entry r) (fold_table cb) (cb.open_entry r)) a ts in
      cb.close_line r a

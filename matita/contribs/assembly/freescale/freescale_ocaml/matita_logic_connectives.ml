let true_rec =
(function p -> p)
;;

let true_rect =
(function p -> p)
;;

let false_rec () =
assert false
;;

let false_rect () =
assert false
;;

let and_rec =
(function f -> (f))
;;

let and_rect =
(function f -> (f))
;;


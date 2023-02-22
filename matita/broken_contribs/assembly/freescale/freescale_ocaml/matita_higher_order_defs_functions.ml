let compose =
(function f -> (function g -> (function x -> (f (g x)))))
;;


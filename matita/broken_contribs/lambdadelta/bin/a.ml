let f = "0123456789abcdef"

let r, g, b = 1.0, 0.5, 0.0

let h = 1. /. 2.

let mk_h x = x +. (1. -. x) *. h

let rr, gg, bb = mk_h r, mk_h g, mk_h b 

let mk_f x = 
   let x = int_of_float x in
   print_char f.[x / 16]; print_char f.[x mod 16]  

let _ = 
   mk_f (rr *. 255.); mk_f (gg *. 255.); mk_f (bb *. 255.);
   print_newline ()

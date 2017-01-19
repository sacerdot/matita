let cols = int_of_string (Sys.getenv "COLUMNS")

let hl = ref []

let normal = "\x1B[0m"

let color = "\x1B[32m"

let add s =
   if s = "" then false else
   begin hl := s :: !hl; true end

let rec read ich =
   if Scanf.fscanf ich "%s " add then read ich

let length l s = max l (String.length s)

let split s =
try 
   let i = String.rindex s '.' in
   if i = 0 then s, "" else
   String.sub s 0 i, String.sub s i (String.length s - i)    
with Not_found -> s, ""

let compare s1 s2 =
   let n1, e1 = split s1 in
   let n2, e2 = split s2 in
   let e = String.compare e1 e2 in
   if e = 0 then String.compare n1 n2 else e

let write l c s =
   let pre, post = if List.mem s !hl then color, normal else "", "" in
   let spc = String.make (l - String.length s) ' ' in
   let bol, ret =
       if c = 0 || c = cols then "", l else
       if c + l < cols then " ", c + succ l else "\n", l
   in
   Printf.printf "%s%s%s%s%s" bol pre s post spc;
   ret

let process fname =
   let ich = open_in fname in
   read ich; close_in ich

let help = ""

let main =
   Arg.parse [] process help;
   let files = Sys.readdir "." in
   let l = Array.fold_left length 0 files in
   if cols < l then failwith "window too small";
   Array.fast_sort compare files;
   let c = Array.fold_left (write l) 0 files in
   if 0 < c && c < cols then print_newline ();

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
   Array.fast_sort String.compare files;
   let l = Array.fold_left length 0 files in
   if cols < l then failwith "window too small";
   let c = Array.fold_left (write l) 0 files in
   if 0 < c && c < cols then print_newline ()

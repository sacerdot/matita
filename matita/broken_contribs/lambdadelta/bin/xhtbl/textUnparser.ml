module L = List
module P = Printf
module S = String

module T = Table
module F = Fold

type status = {
   i: int;              (* indentation *)
   out: string -> unit; (* output function *)
}

let home = {
   i = 0; out = print_string
}

let indent st =
   S.make st.i ' '

let add st = {st with i = st.i + 3}

let sub st = {st with i = st.i - 3}

let parent = function
   | None       -> "key"
   | Some false -> "col"
   | Some true  -> "row"

let size ts =
   P.sprintf "(%u, %u); (%u+%u, %u+%u); %s"
      ts.T.y ts.T.x ts.T.rf ts.T.ri ts.T.cf ts.T.ci (parent ts.T.p)

let border tb =
   let str = S.make 4 ' ' in
   if tb.T.w then str.[0] <- 'W';
   if tb.T.n then str.[1] <- 'N';
   if tb.T.e then str.[2] <- 'E';
   if tb.T.s then str.[3] <- 'S';
   str

let css tc =
   P.sprintf "\"%s\"" (S.concat " " tc)

let uri tu tx =
   P.sprintf "@\"%s\" \"%s\"" tu tx

let name tn =
   P.sprintf "$\"%s\"" tn


let text = function
   | T.Plain s              -> P.sprintf "\"%s\"" s
   | T.Link (true, uri, s)  -> P.sprintf "@(\"%s\" \"%s\")" uri s
   | T.Link (false, uri, s) -> P.sprintf "@@(\"%s\" \"%s\")" uri s

let key = function
   | T.Text sl       -> S.concat " ^ " (L.map text sl)
   | T.Glue None     -> "*"
   | T.Glue (Some i) -> P.sprintf "%u" i

let entry = function
   | false -> "column"
   | true  -> "row"

(****************************************************************************)

let open_table st t =
   let str = 
      P.sprintf "%s[{#%u: %s; %s; %s; %s; %s}\n"    
         (indent st) t.T.ti (size t.T.ts) (border t.T.tb) (css t.T.tc) (uri t.T.tu t.T.tx) (name t.T.tn)
   in
   st.out str; add st

let close_table st t =
   let st = sub st in
   let str = P.sprintf "%s]\n" (indent st) in
   st.out str; st

let map_key st k =
   let str = P.sprintf "%s%s\n" (indent st) (key k) in
   st.out str; st
   
let open_line b st =
   let str = P.sprintf "%s%s\n" (indent st) (entry b) in
   st.out str; st

let close_line b st = st

let open_entry b st = st

let close_entry b st sst = st

let cb = {
   F.open_table = open_table; F.close_table = close_table;   
   F.open_line = open_line; F.close_line = close_line;
   F.open_entry = open_entry; F.close_entry = close_entry;
   F.map_key = map_key;
}

let debug t =
   let _ = F.fold_table cb home t in ()

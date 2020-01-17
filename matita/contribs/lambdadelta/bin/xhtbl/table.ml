type css = string list

type uri = string

type ext = string

type anchor = string

type absolute = bool

type size = {
   y : int;         (* first row *)
   x : int;         (* first column *)
   rf: int;         (* finite rows *)
   cf: int;         (* finite columns *)
   ri: int;         (* infinite rows *)
   ci: int;         (* infinite columns *)
   p : bool option; (* parent kind *)
}

type border = {
   n: bool; (* north *)
   s: bool; (* south *)
   e: bool; (* east *)
   w: bool; (* west *)
}

type text = Plain of string
          | Link of absolute * string * string

type key = Text of text list
         | Glue of int option

type table = {
           tn: anchor; (* named anchor *)
   mutable tc: css;    (* css classes *)
   mutable tu: uri;    (* uri *)
   mutable tx: ext;    (* uri extension *)
   mutable ts: size;   (* dimension *)
           tb: border; (* border *)
           te: entry;  (* contents *)
	   ti: int;    (* table identifier *)
}

and entry = Key  of key
          | Line of bool * table list (* true for a row *)

let id =
   let current = ref 0 in
   fun () -> incr current; !current

let no_size = {
   y = 0; x = 0; rf = 0; cf = 0; ri = 0; ci = 0; p = None;
}

let border b = {
   n = b; s = b; e = b; w = b;
}

let mk_key k tc tu tx tn = {
   ts = no_size; tb = border false; te = Key k;
   tc = tc; tu = tu; tx = tx; tn = tn;
   ti = id ();
}

let mk_line b tl tc tu tx tn = {
   ts = no_size; tb = border b; te = Line (b, tl);
   tc = tc; tu = tu; tx = tx; tn = tn;
   ti = id ();
}

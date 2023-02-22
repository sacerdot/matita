module A = Array
module N = Filename

module T = Table

type cell = {
   ck: T.text list; (* contents *)
   cc: T.css;       (* css classes *)
   cu: T.uri;       (* uri *)
   cx: T.ext;       (* extension *)
   cn: T.anchor;    (* named anchor *)   
   cb: T.border;    (* border *)
}

type matrix = {
   r: int;              (* rows *)
   c: int;              (* columns *)
   m: cell array array; (* matrix *)
}

let strand a b = if a = "" then b else a

let empty = {
   ck = []; cc = []; cu = ""; cx = ""; cn = ""; cb = T.border false;
}

let make ts = {
   r = ts.T.rf; c = ts.T.cf;
   m = A.make_matrix ts.T.rf ts.T.cf empty;
}

let set_key m y x kl = 
   m.m.(y).(x) <- {m.m.(y).(x) with ck = kl}

let set_attrs m y x c u e n = 
   m.m.(y).(x) <- {m.m.(y).(x) with
      cc = c @ m.m.(y).(x).cc;
      cu = u ^ m.m.(y).(x).cu;
      cx = m.m.(y).(x).cx ^ e;
      cn = strand m.m.(y).(x).cn n;
   }

let set_west m y x b =
   let c = m.m.(y).(x) in
   let cb = {c.cb with T.w = c.cb.T.w || b.T.w} in 
   m.m.(y).(x) <- {c with cb = cb}

let set_north m y x b =
   let c = m.m.(y).(x) in
   let cb = {c.cb with T.n = c.cb.T.n || b.T.n} in 
   m.m.(y).(x) <- {c with cb = cb}

let set_east m y x b =
   if x < pred m.c then set_west m y (succ x) {b with T.w = b.T.e} else
   let c = m.m.(y).(x) in
   let cb = {c.cb with T.e = c.cb.T.e || b.T.e} in 
   m.m.(y).(x) <- {c with cb = cb}

let set_south m y x b =
   if y < pred m.r then set_north m (succ y) x {b with T.n = b.T.s} else
   let c = m.m.(y).(x) in
   let cb = {c.cb with T.s = c.cb.T.s || b.T.s} in 
   m.m.(y).(x) <- {c with cb = cb}

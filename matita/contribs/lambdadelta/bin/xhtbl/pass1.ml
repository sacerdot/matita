module L = List

module T = Table
module F = Fold

type status = {
   ts: T.size; (* current dimensions *)
   tc: T.css;  (* current class *)
   tu: T.uri;  (* current uri *)
   tx: T.ext;  (* current extension *)
}

let empty = {
   ts = T.no_size; tc = []; tu = ""; tx = ""
}

let init b ts =
   if b then
      {ts with T.ri = max_int; T.ci = 0}
   else
      {ts with T.ri = 0; T.ci = max_int}

let combine b ts1 ts2 =
   if b then 	 
      {ts1 with 
         T.rf = max ts1.T.rf ts2.T.rf; T.ri = min ts1.T.ri ts2.T.ri; 
	 T.cf = ts1.T.cf + ts2.T.cf; T.ci = ts1.T.ci + ts2.T.ci;
      }
   else
      {ts1 with
         T.cf = max ts1.T.cf ts2.T.cf; T.ci = min ts1.T.ci ts2.T.ci;
	 T.rf = ts1.T.rf + ts2.T.rf; T.ri = ts1.T.ri + ts2.T.ri; 
      }

let deinit ts = {ts with
   T.ri = if ts.T.ri = max_int then 0 else ts.T.ri;
   T.ci = if ts.T.ci = max_int then 0 else ts.T.ci;
}

(****************************************************************************)

let open_table st t =
   t.T.tc <- t.T.tc @ st.tc; t.T.tu <- st.tu ^ t.T.tu; t.T.tx <- st.tx ^ t.T.tx; 
   {st with tc = t.T.tc; tu = t.T.tu; tx = t.T.tx}

let close_table st t =
   t.T.ts <- st.ts; st

let map_key st k = 
   let ts = match k, st.ts.T.p with
      | T.Text _     , _          ->
         {st.ts with T.rf = 1; T.cf = 1; T.ri = 0; T.ci = 0}
      | T.Glue None  , _          ->
         {st.ts with T.rf = 0; T.cf = 0; T.ri = 1; T.ci = 1}
      | T.Glue Some g, Some false ->
         {st.ts with T.rf = g; T.cf = 0; T.ri = 0; T.ci = 1}
      | T.Glue Some g, Some true  ->
         {st.ts with T.rf = 0; T.cf = g; T.ri = 1; T.ci = 0}
      | T.Glue Some g, None       ->
         {st.ts with T.rf = g; T.cf = g; T.ri = 0; T.ci = 0}
   in
   {st with ts = ts}

let open_line b st =
   let ts = init b st.ts in
   let ts = {ts with T.rf = 0; T.cf = 0} in
   {st with ts = ts}

let open_entry b st =
   let ts = {st.ts with T.p = Some b} in
   {st with ts = ts}

let close_entry b st sst =
   {st with ts = combine b st.ts sst.ts}

let close_line b st =
   {st with ts = deinit st.ts}

let cb = {
   F.open_table = open_table; F.close_table = close_table;   
   F.open_line = open_line; F.close_line = close_line;
   F.open_entry = open_entry; F.close_entry = close_entry;
   F.map_key = map_key;
}

let process t =
   let st = F.fold_table cb empty t in
   st.ts

module O = Options
module T = Table
module M = Matrix
module F = Fold

type status = {
   ts: T.size;   (* current dimensions *)
   tm: M.matrix; (* current matrix *)
}

let initial t m = {
   ts = {t.T.ts with T.ri = 0; T.ci = 0};
   tm = m;
}

let resize b sts tts = 
   if b then begin (* parent is a row *) 
      if tts.T.rf < sts.T.rf && tts.T.ri = 0 then
         failwith "underful column";
      {tts with T.rf = sts.T.rf; T.cf = tts.T.cf + sts.T.ci * tts.T.ci}
   end else begin (* parent is a column *)
      if tts.T.cf < sts.T.cf && tts.T.ci = 0 then
         failwith "underful row";
      {tts with T.cf = sts.T.cf; T.rf = tts.T.rf + sts.T.ri * tts.T.ri}
   end

let fill b sts tts =
   if b then (* parent is a row *) 
      {sts with T.ri = 
         let rf, ri = sts.T.rf - tts.T.rf, tts.T.ri in
	 if ri = 0 then 0 else
	 if rf mod ri = 0 then rf / ri else
	 failwith "fracted column"
      }
   else (* parent is a column *)
      {sts with T.ci = 
         let cf, ci = sts.T.cf - tts.T.cf, tts.T.ci in
	 if ci = 0 then 0 else
	 if cf mod ci = 0 then cf / ci else
	 failwith "fracted row"
      }

let place b sts tts =
   if b then (* parent is a row *)
      {sts with T.x = sts.T.x + tts.T.cf}
   else (* parent is a column *)
      {sts with T.y = sts.T.y + tts.T.rf}

let set_key st t = match t.T.te with
   | T.Key (T.Text sl) -> M.set_key st.tm t.T.ts.T.y t.T.ts.T.x sl  
   | _                 -> ()

let set_attrs st t =
   let rec aux y x =
      if y >= t.T.ts.T.rf then () else
      if x >= t.T.ts.T.cf then aux (succ y) 0 else begin
	 M.set_attrs st.tm (t.T.ts.T.y + y) (t.T.ts.T.x + x) t.T.tc t.T.tu t.T.tx t.T.tn;
         aux y (succ x)
      end
   in
   match t.T.te with 
      | T.Key _ -> aux 0 0 
      | _       -> ()

let set_borders st t =
   let rec aux_we y =
      if y >= t.T.ts.T.rf then () else begin
	 M.set_west st.tm (t.T.ts.T.y + y) t.T.ts.T.x t.T.tb;
	 if t.T.ts.T.cf > 0 then 
	    M.set_east st.tm (t.T.ts.T.y + y) (t.T.ts.T.x + pred t.T.ts.T.cf) t.T.tb;
         aux_we (succ y)
      end      
   in
   let rec aux_ns x =
      if x >= t.T.ts.T.cf then () else begin
	 M.set_north st.tm t.T.ts.T.y (t.T.ts.T.x + x) t.T.tb;
	 if t.T.ts.T.rf > 0 then 
	    M.set_south st.tm (t.T.ts.T.y + pred t.T.ts.T.rf) (t.T.ts.T.x + x) t.T.tb;
         aux_ns (succ x)
      end      
   in
   match t.T.te with 
      | T.Line (true, _) -> aux_we 0; aux_ns 0
      | _                -> ()

let print st t = 
   if !O.e2 then
      Printf.printf "#%u: (%u+%u, %u+%u) - (%u+%u, %u+%u)\n"
         t.T.ti 
         t.T.ts.T.rf t.T.ts.T.ri 
         t.T.ts.T.cf t.T.ts.T.ci
         st.ts.T.rf st.ts.T.ri
         st.ts.T.cf st.ts.T.ci

(****************************************************************************)

let open_table st t =
   print st t;
   let ts = match t.T.ts.T.p with
      | None   ->
         let ts = fill false st.ts t.T.ts in
         let ts = fill true ts t.T.ts in
	 t.T.ts <- resize false st.ts t.T.ts;
         t.T.ts <- resize true st.ts t.T.ts;
	 ts
      | Some b ->
         let ts = fill b st.ts t.T.ts in
	 t.T.ts <- resize b st.ts t.T.ts;
	 ts
   in
   t.T.ts <- {t.T.ts with T.ri = 0; T.ci = 0; T.x = st.ts.T.x; T.y = st.ts.T.y};
   let ts = {ts with T.rf = t.T.ts.T.rf; T.cf = t.T.ts.T.cf} in
   let st = {st with ts = ts} in 
   print st t; st

let close_table st t =
   set_key st t; set_attrs st t; set_borders st t; st

let map_key st k = st

let open_line b st = st

let open_entry b st = st

let close_entry b st sst =
   let ts = place b st.ts sst.ts in
   {st with ts = ts}

let close_line b st = st

let cb = {
   F.open_table = open_table; F.close_table = close_table;   
   F.open_line = open_line; F.close_line = close_line;
   F.open_entry = open_entry; F.close_entry = close_entry;
   F.map_key = map_key;
}

let process t m =
   let _ = F.fold_table cb (initial t m) t in ()

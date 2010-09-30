module Registry = Helm_registry
module SQL = HSql
module DB = LibraryDb

let tbl = Hashtbl.create 50147
let ord = ref 1
let conf_file = ref "heights.conf.xml"

let rec mesure db_type dbd prim str =
   try 
      let h, p = Hashtbl.find tbl str in 
      if prim then begin
         if p > 0 then Printf.eprintf "Hit %2u: %s\n" (succ p) str;
         Hashtbl.replace tbl str (h, succ p)
      end;
      h
   with Not_found -> 
   let query = 
      Printf.sprintf "SELECT h_occurrence FROM refObj WHERE source = '%s'"
      (SQL.escape db_type dbd str)
   in
   let result = SQL.exec db_type dbd query in
   let f res = match res.(0) with
      | Some str -> mesure db_type dbd false str
      | None     -> assert false 
   in
   let hs = SQL.map result ~f in
   let h = succ (List.fold_left max 0 hs) in
   Printf.printf "%3u %5u %s\n" h !ord str; flush stdout;
   ord := succ !ord;
   let p = if prim then 1 else 0 in
   Hashtbl.add tbl str (h, p); h

let scan_objs db_type dbd =
   let query = "SELECT source FROM objectName" in
   let result = SQL.exec db_type dbd query in
   let f res = match res.(0) with
      | Some str -> ignore (mesure db_type dbd true str)
      | None     -> assert false
   in
   SQL.iter result ~f

let _ =
   Registry.load_from !conf_file;
   let db_type = DB.dbtype_of_string (Registry.get_string "db.type") in
   let db_spec = DB.parse_dbd_conf () in
   let dbd = SQL.quick_connect db_spec in
   scan_objs db_type dbd   

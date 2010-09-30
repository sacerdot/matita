
open Printf

let map =
  (MetadataTypes.library_obj_tbl,`RefObj) ::
  (MetadataTypes.library_sort_tbl,`RefSort) ::
  (MetadataTypes.library_rel_tbl,`RefRel) ::
  (MetadataTypes.library_name_tbl,`ObjectName) ::
  (MetadataTypes.library_hits_tbl,`Hits) ::
  (MetadataTypes.library_count_tbl,`Count) :: []

let usage argv_o =
  prerr_string "\nusage:";
  prerr_string ("\t" ^ argv_o ^ " what tablename[=rename]\n");
  prerr_string ("\t" ^ argv_o ^ " what all\n\n");
  prerr_endline "what:";
  prerr_endline "\tlist\tlist table names";
  prerr_endline "\ttable\toutput SQL regarding tables";
  prerr_endline "\tindex\toutput SQL regarding indexes";
  prerr_endline "\tfill\toutput SQL filling tables (only \"hits\" supported)\n";
  prerr_string "known tables:\n\t";
  List.iter (fun (n,_) -> prerr_string (" " ^ n)) map;
  prerr_endline "\n"

let eq_RE = Str.regexp "="
  
let parse_args l =
  List.map (fun s -> 
    let parts = Str.split eq_RE s in
    let len = List.length parts in
    assert (len = 1 || len = 2);
    if len = 1 then (s,s) else (List.nth parts 0, List.nth parts 1)) 
  l

let destructor_RE = Str.regexp "table_destructor\\(\\|\\.opt\\)$"
  
let am_i_destructor () = 
  try 
    let _ = Str.search_forward destructor_RE Sys.argv.(0) 0 in true
  with Not_found -> false
  
let main () =
  let len = Array.length Sys.argv in
  if len < 3 then 
    begin
    usage Sys.argv.(0);
    exit 1
    end
  else
    begin
      let tab,idx,fill =
        if am_i_destructor () then
          (SqlStatements.drop_tables,
            (fun x ->
              let dbd = HSql.fake_db_for_mysql HSql.Library in     
              SqlStatements.drop_indexes x HSql.Library dbd),
           fun _ t -> [sprintf "DELETE * FROM %s;" t])
        else
          (SqlStatements.create_tables, 
           SqlStatements.create_indexes, 
           SqlStatements.fill_hits)
      in
      let from = 2 in
      let what =
        match Sys.argv.(1) with
        | "list" -> `List
        | "index" -> `Index
        | "table" -> `Table
        | "fill" -> `Fill
        | _ -> failwith "what must be one of \"index\", \"table\", \"fill\""
      in
      let todo = Array.to_list (Array.sub Sys.argv from (len - from)) in
      let todo = match todo with ["all"] -> List.map fst map | todo -> todo in
      let todo = parse_args todo in
      let todo = List.map (fun (x,name) -> name, (List.assoc x map)) todo in
      match what with
      | `Index -> print_endline (String.concat "\n" (idx todo))
      | `Table -> print_endline (String.concat "\n" (tab todo))
      | `Fill ->
          print_endline (String.concat "\n"
            (fill MetadataTypes.library_obj_tbl MetadataTypes.library_hits_tbl))
      | `List -> print_endline (String.concat " " (List.map fst map))
    end

let _ = main ()



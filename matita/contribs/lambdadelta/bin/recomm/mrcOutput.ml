module ET = MrcTypes

let cap = String.capitalize_ascii

let ko b =
  if b then "KO" else "OO"

let write_mli name = 
  let file = name ^ ".mli" in
  if Sys.file_exists file then ()
  else begin
    let och = open_out file in
    close_out och
  end

let write_subst st och subst =
  let iter hd words =
    let lhs = List.map (Printf.sprintf "%S :: ") words in
    let rhs = List.map (Printf.sprintf "%S :: ") hd in
    Printf.fprintf och "  | %stl -> k T.OK (%souts) tl\n"
      (String.concat "" lhs) (String.concat "" rhs)
  in
  match subst with
  | []      -> ()
  | hd :: _ -> List.iter (iter (List.rev hd)) subst 

let write_component st =
  let cmod = "recommGc" ^ st.ET.cmod in
  let och = open_out (cmod ^ ".ml") in
  Printf.fprintf och "module T = RecommTypes\n";
  Printf.fprintf och "module R = Recomm%s\n" (cap st.ET.rmod);
  if st.ET.dmod <> "" then begin
    Printf.fprintf och "module D = Recomm%s\n" (cap st.ET.dmod)
  end;
  Printf.fprintf och "\n";
  Printf.fprintf och "let step k st outs ins =\n";
  if st.ET.para then begin
    Printf.fprintf och "  if st <> T.OO then k st outs ins else\n"
  end else begin
    Printf.fprintf och "  if st = T.KO then k st outs ins else\n"
  end;
  Printf.fprintf och "  match ins with\n";
  List.iter (write_subst st och) st.ET.substs;
  Printf.fprintf och "  | _ -> k T.%s outs ins\n\n" (ko st.ET.optn);
  Printf.fprintf och "let main =\n";
  Printf.fprintf och "  R.register_%s step\n" st.ET.rfun;
  close_out och;
  write_mli cmod

let write_index st =
  let p = float (List.length st.ET.mods) in
  let p =
    if p > 0. then truncate (log10 p) else -1
  in
  let ps = Printf.sprintf "%%0%uu" (succ p) in
  let fmt = Scanf.format_from_string ps "%u" in
  let cmod = Filename.concat st.ET.cdir "recommGc" in
  let och = open_out (cmod ^ ".ml") in
  let iter i name =
    Printf.fprintf och "module G%(%u%) = RecommGc%s\n" fmt (succ i) name
  in
  List.iteri iter st.ET.mods;
  close_out och;
  write_mli cmod

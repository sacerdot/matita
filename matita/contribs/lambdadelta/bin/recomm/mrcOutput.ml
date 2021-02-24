module ET = MrcTypes

let cap = String.capitalize_ascii

let ok b =
  if b then "true" else "ok"

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
    Printf.fprintf och "  | %stl -> k %s (%souts) tl\n"
      (String.concat "" lhs) (ok st.ET.para) (String.concat "" rhs)
  in
  match subst with
  | []      -> ()
  | hd :: _ -> List.iter (iter (List.rev hd)) subst 

let write_component st =
  let cmod = "recommGc" ^ st.ET.cmod in
  let och = open_out (cmod ^ ".ml") in
  if st.ET.dmod <> "" then begin
    Printf.fprintf och "module D = Recomm%s\n\n" (cap st.ET.dmod)
  end;
  Printf.fprintf och "let step k ok outs ins =\n";
  Printf.fprintf och "  if ok then k ok outs ins else\n";
  Printf.fprintf och "  match ins with\n";
  List.iter (write_subst st och) st.ET.substs;
  Printf.fprintf och "  | _ -> k %s outs ins\n\n" (ok st.ET.optn);
  Printf.fprintf och "let main =\n";
  Printf.fprintf och "  Recomm%s.register_%s step\n" (cap st.ET.rmod) st.ET.rfun;
  close_out och;
  write_mli cmod

let write_index st =
  let cmod = Filename.concat st.ET.cdir "recommGc" in
  let och = open_out (cmod ^ ".ml") in
  let iter i name =
    Printf.fprintf och "module G%u = RecommGc%s\n" (succ i) name
  in
  List.iteri iter st.ET.mods;
  close_out och;
  write_mli cmod

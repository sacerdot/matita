module EI = MrcInput
module EO = MrcOutput

let process file =
  if Sys.is_directory file then begin
    let st = EI.read_dir file in
    if st <> EI.read_index file then begin
      Printf.eprintf "indexing: %S\n" file;
      EO.write_index st
    end
  end else if Filename.extension file = ".mrc" then begin
    Printf.eprintf "processing: %S\n" file;
    EO.write_component (EI.read_file file)
  end else begin
    Printf.eprintf "skipping: %S\n" file
  end

let main =
  Arg.parse [
  ] process ""

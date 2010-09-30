(* OPTIONS *)
let tptppath = ref "./";;
let ng = ref false;;
let spec = [
  ("-ng",Arg.Set ng,"Matita ng syntax");
  ("-tptppath", 
      Arg.String (fun x -> tptppath := x), 
      "Where to find the Axioms/ and Problems/ directory")
]

(* MAIN *)
let _ =
  let usage = "Usage: tptp2grafite [options] file" in
  let inputfile = ref "" in
  Arg.parse spec (fun s -> inputfile := s) usage;
  if !inputfile = "" then 
    begin
      prerr_endline usage;
      exit 1
    end;
  print_endline 
    (Tptp2grafite.tptp2grafite ~filename:!inputfile ~tptppath:!tptppath ~ng:!ng ());
  exit 0


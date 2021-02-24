module EC = RecommCheck
module EL = RecommLexer
module EI = RecommInput
module EO = RecommOutput

module P1 = RecommPccFor
module P2 = RecommPcsAnd

module G = RecommGc

let write = ref false

let chdir path =
  Sys.chdir path

let rec process path name =
  let file = Filename.concat path name in 
  if Sys.is_directory file then begin
    let dir = Sys.readdir file in
    Array.iter (process file) dir
  end else
  if Filename.extension file = ".ma" then begin
    Printf.eprintf "processing: %S\n" file;
    let orig = EI.read_srcs file in
    let lint = EC.recomm_srcs orig in
    if !write && lint <> orig then EO.write_srcs file lint
  end else begin
    Printf.eprintf "skipping: %S\n" file
  end

let msg_C = "<dir>  Set this working directory (default: .)"
let msg_L = " Log lexer tokens (default: no)"
let msg_c = "<int>  Set these output columns (default: 78)"
let msg_d = " Log with dark colors (default: no)"
let msg_k = " Log key comments (default: no)"
let msg_m = " Log mark comments (default: no)"
let msg_n = " Log with no colors (default: yes)"
let msg_o = " Log other comments (default: no)"
let msg_s = " Log section comments (default: no)"
let msg_t = " Log title comments (default: no)"
let msg_w = " Write the output files (default: no)"

let main =
  Arg.parse [
    "-C", Arg.String chdir, msg_C;
    "-L", Arg.Set EL.debug, msg_m;
    "-c", Arg.Int ((:=) EO.width), msg_c;
    "-d", Arg.Clear EC.bw, msg_d;
    "-k", Arg.Set EC.log_k, msg_k;
    "-m", Arg.Set EC.log_m, msg_m;
    "-n", Arg.Set EC.bw, msg_n;
    "-o", Arg.Set EC.log_o, msg_o;
    "-s", Arg.Set EC.log_s, msg_s;
    "-t", Arg.Set EC.log_t, msg_t;
    "-w", Arg.Set write, msg_w;
  ] (process "") ""

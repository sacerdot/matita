module EL = RecommLexer
module EP = RecommParser

let read_srcs file =
  let ich = open_in file in
  let lexbuf = Lexing.from_channel ich in
  let srcs = EP.srcs EL.src_token lexbuf in
  close_in ich;
  srcs

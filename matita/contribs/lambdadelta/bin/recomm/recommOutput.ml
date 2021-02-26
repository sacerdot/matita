module ET = RecommTypes

let width = ref 78

let replace = ref false

let complete s =
  let l = !width - String.length s - 6 in
  if l < 0 then begin
    Printf.eprintf "overfull: %S\n" s;
    ""
  end else begin
    String.make l '*'
  end

let out_src och = function
  | ET.Line s             ->
    Printf.fprintf och "%s" s
  | ET.Text s             ->
    Printf.fprintf och "%s" s
  | ET.Mark s             ->
    Printf.fprintf och "(* %s**)" s
  | ET.Key (s1, s2)       ->
    Printf.fprintf och "(* %s%s*)" s1 s2
  | ET.Title ss           ->
    let s = String.concat " " ss in
    Printf.fprintf och "(* %s %s*)" s (complete s)
  | ET.Slice ss           ->
    let s = String.capitalize_ascii (String.concat " " ss) in
    Printf.fprintf och "(* %s %s*)" s (complete s)
  | ET.Other (s1, s2, s3) ->
    Printf.fprintf och "%s%s%s" s1 s2 s3

let write_srcs file srcs =
  let target =  
    if !replace then begin
      Sys.rename file (file ^ ".old");
      file
    end else begin
      file ^ ".new"
    end
  in
  let och = open_out target in
  List.iter (out_src och) srcs;
  close_out och

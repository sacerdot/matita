module KF = Filename
module KP = Printf
module KU = Unix

type status = {
(* base directory *)
  bd: string;
(* input prefix *)
  ip: string;
(* output prefix *)
  op: string;
(* current path *)
  cp: string list
}

let initial_status = {
  bd = ""; ip = ""; op = "";
  cp = [];
}

let imp_st = ref initial_status

let i_ext = ".ld.ldw.xml"
let o_ext = ".ld.html"

let concats l =
  List.fold_left KF.concat "" l

let concat st dname = {st with
  ip = KF.concat st.ip dname; op = KF.concat st.op dname;
}

let normalize dname =
  if dname = KF.current_dir_name then "" else dname

let mk_rlink s_to s_body =
  KP.sprintf "<rlink to=\"%s\">%s</rlink>" s_to s_body

let out_entry st dname och dirs name =
  let iname = concats [st.bd; st.ip; dname; name] in
  let stats = KU.lstat iname in
  match stats.KU.st_kind with
  | KU.S_REG when KF.check_suffix name i_ext ->
    let base = KF.chop_suffix name i_ext in 
    let oname = concats [st.bd; st.op; dname; base^o_ext] in
    KP.fprintf och "    <file class=\"global emph\" type=\"&#x1F5CF;\" to=\"%s\" name=\"%s.ld\"/>\n" oname base;
    dirs
  | KU.S_DIR ->
    let oname = concats [st.bd; st.op; dname; name] in
    KP.fprintf och "    <file class=\"alpha emph\" type=\"&#x1F5C1;\" to=\"%s\" name=\"%s/\"/>\n" oname name;
    name :: dirs
  | _        ->
    dirs

let mk_path st och =
  let path = String.concat "/" (List.rev st.cp) in
  KP.fprintf och "    Contents of %s/\n" path

let list_dir st dname och =
  let iname = concats [st.bd; st.ip; dname] in
  let dir = Sys.readdir iname in
  Array.sort String.compare dir;
  KP.fprintf och "   <index>\n";
  let dirs = Array.fold_left (out_entry st dname och) [] dir in
  KP.fprintf och "   </index>\n";
  dirs

let out_index st dname och =
  KP.fprintf och "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n\n";
  KP.fprintf och "<page xmlns=\"http://lambdadelta.info/\"\n";
  KP.fprintf och "      description=\"\\lambda\\delta home page\"\n";
  KP.fprintf och "      title=\"\\lambda\\delta home page\"\n";
  KP.fprintf och "      head=\"λδ digital library (LDDL)\"\n";
  KP.fprintf och ">\n";
  KP.fprintf och "  <sitemap name=\"sitemap\"/>\n";
  KP.fprintf och "  <section5 name=\"index\">Index</section5>\n";
  KP.fprintf och "  <subsection name=\"path\">\n";
  mk_path st och;
  KP.fprintf och "  </subsection>\n";
  KP.fprintf och "  <body>\n";
  let dirs = list_dir st dname och in
  KP.fprintf och "  </body>\n";
  KP.fprintf och "  <footer><img label=\"helena\"/></footer>\n";
  KP.fprintf och "</page>\n";
  dirs

let rec out_dir st dname =
  let s_to, s_body =
    if dname = ""
    then concats [st.bd; st.op], "ld:" 
    else concats [st.bd; st.op; dname], dname
  in
  let st = {st with cp = mk_rlink s_to s_body :: st.cp} in
  let oname = concats [st.bd; st.ip; dname; "index.ldw.xml"] in
  let och = open_out oname in
  let dirs = out_index st dname och in
  close_out och;
  let map st = out_dir (concat st dname) in
  List.iter (map st) dirs

let help_b = "<dir>  Set this base directory"
let help_i = "<dir>  Set this input prefix"
let help_o = "<dir>  Set this output prefix"
let help = "Usage: index [ -bio <dir> | <dir> ]*"

let set_b bd =
  imp_st := {!imp_st with bd = normalize bd}

let set_i ip =
  imp_st := {!imp_st with ip = normalize ip}

let set_o op =
  imp_st := {!imp_st with op = normalize op}

let process dname =
  out_dir !imp_st (normalize dname)

let main =
  Arg.parse [
    "-b", Arg.String set_b, help_b;
    "-i", Arg.String set_i, help_i;
    "-o", Arg.String set_o, help_o;
  ] process help

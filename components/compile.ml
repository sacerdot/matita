let rec assert_ng mapath ngpath =
 let to_be_compiled =
  if exists_file ngpath then
    let preamble = preamble_of_ngpath ngpath in
    let children_bad = List.exists assert_ng preamble in
     children_bad || date mapath > date ngpath
  else
   true
 in
  if to_be_compiled then
   if already_loaded ngpath then
     (* maybe recompiling it I would get the same... *)
     raise (AlreadyLoaded mapath)
   else
    begin
      compile mapath;
      true
    end
  else
   false

and compile mapath =
 let oldstatus = status in
 let status = toplevel (new status) (content_of mapath) in
  salva_su_disco status;
  oldstatus

and toplevel status testo =
 List.fold
  (fun status cmd ->
    match cmd with
      Include mapath ->
         let ngpath = ... mapath in
         assert_ng mapath ngpath;
         carico ngpath
    | -> ...
  ) status testo
;;

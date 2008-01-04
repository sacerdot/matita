
module type Format = sig

        type source_object
        type target_object

        val target_of : source_object -> target_object
        val string_of_source_object : source_object -> string
        val string_of_target_object : target_object -> string

        val build : source_object -> bool

        val mtime_of_source_object : source_object -> float option
        val mtime_of_target_object : target_object -> float option
end

module Make = functor (F:Format) -> struct

  let prerr_endline _ = ();;

  let younger_s_t a b = 
    match F.mtime_of_source_object a, F.mtime_of_target_object b with
    | Some a, Some b -> a < b
    | _ -> false (* XXX check if correct *)
  ;;
  let younger_t_t a b = 
    match F.mtime_of_target_object a, F.mtime_of_target_object b with
    | Some a, Some b -> a < b
    | _ -> false (* XXX check if correct *)
  ;;

  let is_built t = younger_s_t t (F.target_of t);;

  let rec needs_build deps compiled (t,dependencies) =
    prerr_endline ("Checking if "^F.string_of_source_object t^" needs to be built");
    if List.mem t compiled then
      (prerr_endline "already compiled";
      false)
    else
    if not (is_built t) then
      (prerr_endline (F.string_of_source_object t^
       " is not built, thus needs to be built");
      true)
    else
    try
      let unsat =
        List.find
          (needs_build deps compiled) 
          (List.map (fun x -> x, List.assoc x deps) dependencies)
      in
        prerr_endline 
         (F.string_of_source_object t^" depends on "^F.string_of_source_object (fst unsat)^
         " that needs to be built, thus needs to be built");
        true
    with Not_found ->
      try 
        let unsat = 
          List.find (younger_t_t (F.target_of t)) (List.map F.target_of dependencies)
        in
          prerr_endline 
           (F.string_of_source_object t^" depends on "^F.string_of_target_object
           unsat^" and "^F.string_of_source_object t^".o is younger than "^
           F.string_of_target_object unsat^", thus needs to be built");
          true
      with Not_found -> false
  ;;

  let is_buildable compiled deps (t,dependencies) =
    prerr_endline ("Checking if "^F.string_of_source_object t^" is buildable");
    let b = needs_build deps compiled (t,dependencies) in
    if not b then
      (prerr_endline (F.string_of_source_object t^
       " does not need to be built, thus it not buildable");
      false)
    else
    try  
      let unsat =
        List.find (needs_build deps compiled) 
          (List.map (fun x -> x, List.assoc x deps) dependencies)
      in
        prerr_endline 
          (F.string_of_source_object t^" depends on "^
          F.string_of_source_object (fst unsat)^
          " that needs build, thus is not buildable");
        false
    with Not_found -> 
      prerr_endline 
        ("None of "^F.string_of_source_object t^
        " dependencies needs to be built, thus it is buildable");
      true
  ;;

  let rec make compiled failed deps = 
    let todo = List.filter (is_buildable compiled deps) deps in
    let todo = List.filter (fun (f,_) -> not (List.mem f failed)) todo in
    if todo <> [] then
      let compiled, failed = 
        List.fold_left 
          (fun (c,f) (file,_) ->
            if F.build file then (file::c,f)
            else (c,file::f))
          (compiled,failed) todo
      in
       make compiled failed deps
  ;;

  let rec purge_unwanted_roots wanted deps =
    let roots, rest = 
       List.partition 
         (fun (t,d) ->
           not (List.exists (fun (_,d1) -> List.mem t d1) deps))
         deps
    in
    let newroots = List.filter (fun (t,_) -> List.mem t wanted) roots in
    if newroots = roots then
      deps
    else
      purge_unwanted_roots wanted (newroots @ rest)
  ;;

  let make deps targets = 
    if targets = [] then 
      make [] [] deps
    else
      make [] [] (purge_unwanted_roots targets deps)
  ;;

end
  
let load_deps_file f = 
  let deps = ref [] in
  let ic = open_in f in
  try
    while true do
      begin
        let l = input_line ic in
        match Str.split (Str.regexp " ") l with
        | [] -> HLog.error "malformed deps file"; exit 1
        | he::tl -> deps := (he,tl) :: !deps
      end
    done; !deps
    with End_of_file -> !deps
;;

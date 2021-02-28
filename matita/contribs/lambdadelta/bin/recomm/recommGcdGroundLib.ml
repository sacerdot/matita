module T = RecommTypes
module R = RecommPccFor

let step k st outs ins =
  if st <> T.OO then k st outs ins else
  match ins with
  | "GENERATED" :: "LIBRARY" :: tl -> k T.OK ("LIBRARY" :: "GENERATED" :: outs) tl
  | "STREAMS" :: tl -> k T.OK ("STREAMS" :: outs) tl
  | "LISTS" :: tl -> k T.OK ("LISTS" :: outs) tl
  | "BOOLEANS" :: tl -> k T.OK ("BOOLEANS" :: outs) tl
  | "LOGIC" :: tl -> k T.OK ("LOGIC" :: outs) tl
  | "FUNCTIONS" :: tl -> k T.OK ("FUNCTIONS" :: outs) tl
  | "RELATIONS" :: tl -> k T.OK ("RELATIONS" :: outs) tl
  | "GROUND" :: "NOTATION" :: tl -> k T.OK ("NOTATION" :: "GROUND" :: outs) tl
  | "GENERAL" :: "NOTATION" :: "USED" :: "BY" :: "THE" :: "FORMAL" :: "SYSTEM" :: "\206\187\206\180" :: tl -> k T.OK ("NOTATION" :: "GROUND" :: outs) tl
  | _ -> k T.OO outs ins

let main =
  R.register_d step

module T = RecommTypes
module R = RecommPccFor

let step k st outs ins =
  if st <> T.OO then k st outs ins else
  match ins with
  | "PARTIAL" :: "RELOCATION" :: "MAPS" :: tl -> k T.OK ("MAPS" :: "RELOCATION" :: "PARTIAL" :: outs) tl
  | "FINITE" :: "RELOCATION" :: "MAPS" :: "WITH" :: "PAIRS" :: tl -> k T.OK ("PAIRS" :: "WITH" :: "MAPS" :: "RELOCATION" :: "FINITE" :: outs) tl
  | "FINITE" :: "RELOCATION" :: "MAPS" :: tl -> k T.OK ("MAPS" :: "RELOCATION" :: "FINITE" :: outs) tl
  | _ -> k T.OO outs ins

let main =
  R.register_d step

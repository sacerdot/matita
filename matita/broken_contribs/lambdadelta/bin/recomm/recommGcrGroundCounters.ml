module T = RecommTypes
module R = RecommPccFor

let step k st outs ins =
  if st <> T.OO then k st outs ins else
  match ins with
  | "SHIFT" :: tl -> k T.OK ("SHIFT" :: outs) tl
  | _ -> k T.OO outs ins

let main =
  R.register_r step

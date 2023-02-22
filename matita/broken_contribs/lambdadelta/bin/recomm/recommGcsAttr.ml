module T = RecommTypes
module R = RecommCheck

let step k st outs ins =
  if st = T.KO then k st outs ins else
  match ins with
  | "main" :: tl -> k T.OK ("main" :: outs) tl
  | "helper" :: tl -> k T.OK ("helper" :: outs) tl
  | "basic" :: tl -> k T.OK ("basic" :: outs) tl
  | "advanced" :: tl -> k T.OK ("advanced" :: outs) tl
  | _ -> k T.OO outs ins

let main =
  R.register_s step

module T = RecommTypes
module R = RecommCheck
module D = RecommGcsMain

let step k st outs ins =
  if st = T.KO then k st outs ins else
  match ins with
  | "with" :: tl -> k T.OK ("with" :: outs) tl
  | "of" :: tl -> k T.OK ("with" :: outs) tl
  | "for" :: tl -> k T.OK ("with" :: outs) tl
  | "on" :: tl -> k T.OK ("with" :: outs) tl
  | _ -> k T.OO outs ins

let main =
  R.register_s step

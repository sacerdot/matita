module T = RecommTypes
module R = RecommPcsPar

let step k st outs ins =
  if st <> T.OO then k st outs ins else
  match ins with
  | "(decidability)" :: tl -> k T.OK ("(decidability)" :: outs) tl
  | "(semigroup" :: "properties)" :: tl -> k T.OK ("properties)" :: "(semigroup" :: outs) tl
  | _ -> k T.OO outs ins

let main =
  R.register_p step

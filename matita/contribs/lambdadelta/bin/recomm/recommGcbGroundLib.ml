module T = RecommTypes
module R = RecommPcsAnd

let step k st outs ins =
  if st <> T.OO then k st outs ins else
  match ins with
  | "ctc" :: tl -> k T.OK ("ctc" :: outs) tl
  | "contextual" :: "transitive" :: "closure" :: tl -> k T.OK ("ctc" :: outs) tl
  | "compose" :: tl -> k T.OK ("compose" :: outs) tl
  | "function" :: "composition" :: tl -> k T.OK ("compose" :: outs) tl
  | "lsub" :: tl -> k T.OK ("lsub" :: outs) tl
  | "land" :: tl -> k T.OK ("land" :: outs) tl
  | "eq" :: tl -> k T.OK ("eq" :: outs) tl
  | "ex4" :: tl -> k T.OK ("ex4" :: outs) tl
  | _ -> k T.OO outs ins

let main =
  R.register_b step

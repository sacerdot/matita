module T = RecommTypes
module R = RecommPccFor

let step k st outs ins =
  if st <> T.OO then k st outs ins else
  match ins with
  | "\206\187\206\180-2B" :: tl -> k T.OK ("\206\187\206\180-2B" :: outs) tl
  | "\206\187\206\180-2A" :: tl -> k T.OK ("\206\187\206\180-2A" :: outs) tl
  | "WELL-FOUNDED" :: "INDUCTION" :: tl -> k T.OK ("INDUCTION" :: "WELL-FOUNDED" :: outs) tl
  | "NON-NEGATIVE" :: "INTEGERS" :: "WITH" :: "INFINITY" :: tl -> k T.OK ("INFINITY" :: "WITH" :: "INTEGERS" :: "NON-NEGATIVE" :: outs) tl
  | "NON-NEGATIVE" :: "INTEGERS" :: tl -> k T.OK ("INTEGERS" :: "NON-NEGATIVE" :: outs) tl
  | "POSITIVE" :: "INTEGERS" :: tl -> k T.OK ("INTEGERS" :: "POSITIVE" :: outs) tl
  | _ -> k T.OO outs ins

let main =
  R.register_d step

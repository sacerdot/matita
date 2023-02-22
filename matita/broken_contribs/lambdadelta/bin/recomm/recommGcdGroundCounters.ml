module T = RecommTypes
module R = RecommPccFor

let step k st outs ins =
  if st <> T.OO then k st outs ins else
  match ins with
  | "T-TRANSITION" :: "COUNTERS" :: tl -> k T.OK ("COUNTERS" :: "T-TRANSITION" :: outs) tl
  | "T-BOUND" :: "RT-TRANSITION" :: "COUNTERS" :: tl -> k T.OK ("COUNTERS" :: "RT-TRANSITION" :: "T-BOUND" :: outs) tl
  | "RT-TRANSITION" :: "COUNTERS" :: tl -> k T.OK ("COUNTERS" :: "RT-TRANSITION" :: outs) tl
  | _ -> k T.OO outs ins

let main =
  R.register_d step

module T = RecommTypes
module R = RecommPcsAnd

let step k st outs ins =
  if st <> T.OO then k st outs ins else
  match ins with
  | "rtc_plus" :: tl -> k T.OK ("rtc_plus" :: outs) tl
  | "rtc_max" :: tl -> k T.OK ("rtc_max" :: outs) tl
  | "rtc_shift" :: tl -> k T.OK ("rtc_shift" :: outs) tl
  | _ -> k T.OO outs ins

let main =
  R.register_b step

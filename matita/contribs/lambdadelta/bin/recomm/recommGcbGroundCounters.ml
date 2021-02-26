let step k ok outs ins =
  if ok then k ok outs ins else
  match ins with
  | "rtc_plus" :: tl -> k true ("rtc_plus" :: outs) tl
  | "rtc_max" :: tl -> k true ("rtc_max" :: outs) tl
  | "rtc_shift" :: tl -> k true ("rtc_shift" :: outs) tl
  | _ -> k ok outs ins

let main =
  RecommPcsAnd.register_b step

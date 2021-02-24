let step k ok outs ins =
  if ok then k ok outs ins else
  match ins with
  | "rtc_ist" :: tl -> k true ("rtc_ist" :: outs) tl
  | "test" :: "for" :: "t-transition" :: "counter" :: tl -> k true ("rtc_ist" :: outs) tl
  | "rtc_ism" :: tl -> k true ("rtc_ism" :: outs) tl
  | "test" :: "for" :: "constrained" :: "rt-transition" :: "counter" :: tl -> k true ("rtc_ism" :: outs) tl
  | "rtc_shift" :: tl -> k true ("rtc_shift" :: outs) tl
  | "shift" :: tl -> k true ("rtc_shift" :: outs) tl
  | "rtc_max" :: tl -> k true ("rtc_max" :: outs) tl
  | "max" :: tl -> k true ("rtc_max" :: outs) tl
  | _ -> k ok outs ins

let main =
  RecommPcsAnd.register_b step

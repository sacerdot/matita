let step k ok outs ins =
  if ok then k ok outs ins else
  match ins with
  | "T-TRANSITION" :: "COUNTERS" :: tl -> k true ("COUNTERS" :: "T-TRANSITION" :: outs) tl
  | "T-TRANSITION" :: "COUNTER" :: tl -> k true ("COUNTERS" :: "T-TRANSITION" :: outs) tl
  | "T-BOUND" :: "RT-TRANSITION" :: "COUNTERS" :: tl -> k true ("COUNTERS" :: "RT-TRANSITION" :: "T-BOUND" :: outs) tl
  | "RT-TRANSITION" :: "COUNTER" :: tl -> k true ("COUNTERS" :: "RT-TRANSITION" :: "T-BOUND" :: outs) tl
  | _ -> k ok outs ins

let main =
  RecommPccFor.register_d step

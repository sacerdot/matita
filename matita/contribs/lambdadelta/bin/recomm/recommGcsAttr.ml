let step k ok outs ins =
  if ok then k ok outs ins else
  match ins with
  | "main" :: tl -> k ok ("main" :: outs) tl
  | "basic" :: tl -> k ok ("basic" :: outs) tl
  | "advanced" :: tl -> k ok ("advanced" :: outs) tl
  | _ -> k ok outs ins

let main =
  RecommCheck.register_s step

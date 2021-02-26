let step k ok outs ins =
  if ok then k ok outs ins else
  match ins with
  | "SHIFT" :: tl -> k true ("SHIFT" :: outs) tl
  | "MAXIMUM" :: tl -> k true ("MAXIMUM" :: outs) tl
  | "MAXIMUN" :: tl -> k true ("MAXIMUM" :: outs) tl
  | "ADDITION" :: tl -> k true ("ADDITION" :: outs) tl
  | _ -> k ok outs ins

let main =
  RecommPccFor.register_r step

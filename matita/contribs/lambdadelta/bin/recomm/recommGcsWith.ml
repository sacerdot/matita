module D = RecommGcsMain

let step k ok outs ins =
  if ok then k ok outs ins else
  match ins with
  | "with" :: tl -> k ok ("with" :: outs) tl
  | _ -> k true outs ins

let main =
  RecommCheck.register_s step

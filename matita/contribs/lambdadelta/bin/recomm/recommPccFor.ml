module EC = RecommCheck
module ES = RecommStep

let d_line = ref ES.id

let r_line = ref ES.id

let k_for k ok outs ins =
  if ok then begin
    match ins with
    | "for" :: tl -> !d_line k false ("for" :: outs) tl
    | _           -> k true outs ins
  end else begin
    k true outs ins
  end

let k_or k ok outs ins =
  if ok then k ok outs ins else
  !r_line (k_for k) ok outs ins

let step k ok outs ins =
  if ok then k ok outs ins else
  !d_line (k_or k) ok outs ins

let register_d =
  ES.register d_line

let register_r =
  ES.register r_line

let main =
  EC.register_c step

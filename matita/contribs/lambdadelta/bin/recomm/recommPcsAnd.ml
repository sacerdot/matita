module EC = RecommCheck
module ES = RecommStep

module D = RecommGcsWith

let b_line = ref ES.id

let rec k_and k ok outs ins =
  if ok then begin
    match ins with
    | "and" :: tl -> step k false ("and" :: outs) tl
    | _           -> k true outs ins
  end else begin
    k true outs ins
  end

and step k ok outs ins =
  if ok then k ok outs ins else
  !b_line (k_and k) ok outs ins

let register_b =
  ES.register b_line

let main =
  EC.register_s step

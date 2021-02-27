module EC = RecommCheck
module ES = RecommStep
module ET = RecommTypes

module D = RecommGcsWith

let b_line = ref ES.id

let rec k_and k st outs ins =
  if st <> ET.OK then k ET.KO outs ins else
  match ins with
  | "and" :: tl -> step k ET.OK ("and" :: outs) tl
  | _           -> k ET.OK outs ins

and step k st outs ins =
  if st <> ET.OK then k st outs ins else
  !b_line (k_and k) ET.OO outs ins 

let register_b =
  ES.register b_line

let main =
  EC.register_s step

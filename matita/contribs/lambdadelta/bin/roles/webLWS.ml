(*
    ||M||  This file is part of HELM, an Hypertextual, Electronic
    ||A||  Library of Mathematics, developed at the Computer Science
    ||T||  Department, University of Bologna, Italy.
    ||I||
    ||T||  HELM is free software; you can redistribute it and/or
    ||A||  modify it under the terms of the GNU General Public License
    \   /  version 2 or (at your option) any later version.
     \ /   This software is distributed as is, NO WARRANTY.
      V_______________________________________________________________ *)

module KL = List
module KP = Printf
module KR = Random
module KT = String

type request = (string * string) list * string

(* internals *)

let opt_map = function
  | opt, ""  -> opt
  | opt, arg -> KP.sprintf "%s=%s" opt arg

let get_random () =
  KP.sprintf "%08X" (KR.bits ())

(* interface *)

let open_out enc len =
  KP.printf "%s %u\n" enc len

let close_out () =
  KP.printf "\x04"

let loop_in context handler eot st =
  let read () = KT.trim (read_line ()) in
  let rec aux st =
    let opt = read () in
    let arg = read () in
    match opt with
      | "control-stop"    -> st
      | "control-random"  -> aux st
      | "control-context" -> aux (context st)
      | "control-eot"     -> aux (eot st)
      | _                 ->
        let st = handler opt arg st in
        aux st
  in
  aux st

let string_of_request cx (opts, fi) =
  let str =
    if opts = [] then "" else
    let opts = ("control-random", get_random ()) :: opts in
    let str = KT.concat "&amp;" (KL.map opt_map opts) in
    KP.sprintf "/%s?%s" cx str
  in
  KP.sprintf "%s#%s" str fi

let control_input form =
  KP.printf "<input form=\"%s\" type=\"hidden\" name=\"%s\" value=\"%s\"/>"
    form "control-random" (get_random ())

let open_out_html author description title icon css js =
  open_out "application/xhtml+xml" 0;
  KP.printf "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n";
  KP.printf "<!DOCTYPE html PUBLIC \"-//W3C//DTD XHTML 1.1//EN\" \"http://www.w3.org/TR/xhtml11/DTD/xhtml11.dtd\">\n";
  KP.printf "<html xmlns=\"http://www.w3.org/1999/xhtml\" dir=\"ltr\" lang=\"en-us\">\n";
  KP.printf "<head>\n";
  KP.printf "  <meta http-equiv=\"Pragma\" content=\"no-cache\"/>\n";
  KP.printf "  <meta http-equiv=\"Expires\" content=\"-1\"/>\n";
  KP.printf "  <meta http-equiv=\"CACHE-CONTROL\" content=\"NO-CACHE\"/>\n";
  KP.printf "  <meta http-equiv=\"Content-Type\" content=\"text/html; charset=UTF-8\"/>\n";
  KP.printf "  <meta http-equiv=\"Content-Language\" content=\"en-us\"/>\n";
  KP.printf "  <meta http-equiv=\"Content-Style-Type\" content=\"text/css\"/>\n";
  KP.printf "  <meta http-equiv=\"content-script-type\" content=\"text/javascript\"/>\n";
  KP.printf "  <meta name=\"author\" content=\"%s\"/>\n" author;
  KP.printf "  <meta name=\"description\" content=\"%s\"/>\n" description;
  KP.printf "  <title>%s</title>" title;
  KP.printf "  <link rel=\"shortcut icon\" href=\"%s\"/>\n" icon;
  KP.printf "  <link rel=\"stylesheet\" type=\"text/css\" href=\"%s\"/>\n" css;
  KP.printf "</head>\n";
  KP.printf "<body lang=\"en-US\">\n";
  KP.printf "<script type=\"text/javascript\" src=\"%s\"/>\n" js

let close_out_html () =
  KP.printf "</body>\n";
  KP.printf "</html>\n";
  close_out ()

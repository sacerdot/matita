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

module KP = Printf

module EG = RolesGlobal
module EE = RolesEngine

let open_out_html author description title css icon =
(*
  YW.open_out "application/xhtml+xml" 0;
*)
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
  KP.printf "  <meta name=\"author\" content=\"%s\"/>\n" author;
  KP.printf "  <meta name=\"description\" content=\"%s\"/>\n" description;
  KP.printf "  <title>%s</title>" title;
  KP.printf "  <link rel=\"stylesheet\" type=\"text/css\" href=\"%s\"/>\n" css;
  KP.printf "  <link rel=\"shortcut icon\" href=\"%s\"/>\n" icon;
  KP.printf "</head>\n";
  KP.printf "<body lang=\"en-US\">\n"

let close_out_html () =
  KP.printf "</body>\n";
  KP.printf "</html>\n"
(*
  YW.close_out ()
*)
let open_out () =
  let author = "λδ development binary: roles manager" in
  let description = "λδ development binary: roles manager" in
  let title = "Roles Manager" in
  let css = Filename.concat !EG.base_url "css/roles.css" in
  let icon = Filename.concat !EG.base_url "images/crux_32.ico" in
  open_out_html author description title css icon

let close_out () =
  close_out_html ()

let init () =
  open_out ();
  close_out ()

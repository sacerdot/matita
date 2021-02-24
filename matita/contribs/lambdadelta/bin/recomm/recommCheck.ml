module ES = RecommStep
module ET = RecommTypes

let c_line = ref ES.id

let s_line = ref ES.id

let k_final b ws1 ws2 = b, ws1, ws2  

type status =
  {
    r: ET.srcs; (* reversed result *)
  }

let init () =
  {
    r = [];
  }

let add src st =
  {
    r = src :: st.r;
  }

let middle st =
  match st.r with
  | []
  | ET.Line _ :: _ -> false
  | _              -> true

let mute_o = [|
  "___                                                              ";
  "||M||                                                             ";
  "||A||       A project by Andrea Asperti                           ";
  "||T||                                                             ";
  "||I||       Developers:                                           ";
  "||T||         The HELM team.                                      ";
  "||A||         http://helm.cs.unibo.it                             ";
  "\\   /                                                             ";
  "\\ /        This file is distributed under the terms of the       ";
  "v         GNU General Public License Version 2                  ";
  "";
|]

let bw = ref false

let log_k = ref false
let log_m = ref false
let log_o = ref false
let log_s = ref false
let log_t = ref false

let no_color = "\x1B[0m"
let black    = "\x1B[30m"
let sky      = "\x1B[38;2;0;96;128m"
let blue     = "\x1B[34m"
let prune    = "\x1B[38;2;96;0;128m"
let red      = "\x1B[31m"

let log color s =
  if !bw then Printf.printf "%S\n" s else
  Printf.printf "%s%S%s\n" color s no_color

let rec recomm srcs st =
  match srcs with
  | []                             ->
    st
  | ET.Line _ as hd :: tl          ->
    recomm tl @@ add hd @@ st
  | ET.Text _ as hd :: tl          ->
    recomm tl @@ add hd @@ st
  | ET.Mark s as hd :: tl          ->
    if !log_m then log red s;
    recomm tl @@ add hd @@ st
  | ET.Key (s1, s2) as hd :: tl    ->
    if middle st then Printf.eprintf "middle: %S\n" s1;
    if !log_k then log prune (s1^s2);
    recomm tl @@ add hd @@ st
  | ET.Title ss as hd :: tl        ->
    if middle st then Printf.eprintf "middle: TITLE\n";
    let b, ss1, ss2 = !c_line k_final false [] ss in
    let ss2 =
      if ss2 = [] then ss2 else "*" :: ss2
    in
    let ss = List.rev_append ss1 ss2 in
    let s = String.concat " " ss in
    if !log_t then log blue s;
    recomm tl @@ add hd @@ st
  | ET.Slice ss as hd :: tl        ->
    if middle st then Printf.eprintf "middle: Section\n";
    let b, ss1, ss2 = !s_line k_final false [] ss in
    let ss2 =
      if ss2 = [] then ss2 else "*" :: ss2
    in
    let ss = List.rev_append ss1 ss2 in
    let s = String.capitalize_ascii (String.concat " " ss) in
    if !log_s then log sky s;
    recomm tl @@ add hd @@ st
  | ET.Other (_, s, _) as hd :: tl ->
    if !log_o && not (Array.mem s mute_o) then log black s;
    recomm tl @@ add hd @@ st

let recomm_srcs srcs =
  let st = recomm srcs @@ init () in
  List.rev st.r

let register_c = ES.register c_line

let register_s = ES.register s_line

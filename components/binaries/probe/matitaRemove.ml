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

module A = Array
module F = Filename
module Y = Sys
module U = Unix

module O = Options

let remove_dir dir =
   let map name = Y.remove (F.concat dir name) in
   let rec rmdir dir =
      U.rmdir dir; (* Sys.remove does not seem to remove empty directories *)
      rmdir (F.dirname dir)
   in
   if Y.file_exists dir then begin
      try A.iter map (Y.readdir dir); rmdir dir
      with U.Unix_error _ -> ()
   end

let objects () =
   let map name = 
      Y.remove name;
      remove_dir (F.chop_extension name)
   in
   List.iter map !O.remove

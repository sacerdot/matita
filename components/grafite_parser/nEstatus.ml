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

(* $Id: nCic.ml 9058 2008-10-13 17:42:30Z tassi $ *)

class type g_status =
 object
  inherit LexiconEngine.g_status
  inherit NCicLibrary.g_dumpable_status
 end

class status =
 object (self)
  inherit LexiconEngine.status
  inherit NCicLibrary.dumpable_status
  method set_estatus : 'status. #g_status as 'status -> 'self
   = fun o -> (self#set_lexicon_engine_status o)#set_dumpable_status o
 end

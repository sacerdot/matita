(* Copyright (C) 2005, HELM Team.
 * 
 * This file is part of HELM, an Hypertextual, Electronic
 * Library of Mathematics, developed at the Computer Science
 * Department, University of Bologna, Italy.
 * 
 * HELM is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 * 
 * HELM is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with HELM; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston,
 * MA  02111-1307, USA.
 * 
 * For details, see the HELM World-Wide-Web page,
 * http://helm.cs.unibo.it/
 *)

class type gui =
object
    (** {2 Access to singleton instances of lower-level GTK widgets} *)
  method main: MatitaGeneratedGui.mainWin

    (** {2 Utility methods} *)
  method loadScript: string -> unit

  method kill_worker: unit -> unit
end

type paste_kind = [ `Term | `Pattern ]

class type sequentsViewer =
object
  method reset: unit
  method load_logo: unit
  method load_logo_with_qed: unit
  method nload_sequents: #GrafiteTypes.status -> unit
  method goto_sequent:
   #ApplyTransformation.status -> int -> unit (* to be called _after_ load_sequents *)
end

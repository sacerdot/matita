(lang dune 3.6)
(using dune_site 0.1)

(name matita)

; Remember to change manually also matita/help/C/version.txt.in
(version 0.99.7)

(generate_opam_files true)

(source
 (github sacerdot/matita))

(authors "HELM Team" "Andrea Asperti" "Ferruccio Guidi" "Luca Padovani" "Claudio Sacerdoti Coen" "Enrico Tassi" "Stefano Zacchiroli")

(maintainers "Claudio Sacerdoti Coen")

(license GPL-2.0-or-later)

(homepage http://matita.cs.unibo.it)

(documentation http://matita.cs.unibo.it)

(package
 (name matita)
 (synopsis "An experimental, interactive theorem prover")
 (description "Matita (that means pencil in italian) is an experimental, interactive theorem prover under development at the Computer Science Department of the University of Bologna.")
 (depends
   (ocaml (and (>= "4.14.1") (< "5.0.0")))
   (ocaml-expat (>= 1.1.0))
   (pcre2 (>= 8.0.3))
   (sedlex (>= 3.0))
   (uutf (>= "1.0.0"))
   (uuseg (>= 15.0.0))
   ;(ocamlnet (>= 4.1.9.git)) ; used only by ocaml-http
   ;(ocaml-http (>= 0.1.6))   ; no longer really used, replaced by failing stubs
                              ; in components/ocaml_http_stubs
   (camlzip (>= 1.11))
   (lablgtk3-sourceview3 (>= 3.1.3))
   (cairo2 (>= 0.6.4))
   dune-build-info
   dune-site
   (camlp5 (>= 8.03.00)))
 (tags
  ("interactive theorem proving" "calculus of constructions"))
 (sites (share myshare)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project

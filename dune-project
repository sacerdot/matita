(lang dune 3.6)
(using dune_site 0.1)

(name matita)

; Remember to change manually also matita/help/C/version.txt.in
(version 0.99.5)

(generate_opam_files true)

(source
 (uri git://matita.cs.unibo.it/git/helm))

(authors "HELM Team (Andrea Asperti, Ferruccio Guidi, Luca Padovani, Claudio Sacerdoti Coen, Enrico Tassi, Stefano Zacchiroli et alt.)")

(maintainers "Claudio Sacerdoti Coen")

(license GPL-2.0-or-later)


(bug_reports "mailto:claudio.sacerdoticoen@unibo.it")

(homepage http://matita.cs.unibo.it)

(documentation http://matita.cs.unibo.it)

(package
 (name matita)
 (synopsis "An experimental, interactive theorem prover")
 (description "Matita (that means pencil in italian) is an experimental, interactive theorem prover under development at the Computer Science Department of the University of Bologna.")
 (depends
   (ocaml (>= "4.14.1"))
   (ulex-camlp5 (>= 1.3))
   (ocaml-expat (>= 1.1.0))
   (pcre (>= 7.5.0))
   (ocamlnet (>= 4.1.9.git)) ; used only by ocaml-http
   (ocaml-http (>= 0.1.6))
   (camlzip (>= 1.11))
   (lablgtk3-sourceview3 (>= 3.1.3))
   dune-build-info
   dune-site
   (camlp5 (>= 8.00.04)))
 (tags
  ("interactive theorem proving" "calculus of constructions"))
 (sites (share myshare)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project

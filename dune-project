(lang dune 3.6)

(name matita)

(version 0.99.5)

(generate_opam_files true)

(source
 (uri http://matita.cs.unibo.it/download.shtml))

(authors "HELM Team (Andrea Asperti, Ferruccio Guidi, Claudio Sacerdoti Coen, Enrico Tassi, Stefano Zacchiroli et alt.)")

(maintainers "Claudio Sacerdoti Coen")

(license GPL)

(homepage http://matita.cs.unibo.it)

(documentation http://matita.cs.unibo.it)

(package
 (name matita)
 (synopsis "An experimental, interactive theorem prover")
 (description "Matita (that means pencil in italian) is an experimental, interactive theorem prover under development at the Computer Science Department of the University of Bologna.")
 (depends
   (ocamlnet (= 4.1.9.git))
   (ulex-camlp5 (= 1.3))
   (ocaml-expat (= 1.1.0))
   (lablgtk3-sourceview3 (= 3.1.3))
   (camlp5 (= 8.00.04)))
 (tags
  ("interactive theorem proving" "calculus of constructions")))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project

(lang dune 3.15)

(name ASLCI)

(generate_opam_files true)

(source
 (github anishrajeev/ASLCI))

(authors "Anish Rajeev")

(maintainers "Anish Rajeev")

(license LICENSE)

(documentation https://url/to/documentation)

(package
 (name ASLCI)
 (synopsis "Another Simple Lambda Calculus Interpreter")
 (description "An interpreter for the typed LC for me to apply the ideas I've learned in TAPL")
 (depends ocaml dune)
 (tags
  (topics "to describe" your project)))

(using menhir 3.0)
; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project

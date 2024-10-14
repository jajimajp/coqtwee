(lang dune 3.14)
(using coq 0.8)

(name coqtwee)


(generate_opam_files true)

(source
 (github jajimajp/coqtwee))

(authors "Soichi Yajima")

(maintainers "Soichi Yajima")

(license MIT)

(documentation https://github.com/jajimajp/coqtwee)

(package
 (name coqtwee)
 (synopsis "Equational theorem proving plugin for Coq using Twee")
 (depends ocaml dune)
 (tags
  (coq proof)))

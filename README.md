# in-school
This repository contains two memorable projects realised while in school:
- `inductive-type-generator`: a piece of software that generates several lines of Coq code given an inductive type definition;
- `final-year-internship`: Coq proofs of some of the theorems of the research paper *Extending Modal Transition Systems with Structured Labels*, written by Sebastian S. Bauer et al., and published in 2012 in the journal *Mathematical Structures in Computer Science*.

The project in `inductive-type-generator` requires `ocaml` and `camlp5` to be installed on your system, and `final-year-internship` requires `coq`. Please keep in mind that these projects were realised in 2013 and 2015 respectively: you may need older versions of `ocaml`, `camlp5`, and `coq` for them to work properly.

## About the Code Generator
This OCaml software was created during the final year internship of my Bachelor's degree:
- `inductive-type-generator\abstract.pdf` introduces the project;
- `inductive-type-generator\report.pdf` is the report my teammate and I were evaluated on (in French);
- `inductive-type-generator\defense.pdf` is the slideshow we used during our defense (in French);
- `inductive-type-generator\src` contains source files: run the `Makefile` to create an executable;
- `inductive-type-generator\test` contains test files: `*.ml4` files are inputs and `*.v` files are results; rerun the test with `run.sh`.

## About the Coq Certification of the Research Paper
This Coq library was developed during the final year internship of my Master's degree:
- `final-year-internship\paper.pdf` is the research paper of which I certified in Coq some theorems with the help of my supervisors;
- `final-year-internship\thesis.pdf` is my Master's thesis (in French);
- `final-year-internship\defense.pdf` is the slideshow I used during my defense (in French);
- `final-year-internship\scr` contains source files: run the `Makefile` to create a binary version of the library, and open it to know the dependencies between the Coq theories contained therein.
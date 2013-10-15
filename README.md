# CGals
===========

A Cgals compiler with proven real-time and functional guarantees.


Cgals (pronounced seagull) is a programming language for writing safety
critical and hard-real time systems. The compiler uses a GALS (Globally
Asynchronous Locally Synchronous) model of computation to schedule
processes and a variant of 'C' programming language for writing
data. The compiler automatically extracts linear temporal logic from the
written programs and compiles them to a model for verification with SPIN
model-checker using LTL (Linear temporal logic) properties --
guaranteeing functional and timing requirements. Finally, 'C' code is
extracted from the verified models to be compiled with the compcert 'C'
compiler, which is a verified 'C' compiler.


Generating Safety Critical Java (SCJ) code level-0 and level-1 are
planned.


# INSTALL:


Install dependencies:

* Ocaml (>= 4.01.0) http://ocaml.org/
* Batteries: http://batteries.forge.ocamlcore.org/
* Sexplib: https://github.com/janestreet/sexplib.git
* ocaml-pretty: https://github.com/toyvo/ocaml-pretty (will need to write the META file)
* ocaml-find/findlib: http://projects.camlcity.org/projects/findlib.html
* parmap: https://github.com/rdicosmo/parmap
* SPIN model-checker: http://spinroot.com/
* CVC3 (http://www.cs.nyu.edu/acsys/cvc3/) /Z3 (http://z3.codeplex.com/) if you want to perform real-time analysis. The output-files in branch smt are produced in the smt-lib format

make clean && make in the source directory.


# Usage:

## Language:

The language description is available here:

Avinash Malik, Zoran Salcic, Partha S. Roop, Alain Girault: SystemJ: A
GALS language for system level design. Computer Languages, Systems &
Structures 36(4): 317-344 (2010)


## Compiling:

```shell
./systemjc <name-of-file>.sysj -promela [name-of-promela-file.pml] -formula ["formula"]
```

Once compiled: verify the property using "ispin".
``` shell
ispin <name-of-promela-file.pml>
```

see SPIN documentation for more details.


Complete examples are available in testsuite/ directory

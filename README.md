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

Safety critical Java code can also be generated.


# INSTALL:

Install dependencies:

* Ocaml (>= 3.12.0) http://ocaml.org/
* Batteries: http://batteries.forge.ocamlcore.org/
* Sexplib: https://github.com/janestreet/sexplib.git
* ocaml-pretty: https://github.com/toyvo/ocaml-pretty (will need to write the META file)
* ocaml-find/findlib: http://projects.camlcity.org/projects/findlib.html
* parmap: https://github.com/rdicosmo/parmap
* SPIN model-checker: http://spinroot.com/
* CVC3 (http://www.cs.nyu.edu/acsys/cvc3/) /Z3 (http://z3.codeplex.com/)
  if you want to perform real-time analysis. The output-files 
  are produced in the smt-lib (http://www.smtlib.org/)
  format

make clean && make in the source directory.


# Usage:

## Language:

The language description and implementation description is available in the following papers:

* Avinash Malik, Zoran Salcic, Partha S. Roop, Alain Girault: SystemJ: A
GALS language for system level design. Computer Languages, Systems &
Structures 36(4): 317-344 (2010)

* HeeJong Park, Avinash Malik, Zoran A. Salcic: WYPIWYE automation systems - 
An intelligent manufacturing system case study. ETFA 2014: 1-8

* H.J. Park, A. Malik, Z. Salcic, Scheduling Globally Asynchronous Locally
Synchronous Programs for Guaranteed Response Times, ACM Transactions on
Design Automation of Electronic Systems (TODAES), 2015


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

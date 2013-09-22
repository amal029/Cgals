CGals
===========

A C compiler with proven real-time and functional guarantees.


Cgals (pronounced seagull) is a programming language for writing safety
critical and hard-real time systems. The compiler uses a GALS (Globally
Asynchronous Locally Synchronous) model of computation to schedule
processes and a variant of 'C' programming language for writing
data. The compiler automatically extracts linear temporal logic from the
written programs and compiles them to a model for verification with SPIN
or Uppaal model-checkers using LTL (Linear temporal logic) or CTL
(Computational Tree Logic) properties -- guaranteeing functional and
timing requirements. Finally, 'C' code is extracted from the verified
models to be compiled with the compcert 'C' compiler, which is a
verified 'C' compiler.


Generating Safety Critical Java (SCJ) code level-0 and level-1 are
planned.


INSTALL:


Install dependencies:

* Batteries: http://batteries.forge.ocamlcore.org/
* Sexplib: https://github.com/janestreet/sexplib.git
* ocaml-pretty: https://github.com/toyvo/ocaml-pretty (will need to write the META file)
* ocaml-find/findlib: http://projects.camlcity.org/projects/findlib.html
* SPIN model-checker: http://spinroot.com/

make clean && make in the source directory.


Usage:

The language description is available here:

Avinash Malik, Zoran Salcic, Partha S. Roop, Alain Girault: SystemJ: A
GALS language for system level design. Computer Languages, Systems &
Structures 36(4): 317-344 (2010)


Compiling:

./systemjc <name-of-file>.sysj -promela [name-of-promela-file.pml] -formula ["formula"]

Once compiled: verify the property like so:
ispin <name-of-promela-file.pml>

see SPIN documentation for more details.


A complete example is available in testsuite/channel_comm.sysj

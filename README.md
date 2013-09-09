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

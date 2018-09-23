coq2smt
=============

This plugin is based on [coq-smt-check](https://github.com/gmalecha/coq-smt-check).

This is a simple way to invoke an SMT solver on Coq goals.
It does *NOT* generate proof objects. It is meant purely for sanity checking
goals.

The main tactic is 'smt solve' which invokes an smt on the current goal. The
core of the plugin is the conversion from Coq to SMT2 format. At the moment,
the conversion handles the following:

 - boolean connectives, /\, \/, not
 - equality
 - variables
 - real numbers, +, -, /, constants
 - Z
 - int8, int16, int32, int64
 - self-defined types that consist of above types

If your problem fits in this fragment (it can contain other facts as well), then
you can run:

    smt solve.

If the solver solves the goal then the tactic will succeed. If the solver
returns an unsat core then the tactic will act like

    clear - <unsat core>.

otherwise it will simply act like idtac (doing nothing to the goal).
If the solver fails to solve the goal then the tactic will fail and
display the sat model if the solver returns one. A common way to use
the tactic is something like the following:

    smt solve; admit.

which will admit the goal only if it is solved by the SMT solver.

You can also specify the solver to use in the tactic using the syntax:

    smt solve calling "<solver-name>".

Where `<solver-name>' is, e.g. z3 or cvc4.

See the test-suite directory for examples.

Requirements
-------

 - [Coq8.6.1](https://coq.inria.fr/coq-86)
 - [coq-plugin-utils](https://github.com/gmalecha/coq-plugin-utils)

Solvers
-------

Currently, the code supports Z3 and CVC4. You need to set the solver using

    Set SMT Solver "z3".

or

    Set SMT Solver "cvc4".

You can toggle debugging globally using:

    Set SMT Debug.
    Unset SMT Debug.

Implementing Your Own Solver
----------------------------

You can implement your own solver interface using a Coq Plugin. At the high
level, you should call:

    SmtTactic.register_smt_solver : <name> -> (<options> -> <solver>) -> unit

and then set up the solver appropriately. Note that solver names can *NOT*
contain colons (:). The string passed will be split on the first colon (if
one exists) and the rest of the string will be passed as `options` above.

Contributors
------------

This plugin was started by Vignesh Gowada at UCSD as part of the [VeriDrone](http://veridrone.ucsd.edu/) project. 
And it is based on Gregory Malecha's [coq-smt-check](https://github.com/gmalecha/coq-smt-check).

External contributions are always welcome.

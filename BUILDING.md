Building the Tabulator
======================

Building the Tabulator means compiling and analyzing its system
specifications, double-checking its proofs, extracting an
implementation from its specification, and building its manually
written implementations.

A top-level build file specified using GNU make will trigger a full
build, validation, and formal verification of the entire Tabulator
system. Ensure that you have all dependencies installed property.

Dependencies
------------

The Tabulator system and its specifications and implementations rely
upon the following technologies:
 * the [BON][bon] [tool suite][BONc] and its dependencies (such as
   dia, LaTeX, ImageMagik, etc.),
 * [Coq][coq],
 * [Haskell][haskell], and
 * [SPARK][spark].

Specifications
--------------

EBON specifications are located in the `specs` directory. Review the
`Makefile` therein to run the build system for system specifications.
In particular, one can check the EBON system specifications for
consistency and extract system documentation into HTML.

Proofs
------

The formal specification of the election schemes we support are
located in the `coq` directory.  An automatically synthesized makefile
therein uses Coq to typecheck our formalizations as well as their
implementations (in Coq), including the proof of correctness that our
implementations perfectly correspond to their specifications.

Extraction
----------

That same makefile in the `coq` directory also supports the extraction
of an implementation of our tabulator(s) into Haskell and the rigorous
validation of those implementations through the use of QuickCheck.

Implementations
---------------

We have also manually implemented the Tabulator in the SPARK
programming language and rigorously validated and formally verified
those implementations against the aforementioned system and election
scheme specifications.  See the `spark` directory for more
information.

The SPARK implementation is fully multi-platform, permits us to easily
put a graphical front-end on the Tabulator (independent of OpenCount),
and integrate in a straightforward fashion other subsystems written in
languages like Java VM-based languages (such as Java, Scala, etc.) and
C-like languages (such as C, C++, and Objective-C).

[bon]: http://www.bon-method.com/
[haskell]: https://www.haskell.org/
[spark]: http://www.adacore.com/sparkpro/
[coq]: https://coq.inria.fr/
[BONc]: http://kindsoftware.com/products/opensource/BONc/

Tabulator
=========

The **Free & Fair Tabulator** tallies digital Cast Vote Records,
specified in an open JSON-based format, into an election result.

The *Tabulator* is a rigorously engineered high assurance system. Its
quality level is comparable to the best software ever written,
conforming to [Common Criteria][CC] [EAL][eal] 7+.

The Tabulator is formally specified in [BON][bon] and [Coq][coq], and
is implemented via [extraction][extraction] to [Haskell][haskell] or
[OCaml][ocaml] from Coq, and by hand in [SPARK][spark].

Tabulator's specifications and implementations are all formally
reviewed by domain experts, formally verified using mechanical proof
tools, and rigorously validated using artifacts synthesized from those
formal tools. As such, this work is incomparable to any other work in
the elections space worldwide.

The Tabulator's development was accomplished using the Free & Fair
rigorous engineering methodology, sometimes known as **SNFM**. All of
the tools, processes, methodologies, and techniques associated with
this development are published in top peer-reviewed venues. See our
bibliography below for more information.

This work will inform the work of IEEE's Voting System Standards
Committee (VSSC) Working Group [1622.6][vssc_1622_6], "Voting Methods
Mathematical Models."

Specification
-------------

The formal specification of the Tabulator comes in three parts:
  1. at the top-most abstraction level, we provide an EBON
     specification (EBON is Extended BON) of the Tabulator system.  An
     EBON specification itself consists of two parts, one *informal*
     and the other *formal*:
     1. the *informal* specification of the system has five parts:
        1. a *domain model* of the system that describes its core
           concepts and their relationships,
        2. the *requirements* that the system must fulfill,
        3. the *scenarios* that the system must support,
        4. the *events* that the system reacts to and itself emits,
           and
        5. the *creation* structure of the system which describes
           critical dynamic relationships between various parts of the
           system and the resources that the system uses,
     2. the *formal* specification of the system has three parts:
        1. an architecture specification which describes the system at
           a high level using architectures styles,
        2. a static structural specification of the system which
           describes the system and its behavior in a programming
           language and platform-neutral fashion, and
        3. a dynamic structural specification of the system which
           elucidates the informal scenario and event specifications.

     This specification includes an informal and formal specification
     of our Cast Vote Record serialization format. As such, it
     constitutes a quality case study in the formalization and
     realization of interoperability formats in the elections domain.

  2. a formal specification of the election schemes that the Tabulator
     implements.  Namely, we support two variants at this time:
     1. the version of [ranked choice voting][rcv] (RCV), also known
        as [instant runoff voting][irv] (IRV) in the case of a single
        winner and the [single transferable vote][stv] (STV) more
        generally, that is used in in San Francisco, CA, and
     2. plurality, as is used across the U.S.A. for local, state, and
        federal elections.

  3. a formal specification of the system using one or more
     [formal methods][fm].  These specifications formally describe the
     static structure and dynamic behavior of the system in a fashion
     that is amendable to static and dynamic analysis and permits us
     to reason about our various implementations in a rigorous
     fashion.  The formal methods we intend to use include the
     [Alloy][alloy], [B][b], [RAISE][raise], [VDM][vdm], and [Z][z]
     formal methods.

Building
--------

Building the Tabulator means compiling and analyzing its system
specifications, double-checking its proofs, extracting an
implementation from its specification, and building its manually
written implementations. See the file `BUILDING.md` for more
information.

Future Work
-----------

During the evolution of the Tabulator we intend to focus on those
variants of RCV used in U.S. jurisdictions. On our short list at the
moment are the RCV variants used in the jurisdictions mentioned in the
*Jurisdiction Sources* section.

We have already formalized, implemented, and verified election schemes
used outside of the U.S.A., such as PR-STV in Ireland, the list-based
scheme of The Netherlands, and the Parliamentary scheme used in
Denmark, in other repositories.

Within our Coq formalization we intend to demonstrate the functional
correctness of our system against appropriate standard social choice
properties, such as the *Condorcet* property, the *later-no-harm*
property, etc.  We are also interested in formalizing enough game
theory to tackle questions about voting tactics, such as the
resistence of various schemes to specific tactical voting techniques.

The project will also support the development of new ways of auditing
RCV elections. That work is located in another repository as well.

Please contact us for more details about any of these other projects
or if you have an interest in our supporting a new election scheme.

Build Status
------------

The build status of the original GitHub repository from which our Coq
specification comes is located here: [![Build Status](https://travis-ci.org/cjerdonek/formal-rcv.svg?branch=master)](https://travis-ci.org/cjerdonek/formal-rcv)

*A note about the build status:* it is not currently completely continuous, and an improper commit might cause it to fall behind. It is only correct if [the extracted implementation](https://github.com/cjerdonek/formal-rcv/blob/master/src/extracted/ext/SF_imp.hs) is as new as [the Coq implementation](https://github.com/cjerdonek/formal-rcv/blob/master/src/SF_imp.v). We are still considering fixes to this problem.

Contents
--------

* [Glossary](docs/glossary.md)
* [Statutes](#jurisdiction-sources)
* [License](#license)
* [Contributors](#contributors)

Jurisdiction Sources
--------------------

This section contains links to statutes and other sources that describe
the RCV rules in each jurisdiction we are interested in.

* Berkeley, CA, [Municipal Codes][berkeley_codes].
  See Charter, Article III, Sec. 5.12, "Use of instant runoff voting in lieu
  of runoff elections"; and Municipal Code, Title 2, Chapter 2.14,
  "Elections -- Instant Runoff Voting."
* Cambridge, MA
  * TODO
* Minneapolis, MN, [Code of Ordinances][minneapolis_codes].
  See Charter, Article III, Sec. 3.1; and Code of Ordinances, Title 8.5,
  Chapter 167, "Municipal Elections: Rules of Conduct."
* Oakland, CA, [Charter][oakland_charter].  See Article XI, Sec. 1105,
  "Ranked Choice Voting."
* Portland, ME
  * TODO
* San Francisco, CA, [Charter][sf_charter].  See Article XIII, Sec. 13.102,
  "Instant Runoff Elections."
* San Leandro, CA
  * TODO
* Saint Paul, MN
  * TODO

License
-------

The project is licensed under a BSD 3-Clause license.  See the
[LICENSE](LICENSE) file for details.

Contributors
------------

* Rob Dockins
* Joey Dodds
* Chris Jerdonek
* Joseph Kiniry
* Dan Zimmerman

Bibliography
------------

TODO

[bon]: http://www.bon-method.com/
[extraction]: https://coq.inria.fr/refman/Reference-Manual026.html
[haskell]: https://www.haskell.org/
[ocaml]: https://ocaml.org/
[spark]: http://www.adacore.com/sparkpro/
[berkeley_codes]: http://codepublishing.com/ca/berkeley/
[coq]: https://coq.inria.fr/
[irv]: https://en.wikipedia.org/wiki/Instant-runoff_voting
[minneapolis_codes]: https://www.municode.com/library/mn/minneapolis/codes/code_of_ordinances?nodeId=11490
[oakland_charter]: https://www.municode.com/library/ca/oakland/codes/code_of_ordinances?nodeId=16308
[rcv]: https://en.wikipedia.org/wiki/Ranked_Choice_Voting
[sf_charter]: http://www.amlegal.com/library/ca/sfrancisco.shtml
[stv]: https://en.wikipedia.org/wiki/Single_transferable_vote
[vssc_1622_6]: http://grouper.ieee.org/groups/1622/groups/6/index.html

Formal RCV source
=================

Building
--------

### Prerequisites

Install [Coq][coq]. This project currently builds with (exactly)
[Version8.4pl6](https://coq.inria.fr/coq-84).

Install [Haskell][haskell], preferably using the
[Haskell Platform](https://www.haskell.org/platform/) be sure to get
at least GHC 7.8.

Run GNU make in the "`coq`" source directory:
```
make
```

This should build all of the Coq files in the directory. Building the
Coq files also checks the proof of correctness for the implementations
of ranked choice voting and plurality.

To build the docs for the Coq files run:
```
make html
```

This will place docs in a folder named "`html`".

Then move to the "`extracted`" folder
```
cd extracted
```

Create a [cabal][cabal] sandbox

```
cabal sandbox init
```

and run

```
cabal install
```

to build the extracted Haskell implementation and all of its
dependencies. Note that, at the time of this writing, there is
approximately 104 MB of source and binary dependencies to be
downloaded and built. The binary executable of the tabulator is only
approximately 15 MB in size.

Finally, run

```
cabal test
```

to run the [QuickCheck][quickcheck] tests that have been automatically
extracted from Coq.

[quickcheck]: https://hackage.haskell.org/package/QuickCheck
[coq]: https://coq.inria.fr/
[haskell]: https://www.haskell.org/
[cabal]: https://www.haskell.org/cabal/

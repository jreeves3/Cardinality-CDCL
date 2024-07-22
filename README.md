# Cardinality-CDCL
CDCL with native cardinality constraint handling.


Solver and Checker:
* CaDiCaL (https://github.com/arminbiere/cadical Commit a5f15211db36c3956764e18194dd5bd63bf3b5e6)
* Drat-trim (https://github.com/marijnheule/drat-trim)


## Build

To build use

```bash
sh build.sh
```

To clean use

```bash
sh clean.sh
```


## General Usage

Solver configurations include:

* CCDCL:    cardinality-based CDCL solver
* CCDCL+:   cardinality-based CDCL solver with reencoded constraints
* ReEncode: basic CaDiCaL CDCL solver with reencoded constraints

For general usage with a KNF formula as input, you can use the cardinality CDCL solver directly with:

`> ./cardinality-cadical/build/cadical <KNF> <Proof> --no-binary`

Where `<Proof> --no-binary` can be left off if you do not need proof logging.

If you want to extract cardinality constraints from a CNF, or use one of the configurations that reencodes cardinality constraints into clauses, you should use one of the scripts below.

The scripts also provide proof checking.

## Running Scripts

To run configurations from the paper (on input CNF), and check result (as described in the paper):

* CaDiCaL:  `> sh scripts/cadical <CNF>`
* CCDCL:  `> sh scripts/ccdcl <CNF>`
* CCDCL+: `> sh scripts/ccdclPlus <CNF>`
* ReEncode: `> sh scripts/ReEncode <CNF>`

e.g., `sh scripts/ccdcl.sh benchmarks/cnf/php8.cnf`

To run configurations from the paper (on input KNF), and check result (as described in the paper):

* CCDCL:  `> sh scripts/ccdcl <KNF>`
* CCDCL+: `> sh scripts/ccdclPlus <KNF>`
* ReEncode: `> sh scripts/ReEncode <KNF>`

e.g., `sh scripts/ccdcl.sh benchmarks/knf/php8.knf `

The folder `tmp` will contain formulas and proofs when executing the scripts.

To extract a KNF from a CNF, use
```bash
sh scripts/Extract.sh <CNF> <OUT.knf>
```

To reencode a KNF into CNF, for the Linear encoding of AMO use
```bash
./tools/knf2cnf <KNF> > <OUT.cnf>
```

for the pairwise encoding of AMO constraints use
```bash
./tools/pairwise <KNF> > <OUT.cnf>
```

To generate the derivation for the Linear AMO reencoding, use
```bash
./tools/derivation <KNF> > <OUT.drat>
```


## Data

For extraction and solving on the SAT Annivesary track benchmarks, as well as an extractor compariosn on PySAT.Card encodings, refer to the CAV24 repository: https://github.com/jreeves3/CAV24-FromClausesToKlauses and paper: https://www.cs.cmu.edu/~jereeves/research/cav24-paper.pdf
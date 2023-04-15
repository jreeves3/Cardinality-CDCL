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

* CaDiCaL:  basic CaDiCaL CDCL solver
* CCDCL:    cardinality-based CDCL solver
* CCDCL+:   cardinality-based CDCL solver with reencoded constraints
* ReEncode: basic CaDiCaL CDCL solver with reencoded constraints
* CCDCL-:   CCDCL with reencoded constraints (basic CaDiCaL with some inprocessing disabled)

The three main configurations are CCDCL, CCDCL+, and ReEncode. The others are controls used in the paper. 

For general usage with a KNF formula as input, you can use the cardinality CDCL solver directly with:

`> ./cardinality-cadical/build/cadical <KNF> <Proof> --no-binary`

Where `<Proof> --no-binary` can be left off if you do not care about proof logging.

If you want to extract cardinality constraints from a CNF, or use one of the configurations that reencodes cardinality constraints into clauses, you should use one of the scripts below.

The scripts also provide certificate checking.


## Running Scripts

To run configurations from the paper (on input CNF), and check result (as described in the paper):

* CaDiCaL:  `> sh scripts/cadical <CNF>`
* CCDCL:  `> sh scripts/ccdcl <CNF>`
* CCDCL+: `> sh scripts/ccdclPlus <CNF>`
* CCDCL-: `> sh scripts/ccdclMinus <CNF>`
* ReEncode: `> sh scripts/ReEncode <CNF>`

e.g., `sh scripts/ccdcl.sh benchmarks/cnf/php8.cnf`

To run configurations from the paper (on input KNF), and check result (as described in the paper):

* CCDCL:  `> sh scripts/ccdcl <KNF>`
* CCDCL+: `> sh scripts/ccdclPlus <KNF>`
* CCDCL-: `> sh scripts/ccdclMinus <KNF>`
* ReEncode: `> sh scripts/ReEncode <KNF>`
* ReEncodePair: `> sh scripts/ReEncodePair <KNF>`

e.g., `sh scripts/ccdcl.sh benchmarks/knf/php8.knf `

The folder `tmp` will contain formulas and proofs when executing the scripts.

Note, before running the cardinality extractor and before solving we permute clauses in the formula with 

```bash
python3 tools/permute.py -c <IN> -o <OUT>
```

To extract a KNF from a CNF, use
```bash
python3 tools/card_extractor.py -i <CNF> -T 1000 -o <OUT.knf>
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

To extract paper table data from spreadsheets, use
```bash
python3 get_data.py -t
```

To extract paper plots in tikz format from spreadsheets, use
```bash
python3 get_data.py -p
```

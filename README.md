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

* CCDCL:    cardinality-based CDCL solver (native propagation on cardinality constraints)
* CCDCL+:   cardinality-based CDCL solver with reencoded constraints (Hybrid mode from the paper)
* ReEncode: basic CaDiCaL CDCL solver with reencoded constraints

For general usage with a KNF formula as input, you can use the cardinality CDCL solver directly with:

`> ./cardinality-cadical/build/cadical <KNF> <Proof> --no-binary`

Where `<Proof> --no-binary` can be left off if you do not need proof logging.

If you want to extract cardinality constraints from a CNF, or use one of the configurations that reencodes cardinality constraints into clauses, you should use one of the scripts below.

The scripts also provide proof checking.

## KNF format

Header : `p knf  <nVariables> <nKlauses>`

Cardinality Constraint : `k <bound> [<lit>] 0`

x1 + x3 + -x5 >= 2 : `k 2 1 3 -5 0`

Clauses written in standard dimacs format 

(x1 OR x2 OR -x5) : `1 2 -5 0`

Note, KNF does not support duplicate literals or opposing literals in cardinality constraints. 

Remove opposing literals and update the bound appropriately in a preprocessing step before calling the solver. 

E.g., x1 + -x1 + x2 + x3 >= 2 can be replaced by x2 + x3 >= 1.

Duplicate literals can be replaced by new variables in a preprocessing step before calling the solver. 

E.g., x1 + x1 + x2 >= 1 can be replaced by x3 + x4 + x2 >= 1 AND x1 <-> x3 AND x1 <-> x4. 

## Running Scripts

Proof checking is enabled with `1` and disabled with `0`. 

To run configurations from the paper (on input CNF), and check result (as described in the paper):

* CaDiCaL:  `> sh scripts/cadical <CNF> <ProofChecking>`
* CCDCL:  `> sh scripts/ccdcl <CNF> <ProofChecking>`
* CCDCL+ (Hybrid mode): `> sh scripts/ccdclPlus <CNF> <ProofChecking>`
* ReEncode: `> sh scripts/ReEncode <CNF> <ProofChecking>`

e.g. with proog checking, `sh scripts/ccdcl.sh benchmarks/cnf/php8.cnf 1`

To run configurations from the paper (on input KNF), and check result (as described in the paper):

* CCDCL:  `> sh scripts/ccdcl <KNF> <ProofChecking>`
* CCDCL+ (Hybrid mode): `> sh scripts/ccdclPlus <KNF> <ProofChecking>`
* ReEncode: `> sh scripts/ReEncode <KNF> <ProofChecking>`

e.g. with proog checking, `sh scripts/ccdcl.sh benchmarks/knf/php8.knf 1`

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
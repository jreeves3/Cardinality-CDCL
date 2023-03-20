# Cardinality-CDCL
CDCL with native cardinality constraint handling.


Solver and Checker:
* CaDiCaL (https://github.com/arminbiere/cadical Commit a5f15211db36c3956764e18194dd5bd63bf3b5e6)
* Drat-trim (https://github.com/marijnheule/drat-trim)

To build use

	``> sh build.sh``

To clean use

	``> sh clean.sh``

To extract paper table data from spreadsheets, use
	``python3 get_data.py -t``

To extract paper plots in tikz format from spreadsheets, use
	``python3 get_data.py -p``

To run configurations from the paper (on input CNF), and check result (as described in the paper):

* CaDiCaL:  ``> sh scripts/cadical <CNF>``
* CCDCL:  ``> sh scripts/ccdcl <CNF>``
* CCDCL+: ``> sh scripts/ccdclPlus <CNF>``
* CCDCL-: ``> sh scripts/ccdclMinus <CNF>``
* ReEncode: ``> sh scripts/ReEncode <CNF>``

e.g., ``sh scripts/ccdcl.sh benchmarks/cnf/php8.cnf``

To run configurations from the paper (on input KNF), and check result (as described in the paper):

* CCDCL:  ``> sh scripts/ccdcl <KNF>``
* CCDCL+: ``> sh scripts/ccdclPlus <KNF>``
* CCDCL-: ``> sh scripts/ccdclMinus <KNF>``
* ReEncode: ``> sh scripts/ReEncode <KNF>``
* ReEncodePair: ``> sh scripts/ReEncodePair <KNF>``

e.g., ``sh scripts/ccdcl.sh benchmarks/knf/php8.knf``

The folder `tmp` will contain formulas and proofs when executing the scripts.

Note, before running the cardinality extractor and before solving we permute clauses in the formula with 

	``python3 tools/permute.py -c <IN> -o <OUT>``

To extract a KNF from a CNF, use

	``python3 tools/card_extractor.py -i <CNF> -T 1000 -o <OUT.knf>``

To reencode a KNF into CNF, for the Linear encoding of AMO use

	``./tools/knf2cnf <KNF> > <OUT.cnf>``

for the pairwise encoding of AMO constraints use

	``./tools/pairwise <KNF> > <OUT.cnf>``

To generate the derivation for the Linear AMO reencoding, use

	``./tools/derivation <KNF> > <OUT.drat>``




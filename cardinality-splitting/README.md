# Cardinality Splitting

Tooling for the cardinality splitting of the totalizer encoding from [Problem Partitioning via Proof Prefixes](drops.dagstuhl.de/entities/document/10.4230/LIPIcs.SAT.2025.3)

Zachary Battleman, Joseph E. Reeves, and Marijn J. H. Heule. Problem Partitioning via Proof Prefixes. In 28th International Conference on Theory and Applications of Satisfiability Testing (SAT 2025). Leibniz International Proceedings in Informatics (LIPIcs), Volume 341, pp. 3:1-3:18, Schloss Dagstuhl – Leibniz-Zentrum für Informatik (2025) https://doi.org/10.4230/LIPIcs.SAT.2025.3


Proofix available at https://github.com/zaxioms0/proofix


## Totalizer Splitting 

To generate a single CNF from a KNF using the totalizer encoding, run 

  `> python3 totalizer_splitting.py -f <form.knf> -o <form.cnf>`

To generate `N` static splitting variables, with 2^`N` cubes appended to the end of the incremental, run 

  `> python3 totalizer_splitting.py -f <form.knf> -i <N> -a <form.icnf>`

Note, if these formulas contain AMO of AM2 constraints, please use a tool like knf2cnf to encode them. 

The program will display information about the splitting variables selected and the node counters they arise from. 

To parallelize solving of the icnf file, you can use the scripts from [CnC](https://github.com/marijnheule/CnC) 

Either using an incremental solver like ilingeling

  `./lingeling/ilingeling <form.icnf> -b <number of cores>` 

Or by creating individual CNF formulas for each cube and solving them indepently. 

  `sh solve-icnf.sh <form.icnf> <number of cores> <path to solver> <timeout in seconds>`
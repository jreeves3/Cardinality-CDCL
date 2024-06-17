#include "cnf2knf.hpp"
#include "direct_AMO.hpp"
#include "encoded_AMO.hpp"
#include "ALK.hpp"

namespace cnf2knf {

using namespace std;

vector<int> flatten_vectors (vector<vector<int>> & clauses) {
    vector<int> res;
    for (auto clause : clauses) {
        for (auto lit : clause) {
            res.push_back (lit);
        }
        res.push_back (0);
    }
}

bool Cnf_extractor::validate_constraint (vector<int> &problem_variables, vector<int> &encoding_variables,  vector<int> &clause_ids) {
   // normalize variables and clauses
   vector<vector<int>> normalized_clauses;
   vector<int> literals;
   unordered_map<int,int> to_normalization;
   unordered_map<int,int> from_normalization;

   int nproblem = problem_variables.size ();
   int nvar = 1;
   int nKlauses = 0;

    // cout << "Problem : ";
    // for (auto var : problem_variables) cout << var << " ";
    // cout << endl;
    // cout << "Encoding : ";
    // for (auto var : encoding_variables) cout << var << " ";
    // cout << endl;
    // cout << "clause_ids_set : ";
    // for (auto it = clause_ids.begin(); it != clause_ids.end(); it++) {
    //     for (auto lit : clauses[*it].literals) { 
    //         cout << lit << " ";
    //     }
    //     cout << endl;
    // }

   
   
   for (auto var : problem_variables) {
       to_normalization[var] = nvar++;
       from_normalization[nvar-1] = var;
   }
   for (auto var : encoding_variables) {
       to_normalization[var] = nvar++;
       from_normalization[nvar-1] = var;
   }
   for (auto cls_idx : clause_ids) {
       assert (!clauses[cls_idx].deleted);
       literals.clear ();
       for (auto lit : clauses[cls_idx].literals) {
           assert (to_normalization.find (abs(lit)) != to_normalization.end ());
           literals.push_back ((abs(lit)/lit) * to_normalization[abs(lit)]);
       }
       normalized_clauses.push_back (literals);
   }
   nvar--;

   //logging
   string temp_s;
   temp_s = "Problem variables : " + to_string (nproblem);
   log_ex_comment (temp_s, 2);
   temp_s = "encoding variables : " + to_string (nvar);
   log_ex_comment (temp_s, 2);
   log_ex_comment ("clauses : ", 2);
   for (auto literals : normalized_clauses) {
       temp_s = "";
       for (auto lit : literals) temp_s += to_string (lit) + " ";
       temp_s += "0";
       log_ex_comment (temp_s, 2);
   }



   // // Attempt lookup in cache
   // vector<int> flattened = flatten_vectors (normalized_clauses);
   // if (constraint_cache.count (flattened)) {
   //     // cache hit


   //     return nKlauses;
   // }
   
   // calls bdd_analyze
   analyzed_klauses.clear();
   log_ex_comment ("Entering bdd_analyze", 2);
   // cout << "BDD_analyze " << nvar << " " << nproblem << endl;
   nKlauses = bdd_analyze (nvar, nproblem, normalized_clauses);
   log_ex_comment ("Exiting bdd_analyze", 2);

   // adds klause if success
   if (nKlauses > 0) { // found valid klause(s)
    //    cout << "found clause\n";
       stats.bdd_analyze_successes += 1;

       // add klauses
       for (auto klause : analyzed_klauses) {
           // map literals in klause back to original labelling
           for (int i = 0; i < klause.get_size() ; i++) {
               int lit = klause.literals[i];
               klause.literals[i] = (abs(lit)/lit) * from_normalization[abs(lit)];
           }

           add_klause(klause, clause_ids); // if two klauses will just mark clause_ids deleted twice
       }

   } else { // failed 
//    cout << "Failed" << endl;
       stats.bdd_analyze_failures += 1;
   }

   return (nKlauses > 0);

}

void Cnf_extractor::mark_deleted_clauses (vector<int> clause_ids) {
    for (int cls_id : clause_ids) clauses[cls_id].deleted = true;
}

void Cnf_extractor::extract_direct () {

    // dummy extraction for now, entire formula is an AMO constraint
    // all clauses in formula

    // vector<int> clause_ids;
    // for (int i = 0; i < clauses.size(); i++) clause_ids.push_back(i);

    // int nKlauses = bdd_analyze (nvars, nvars, clause_ids);

    // if (nKlauses > 0) { // found valid klause(s)

    //     stats.bdd_analyze_successes += 1;

    //     // mark deleted clauses
    //     mark_deleted_clauses (clause_ids);

    //     // add klauses
    //     for (auto klause : analyzed_klauses) klauses.push_back (klause);
    //     analyzed_klauses.clear();

    // }

}

void Cnf_extractor::init () {

    this->logging = stoi (extractor_options["Extractor_logging"]); 

}

void print_help () {
    cout << "usage: .\\cnf2knf [options] <CNF_FORMULA>" << endl;
    cout << "-h : print this message" << endl;
    cout << "****" << endl;
    cout << " Options set to a value:" << endl;
    cout << "-Direct_timeout <float>       (default 1000s)" << endl;
    cout << "-Encoded_timeout <float>      (default 1000s)" << endl;
    cout << "-Extractor_logging <int>      (default 0)" << endl;
    cout << "-Engine_logging <int>         (default 0)" << endl;
    cout << "-BDD_logging <int>            (default 0)" << endl;
    cout << "****" << endl;
    cout << " Options set to true or false (--option=true OR --option=false)" << endl;
    cout << "--Direct_AMO           (default true)" << endl;
    cout << "--Direct_AMO_Small     (default true)" << endl;
    cout << "--Encoded_AMO          (default true)" << endl;
    cout << "--Write_KNF            (default true)" << endl;
}

int Cnf_extractor::main (int argc, char ** argv) {
    int res = 0;

    // Initial options that lead to exit
    if (argc == 2) {
        const char * temp_s = argv[1];
        if (!strcmp (temp_s, "-h")) {
            print_help ();
            return -1;
        }
    }
    parse_options(argc,argv);
    init ();

    // Parse input CNF formula
    char * input_file = argv[argc-1];
    parse_cnf(input_file);

    // // Extract direct encoding
    // extract_direct();

    // // Extract other encodings

    // // Write Stats
    // stats.write_stats();

    // // Write generated KNF formula
    // write_knf_formula();

    return res;
}

string literals2str (vector<int> literals) {
    string s;
    for (auto l : literals) s += to_string(l) + " ";
    return s;
}

void Cnf_extractor::write_knf_formula () {
    int nClauses_kept = 0;
    for (auto clause : clauses) nClauses_kept += (clause.deleted)?0:1;
    
    // header
    cout << "p knf " << nvars << " " << nClauses_kept + klauses.size() << endl;

    // klauses
    for (auto klause : klauses)
        cout << "k " << klause.cardinality_bound << " " << literals2str(klause.literals) << "0" << endl;

    // clauses
    for (auto clause : clauses) {
        if (clause.deleted) continue;
        cout << literals2str(clause.literals) << "0" << endl;
    }
}

void process_stats (Cnf_extractor * cnf_extractor, vector<Extraction_engine*> extraction_engines) {
    

    assert (extraction_engines.size() == 3);

    Direct_AMO *d_AMO = (Direct_AMO *) extraction_engines[0];
    Encoded_AMO *e_AMO = (Encoded_AMO *) extraction_engines[1];
    Encoded_AMO *e_other = (Encoded_AMO *) extraction_engines[2];

    int total_constraints = 0;
    // if (d_AMO != NULL) total_constraints += d_AMO->stats->nconstraints;
    // if (e_AMO != NULL) total_constraints += e_AMO->stats->nconstraints;
    for (auto clause : cnf_extractor->clauses) {
        if (!clause.deleted) total_constraints++;
        // else {
        //     for (auto lit : clause.literals) cout << lit << " ";
        // } cout << endl;
    }

    int bdd_successes, bdd_failures, total_card_constraints;
    bdd_successes = bdd_failures = total_card_constraints = 0;

    cout.precision(3);

    cout << "c Clausal constraints: " << total_constraints << endl;
    if (d_AMO != NULL) {
        Stats * stats = d_AMO->stats;
        total_card_constraints += stats->nconstraints;
        cout << "c Direct AMO constraints: " << stats->nconstraints << endl;
        if (stats->nconstraints > 0) {
            string temp_s = "";
            vector<tuple<int,int>> pair_sizes;
            for (auto it = stats->constraint_sizes.begin(); it != stats->constraint_sizes.end(); it++) {
                pair_sizes.push_back (tuple<int,int>{it->first,it->second});
                // cout << it->first << "  " << it->second << endl;
            }
            sort (pair_sizes.begin(), pair_sizes.end(), [](tuple<int,int> l1, tuple<int,int> l2) { return get<0>(l1) < get<0>(l2); });
            for (auto tp : pair_sizes) temp_s += to_string (get<0>(tp)) + ":" + to_string (get<1>(tp)) + " ";

            cout << "c Direct AMO sizes: " << temp_s << endl;
        }

        cout << "c Direct AMO seconds: " << stats->get_final_time () + stats->extra_time << endl;

        if (d_AMO->reached_timeout) cout << "c Direct reached timeout: " << d_AMO->timeout << endl;
    }

    if (e_AMO != NULL) {
        Stats * stats = e_AMO->stats;
        total_card_constraints += stats->nconstraints;
        cout << "c Encoded AMO constraints: " << stats->nconstraints << endl;
        if (stats->nconstraints > 0) {
            string temp_s = "";
            vector<tuple<int,int>> pair_sizes;
            for (auto it = stats->constraint_sizes.begin(); it != stats->constraint_sizes.end(); it++) {
                pair_sizes.push_back (tuple<int,int>{it->first,it->second});
                // cout << it->first << "  " << it->second << endl;
            }
            sort (pair_sizes.begin(), pair_sizes.end(), [](tuple<int,int> l1, tuple<int,int> l2) { return get<0>(l1) < get<0>(l2); });
            for (auto tp : pair_sizes) temp_s += to_string (get<0>(tp)) + ":" + to_string (get<1>(tp)) + " ";

            cout << "c Encoded AMO sizes: " << temp_s << endl;

            cout << "c Encoding variables eliminated: " << stats->eliminated_variables.size () << endl ;

            temp_s = "";
            sort (stats->eliminated_variables.begin(), stats->eliminated_variables.end());
            for (auto ev: stats->eliminated_variables) temp_s += to_string (ev) + " ";
            cout << "c Eliminated variables IDs: " << temp_s << endl;

            
        }

        cout << "c Encoded AMO seconds: " << stats->get_final_time () + stats->extra_time << endl;

        if (e_AMO->reached_timeout) cout << "c Encoded reached timeout: " << e_AMO->timeout << endl;

        bdd_successes += stats->bdd_analyze_successes;
        bdd_failures += stats->bdd_analyze_failures;
    }

    if (e_other != NULL) {
        Stats * stats = e_other->stats;
        total_card_constraints += stats->nconstraints;
        cout << "c Other constraints: " << stats->nconstraints << endl;
        if (stats->nconstraints > 0) {
            string temp_s = "";
            vector<tuple<int,int>> pair_sizes;
            for (auto it = stats->constraint_sizes.begin(); it != stats->constraint_sizes.end(); it++) {
                pair_sizes.push_back (tuple<int,int>{it->first,it->second});
                // cout << it->first << "  " << it->second << endl;
            }
            sort (pair_sizes.begin(), pair_sizes.end(), [](tuple<int,int> l1, tuple<int,int> l2) { return get<0>(l1) < get<0>(l2); });
            for (auto tp : pair_sizes) temp_s += to_string (get<0>(tp)) + ":" + to_string (get<1>(tp)) + " ";

            cout << "c Other constraint sizes: " << temp_s << endl;

            cout << "c Other variables eliminated: " << stats->eliminated_variables.size () << endl ;

            temp_s = "";
            sort (stats->eliminated_variables.begin(), stats->eliminated_variables.end());
            for (auto ev: stats->eliminated_variables) temp_s += to_string (ev) + " ";
            cout << "c Other eliminated variables IDs: " << temp_s << endl;

            
        }

        cout << "c Other constraint seconds: " << stats->get_final_time () + stats->extra_time << endl;

        if (e_AMO->reached_timeout) cout << "c Other reached timeout: " << e_AMO->timeout << endl;

        bdd_successes += stats->bdd_analyze_successes;
        bdd_failures += stats->bdd_analyze_failures;
    }

    cout << "c BDD analyze successes " << cnf_extractor->stats.bdd_analyze_successes << endl;
    cout << "c BDD analyze failures " << cnf_extractor->stats.bdd_analyze_failures << endl;

    cout << "c Total seconds: " << cnf_extractor->stats.get_final_time () 
    << endl;

    cout << "c Total extracted constraints: " << total_card_constraints 
    << endl;

}

void Stats::write_stats() {

    auto end_time = chrono::system_clock::now();
    chrono::duration<double>  total_time = end_time - start_time;

    cout << "c Statistics for cardinality extraction" << endl;
    cout << "c Cache hits " << cache_hits << endl;
    cout << "c Cache misses " << cache_misses << endl;
    cout << "c Number eliminated variables " << eliminated_variables.size() << endl;
    cout << "c bdd analyze successes " << bdd_analyze_successes << endl;
    cout << "c bdd analyze failures " << bdd_analyze_failures << endl;
    cout << "c Total time " << total_time.count() << " seconds" << endl;
}

int run_extraction_engines (Cnf_extractor * cnf_extractor) {
    vector<Extraction_engine*> extraction_engines;
    Direct_AMO *direct_AMO = NULL;
    Encoded_AMO *encoded_AMO = NULL;
    Encoded_AMO *encoded_Others = NULL;
    double direct_AMO_timeout, encoded_AMO_timeout;
    unordered_map<string, string> engine_options;
    unordered_map<string, string> extractor_options = cnf_extractor->extractor_options;
    int logging = stoi (extractor_options["Engine_logging"]);

    direct_AMO_timeout = encoded_AMO_timeout = 1000;


    if (stof (extractor_options["Direct_timeout"]) > 0 ) {
        direct_AMO_timeout = stof (cnf_extractor->extractor_options["Direct_timeout"] );
    }
    if (stof (extractor_options["Encoded_timeout"]) > 0 )
        encoded_AMO_timeout = stof (cnf_extractor->extractor_options["Encoded_timeout"] );


    if (extractor_options["Direct_AMO"] == "true") { 
        direct_AMO = new Direct_AMO (cnf_extractor,logging);
        // cout << "c find direct AMOS" << endl;
        direct_AMO->init (engine_options);
        direct_AMO->run (direct_AMO_timeout);  
        direct_AMO->stats->set_end_time ();

        direct_AMO->clear_data ();  
    }



    if (extractor_options["Encoded_AMO"] == "true") { 
        encoded_AMO = new Encoded_AMO (cnf_extractor,logging);
        // cout << "c find encoded AMOS" << endl;
        encoded_AMO->init (engine_options);
        encoded_AMO->run (encoded_AMO_timeout);  
        encoded_AMO->stats->set_end_time ();
    }

    double small_time = 0;
    if (extractor_options["Direct_AMO"] == "true" && extractor_options["Direct_AMO_Small"] == "true") { 
        // cout << "c find small direct AMOS" << endl;
        small_time = direct_AMO->find_small_AMOs (); 
        direct_AMO->stats->extra_time = small_time;
    }

    if (extractor_options["Encoded_Others"] == "true") {
        engine_options["AMO"] = "false";
        engine_options["Max_Size"] = "3";
        encoded_Others = new Encoded_AMO (cnf_extractor,logging);
        encoded_Others->init (engine_options);
        encoded_Others->run (encoded_AMO_timeout);  
        encoded_Others->stats->set_end_time ();
    }

    extraction_engines.push_back (direct_AMO);
    extraction_engines.push_back (encoded_AMO);
    extraction_engines.push_back (encoded_Others);

    cnf_extractor->stats.set_end_time ();

    process_stats(cnf_extractor, extraction_engines);

    if (extractor_options["Write_KNF"] == "true")
        cnf_extractor->write_knf_formula();

    delete (direct_AMO);
    delete (encoded_AMO);
    delete (encoded_Others);

    return 0;

}

}



int main (int argc, char ** argv) {
  cnf2knf::Cnf_extractor * cnf_extractor;
  cnf_extractor = new cnf2knf::Cnf_extractor();
  int res;
  res = cnf_extractor->main (argc, argv);
  if (res) return 0;

  cnf2knf::run_extraction_engines (cnf_extractor);

  return res;
}

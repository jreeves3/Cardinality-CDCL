#ifndef CNF2KNF_HPP
#define CNF2KNF_HPP

#include <string>
#include <string.h>
#include <vector>
#include <iostream>
#include <chrono>
#include <unordered_map>
#include <map>
#include <set>
#include <algorithm>
#include "assert.h"

#include "klause.hpp"


namespace cnf2knf {

using namespace std;

typedef tuple<int, int> pair_key;

// hash for unordered map on (int,int) key
struct pair_key_hash //: public unary_function<pair_key, size_t> //
{
 size_t operator()(const pair_key& k) const
 {
   return std::get<0>(k) + std::get<1>(k) * (2147483647 + 1);
 }
};

// hash for unordered map on (int,int) key
struct vec_key_hash //: public unary_function<pair_key, size_t> //
{
 size_t operator()(const vector<int>& k) const
 {
    int hash = 0;
    for (int i = 0; i < k.size(); i++) hash += i * k[i];
    return hash;
 }
};

// comparison for ordered map
struct compare_pair {
    bool operator()(const pair_key &l1, const pair_key &l2) 
        const {   if (get<0>(l1) < get<0>(l2)) return true;
            if (get<0>(l1) == get<0>(l2)) return (get<1>(l1) < get<1>(l2));
            return false; }
};



class Stats {

    public:

        int cache_hits;
        int cache_misses;

        int bdd_analyze_failures;
        int bdd_analyze_successes;

        int nconstraints;
        unordered_map<int,int> constraint_sizes;
        
        chrono::system_clock::time_point start_time;
        chrono::system_clock::time_point final_time;

        double extra_time;

        vector<int> eliminated_variables;

        Stats() {
            cache_hits = 0;
            cache_misses = 0;
            bdd_analyze_failures = 0;
            bdd_analyze_successes = 0;

            nconstraints = 0;

            extra_time = 0;

            start_time = chrono::system_clock::now();
            
        }

        double get_elapsed_time () {
            auto end_time = chrono::system_clock::now();
            chrono::duration<double>  total_time = end_time - start_time;

            return (total_time.count ());
        }

        double get_final_time () {
            // auto end_time = chrono::system_clock::now();
            chrono::duration<double>  total_time = final_time - start_time;

            return (total_time.count ());
        }

        void set_end_time() {
            final_time = chrono::system_clock::now();
        }

        void write_stats ();

};

class Cnf_extractor {

    public:

        int             nvars;   // Number of variables
        vector<Klause>  clauses; // Clauses from original CNF formula
        vector<Klause>  klauses; // All klauses generated during extraction

        unordered_map<string, string> extractor_options;

        int logging;

        vector<Klause>  analyzed_klauses; // Klauses generated in current analyze step

        Stats stats;

        unordered_map<vector<int>, vector<Klause>, vec_key_hash> constraint_cache;

        Cnf_extractor () {
            // populate options
            extractor_options["Direct_timeout"] = "1000";
            extractor_options["Encoded_timeout"] = "1000"; 
            extractor_options["Extractor_logging"] = "0";
            extractor_options["Engine_logging"] = "0";
            extractor_options["BDD_logging"] = "0";
            extractor_options["Direct_AMO"] = "true";
            extractor_options["Direct_AMO_Small"] = "true";
            extractor_options["Encoded_AMO"] = "true";
            extractor_options["Encoded_Others"] = "false";
            extractor_options["Write_KNF"] = "true";
            
            }

        void init ();

        int main (int argc, char ** argv);

        // extract directly encoded AMO constraints
        void extract_direct();

        // Analyze set of clauses with data variables numbered from 1 to ndata
        // and encoding variables numbered from ndata+1 to nvar
        // Return number of klauses generated (0 if failure)
        // Place new klauses into analyzed_klauses 
        //   which will be cleared before each call to bdd_analyze
       int bdd_analyze (int nvar, int ndata, vector<vector<int>> &constraint_clauses);

       bool validate_constraint (vector<int> &problem_variables, vector<int> &encoding_variables,  vector<int> &clause_ids);

        // parsing
        int parse_options (int argc, char ** argv);
        bool findOption(char ** start, char ** end, const string & marker);
        bool commandLineParseOption(char ** start, char ** end, const string & marker);

        int parse_cnf (char *);

        // writing
        void write_knf_formula ();

        void add_klause (Klause klause, vector<int> clause_ids) {
            klauses.push_back (klause);
            mark_deleted_clauses (clause_ids);
        }

        void log_ex_comment (string line, int log_if) {
        if (log_if <= logging) {
            cout << "c " << line << endl; 
        }
    }

        private :

        void mark_deleted_clauses (vector<int> clause_ids);


};

class Extraction_engine {
    public :

    double timeout;
    bool   reached_timeout;
    int logging;

    Cnf_extractor * cnf_extractor;
    Stats * stats;

    Extraction_engine (Cnf_extractor * cnf_extractor, int logging) {
        this->cnf_extractor = cnf_extractor;
        reached_timeout = false;
        this->logging = logging;
    }

    // dictionary containing parameters for initializing this engine
    virtual void init (unordered_map<string, string> engine_options) {};
    
    // start extraction with timeout
    virtual void run (double timeout) {};

    // write stats to standard out
    virtual void write_stats () {};

    void log_comment (string line, int log_if) {
        if (log_if <= logging) {
            cout << "c " << line << endl; 
        }
    }

    
};




}

#endif

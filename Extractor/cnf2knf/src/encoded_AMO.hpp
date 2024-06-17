#ifndef ENCODED_AMO_HPP
#define ENCODED_AMO_HPP

#include "cnf2knf.hpp"


namespace cnf2knf {

using namespace std;

class Encoded_AMO : public Extraction_engine {

    public: 

        int max_clause_size;
        bool AMO;

        unordered_map<int, tuple<int, int>> variable_polarity_map;
        unordered_map<int, vector<int>> encoding_variable_map;
        unordered_map<int, vector<int>> problem_variable_map;

        using Extraction_engine::Extraction_engine;

        void init (unordered_map<string, string> engine_options) {

            max_clause_size = 2; // default value
            AMO = true;

        }

        void run (double timeout) {

            string temp_s;

            this->stats = new Stats(); // start clock running

            this->timeout = timeout;
            
            classify_variables();
            generate_maps();

            //logging (maps)
            log_comment ("ploarity map " , 2);
            for (auto it = variable_polarity_map.begin() ; it != variable_polarity_map.end (); it++ ) {
                temp_s = to_string (it->first) + " : " + to_string(get<0>(it->second)) + " , " + to_string (get<1>(it->second)) ;
                log_comment (temp_s, 2);
            }
            log_comment ("problem variable map " , 2);
            for (auto it = problem_variable_map.begin() ; it != problem_variable_map.end (); it++ ) {
                temp_s = to_string(it->first) + " : ";
                for (auto it2 = it->second.begin(); it2 != it->second.end(); it2++) {
                    temp_s += to_string (*it2) + " ";
                }
                log_comment (temp_s, 2);
            }
            log_comment ("encoding variable map " , 2);
            for (auto it = encoding_variable_map.begin() ; it != encoding_variable_map.end (); it++ ) {
                temp_s = to_string(it->first) + " : ";
                for (auto it2 = it->second.begin(); it2 != it->second.end(); it2++) {
                    temp_s += to_string (*it2) + " ";
                }
                log_comment (temp_s, 2);
            }


            while (encoding_variable_map.size() ){

                if (stats->get_elapsed_time() > timeout) {
                    stats->set_end_time();
                    reached_timeout = true; 
                    break;
                }

                get_cluster ();

                //logging (cluster)
                temp_s = "problem_variable_set : ";
                for (auto it = problem_variable_set.begin(); it != problem_variable_set.end(); it++) temp_s += to_string (*it) + " ";
                log_comment (temp_s, 1);
                temp_s = "encoding_variable_set : ";
                for (auto it = encoding_variable_set.begin(); it != encoding_variable_set.end(); it++) temp_s += to_string (*it) + " ";
                log_comment (temp_s, 1);
                temp_s = "clause_ids_set : ";
                for (auto it = clause_ids_set.begin(); it != clause_ids_set.end(); it++) temp_s += to_string (*it) + " ";
                log_comment (temp_s, 1);

                if (!encoding_variable_not_in_cluster || problem_variable_set.size() < 3) continue;

                if (problem_variable_set.size () > 300) continue;

                if (encoding_variable_set.size () > 600) continue;

                if (AMO && encoding_variable_set.size () > 3 * problem_variable_set.size ()) continue;

                if (!AMO && 2 * encoding_variable_set.size () > problem_variable_set.size () * problem_variable_set.size ()) continue;

                if (problem_variable_set.size () > 10 && 3 * encoding_variable_set.size () < problem_variable_set.size () ) continue;

                expand_cluster ();

                bool normalized = normalize_cluster ();

                if (normalized) {
                    vector<int> clause_ids;
                    clause_ids.assign (clause_ids_set.begin(), clause_ids_set.end());

                    //logging (expanded cluster)
                    temp_s = "clause_ids_set : ";
                    for (auto it = clause_ids_set.begin(); it != clause_ids_set.end(); it++) temp_s += to_string (*it) + " ";
                    log_comment (temp_s, 1);

                    bool validated = cnf_extractor->validate_constraint (problem_variables, encoding_variables, clause_ids);

                    if (validated) { 
                        // stats

                        // constraints
                        int csize = problem_variables.size ();
                        stats->nconstraints++;
                        if (stats->constraint_sizes.find (csize) == stats->constraint_sizes.end ())
                            stats->constraint_sizes[csize] = 0;
                        stats->constraint_sizes[csize]++;

                        // eliminated variables
                        for (auto ev : encoding_variables) {
                            stats->eliminated_variables.push_back (ev);
                        }

                    }   
                }
            }
            

        }

        void write_stats () {}


    private:

    bool encoding_variable_not_in_cluster;
    set<int> problem_variable_set;
    set<int> encoding_variable_set;
    set<int> clause_ids_set;
    vector<int> problem_variables;
    vector<int> encoding_variables;

    // build polarity map
    void classify_variables () {
        int var;
        bool pos,neg;

        for (int cls_idx = 0; cls_idx < cnf_extractor->clauses.size(); cls_idx++) {
            // skip deleted clauses
            if (cnf_extractor->clauses[cls_idx].deleted) continue;

            // skip clauses smaller than max_clause_size
            if (cnf_extractor->clauses[cls_idx].get_size () > max_clause_size) continue;

            for (auto lit : cnf_extractor->clauses[cls_idx].literals) {
                var = abs(lit);
                auto map_element = variable_polarity_map.find (var);
                pos = neg = false;
                if (map_element != variable_polarity_map.end()) {
                    pos = get<0>(map_element->second);
                    neg = get<1>(map_element->second);
                }
                if (lit < 0) neg = true;
                else pos = true;

                variable_polarity_map[var] = tuple<bool,bool>{pos,neg};

            }
        }
    }

    void generate_maps () {
        int var;
        bool pos, neg, assigned;

        for (auto it : variable_polarity_map) {
            var = it.first;
            pos = get<0>(it.second);
            neg = get<1>(it.second);

            if (pos && neg) encoding_variable_map[var] = vector<int>();
            else problem_variable_map[var] = vector<int>();
        }


        for (int cls_idx = 0; cls_idx < cnf_extractor->clauses.size(); cls_idx++) {
            // skip deleted clauses
            if (cnf_extractor->clauses[cls_idx].deleted) continue;

            assigned = false;
            for (auto lit : cnf_extractor->clauses[cls_idx].literals) {
                var = abs (lit);

                if (encoding_variable_map.find (var) != encoding_variable_map.end()) encoding_variable_map[var].push_back (cls_idx);
                else if (problem_variable_map.find (var) != problem_variable_map.end()) problem_variable_map[var].push_back (cls_idx);

            }
        }
    }

    void get_cluster () {
        encoding_variable_not_in_cluster = true;
        problem_variable_set.clear ();
        encoding_variable_set.clear ();
        clause_ids_set.clear ();

        int var;
        set<int> tainted_variable_set;
        set<int> trace_variable_set;

        auto it = encoding_variable_map.begin ();

        int encoding_variable = it->first;

        trace_variable_set.insert (encoding_variable);
        encoding_variable_set.insert (encoding_variable);

        while (trace_variable_set.size ()) {
            encoding_variable = *(trace_variable_set.begin());
            trace_variable_set.erase (encoding_variable);

            // log_comment ("Trace encoding variable "+to_string(encoding_variable), 2);

            for (auto cls_idx : encoding_variable_map[encoding_variable]) {
                clause_ids_set.insert (cls_idx);
                
                for (auto lit : cnf_extractor->clauses[cls_idx].literals) {
                    var = abs (lit);

                    if (var == encoding_variable || problem_variable_set.find (var) != problem_variable_set.end () || encoding_variable_set.find (var) != encoding_variable_set.end ()) continue;

                    if (encoding_variable_map.find (var) != encoding_variable_map.end ()) {
                        trace_variable_set.insert (var);
                        encoding_variable_set.insert (var);
                    }
                    else if (problem_variable_map.find (var) != problem_variable_map.end ()) {
                        problem_variable_set.insert (var);
                    }
                    else {
                        // encoding variable not fully contained in cluster
                        encoding_variable_not_in_cluster = true;
                        // skipping code here that cannot be reached
                    }
                }
            }
            encoding_variable_map.erase (encoding_variable);
        }

        while (tainted_variable_set.size ()) {
            encoding_variable = *(tainted_variable_set.begin());
            tainted_variable_set.erase (encoding_variable);

            for (auto cls_idx : encoding_variable_map[encoding_variable]) {
                for (auto lit : cnf_extractor->clauses[cls_idx].literals) {
                    var = abs (lit);
                    if (var == encoding_variable) continue;
                    if (encoding_variable_set.find (var) != encoding_variable_set.end ()) tainted_variable_set.insert (var);
                }
            }
            encoding_variable_map.erase (encoding_variable);
        }

    }

    void expand_cluster () {
        int problem_variable, var;
        bool in_cluster;

        for (auto it = problem_variable_set.begin(); it != problem_variable_set.end (); it++) {
            problem_variable = *it;

            for (auto cls_idx : problem_variable_map[problem_variable]) {
                if (cnf_extractor->clauses[cls_idx].deleted) continue;

                Klause clause = cnf_extractor->clauses[cls_idx];

                if (clause.get_size () > 2) continue;

                in_cluster = true;

                for (auto lit : clause.literals) {
                    var = abs(lit);
                    if (problem_variable_set.find (var) == problem_variable_set.end () && encoding_variable_set.find (var) == encoding_variable_set.end ()) {in_cluster = false; break;}
                }
                if (in_cluster) clause_ids_set.insert (cls_idx);
            }
        }
    }

    bool normalize_cluster () {
        problem_variables.clear ();
        encoding_variables.clear ();
        vector<int> clause_ids;
        int var; 

        if (!clause_ids_set.size()) return false;

        clause_ids.assign (clause_ids_set.begin () , clause_ids_set.end ());
        sort (clause_ids.begin(), clause_ids.end());

        for (auto cls_idx : clause_ids) {
            Klause clause = cnf_extractor->clauses[cls_idx];
            for (auto lit : clause.literals) {
                var = abs(lit);
                if (problem_variable_set.find (var) != problem_variable_set.end ()) {
                    problem_variables.push_back (var);
                    problem_variable_set.erase (var);
                }
                else if (encoding_variable_set.find (var) != encoding_variable_set.end ()) {
                    encoding_variables.push_back (var);
                    encoding_variable_set.erase (var);
                } 
                else {
                    if ((find (problem_variables.begin(),problem_variables.end(), var) == problem_variables.end()  && find (encoding_variables.begin(),encoding_variables.end(), var) == encoding_variables.end()))
                        return false;
                }
            }
        }
        assert (!problem_variable_set.size());
        assert (!encoding_variable_set.size());
        return true;
    }

};

}

#endif
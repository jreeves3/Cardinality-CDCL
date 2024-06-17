#ifndef ALK_HPP
#define ALK_HPP

#include "cnf2knf.hpp"


namespace cnf2knf {

using namespace std;

class ALK : public Extraction_engine {

    public: 

        using Extraction_engine::Extraction_engine;

        void init (unordered_map<string, string> engine_options) {
            ;
        }

        void run (double timeout) {

            string temp_s;

            this->stats = new Stats(); // start clock running

            this->timeout = timeout;
            
            bool found = true;
            while (found) {
                // classify_variables();

                found = false;

                int old_succ = cnf_extractor->stats.bdd_analyze_successes;

                vector<int> e_vars;
                vector<int> p_vars;
                vector<int> cls_ids;

                for (int i = 1; i <= 49 ; i++) p_vars.push_back (i);
                for (int i = 50; i <= 281; i++) e_vars.push_back (i);
                for (int i = 91; i <= 1000; i++) cls_ids.push_back (i);

                cnf_extractor->validate_constraint (p_vars, e_vars, cls_ids);
                break;

                // for (unsigned i = 0; i < encoding_variable_list.size(); i++ ) {
                //     vector<int> e_vars = encoding_variable_list[i];
                //     vector<int> p_vars = problem_variable_list[i];
                //     vector<int> cls_ids = cls_ids_list[i];

                //     cnf_extractor->validate_constraint (p_vars, e_vars, cls_ids);
                // }

                 int new_succ = cnf_extractor->stats.bdd_analyze_successes;

                 if (new_succ > old_succ) found = true;

                // check timeout (may to need nest this)
                if (stats->get_elapsed_time() > timeout) {
                    stats->set_end_time();
                    reached_timeout = true; 
                    break;
                }
            }

        }

        void write_stats () {}


    private:

    unordered_map<int, int> variable_polarities;

    set<int> temp_depends;

    unordered_map<int, set<int>> lit2cls_idxs;
    unordered_map<int, vector<int>> lit_dependencies;
    unordered_map<int, set<int>> rev_lit_dependencies;
    vector<int> literal_types;
    vector<int> variable_types;

    vector<int> variable_max_cls_size;

    vector<vector<int>> encoding_variable_list;
    vector<vector<int>> problem_variable_list;
    vector<vector<int>> cls_ids_list;

    set<int> seen_e_vars;

    void lit2cls_map () {
        for (unsigned cls_idx = 0; cls_idx < cnf_extractor->clauses.size (); cls_idx++) {
            auto cls = cnf_extractor->clauses[cls_idx];
            if (cls.deleted) continue;
            for (auto lit : cls.literals) {
                lit2cls_idxs[lit].insert (cls_idx);
            }
        }
    }

    void in_clause_size_n () {
        for (int i = 0; i <= cnf_extractor->nvars; i++)
            variable_max_cls_size.push_back (0);
        
        for (auto cls : cnf_extractor->clauses) {
            if (cls.deleted) continue;
            unsigned size = cls.literals.size ();
            for (auto lit : cls.literals) {
                if (size > variable_max_cls_size [abs (lit)])
                    variable_max_cls_size [abs (lit)] = size;
            }
        }
    }

    void make_maps () {

        lit2cls_idxs.clear ();
        lit2cls_map ();

        variable_max_cls_size.clear ();
        in_clause_size_n ();

    }

    // Checks is the formula F(lit) is pure,
    // i.e., all variables occur in a single polarity.
    bool is_pure_formula (int in_lit) {
        bool res = true;

        variable_polarities.clear ();
        temp_depends.clear ();

        for (auto cls_idx : lit2cls_idxs[in_lit]) {
            // skip deleted clauses
            if (cnf_extractor->clauses[cls_idx].deleted) continue;

            // check if literals are pure in all clauses F(lit)
            for (auto lit : cnf_extractor->clauses[cls_idx].literals) {
                int var = abs(lit);
                int polarity = var/lit;
                auto map_element = variable_polarities.find (var);
                if (map_element != variable_polarities.end()) {
                    if (map_element->second != polarity) {
                        res = false;
                        break;
                    }
                } else {
                    variable_polarities[var] = polarity;
                    if (lit != in_lit)
                        temp_depends.insert (lit);
                }
            }
            if (!res) break;
        }

        if (res) {
            // add dependencies for pure formula,
            // i.e., all variables in F(lit)
            // and reverse dependencies for post-processing
            for (auto map_element = variable_polarities.begin (); map_element != variable_polarities.end(); map_element++) {
                rev_lit_dependencies[map_element->first].insert (in_lit);
                // cout << in_lit << " depends on " << map_element->first << endl;
            }
            lit_dependencies[in_lit] = vector<int> (temp_depends.begin(), temp_depends.end ());
            // exit (1);
        }

        return res;
    }

    // index lits into an array
    // -1,1,-2,2, ... nvar (2 *nvar-1)
    int lit2var (int lit) {if (lit > 0) return 2*lit-1; else return 2*(abs(lit))-2;}

    void variables_from_clauses (int in_lit, set<int> &variables) {
        for (auto cls_idx : lit2cls_idxs[in_lit]) {
            // skip deleted clauses
            if (cnf_extractor->clauses[cls_idx].deleted) continue;

            for (auto lit : cnf_extractor->clauses[cls_idx].literals) {
                if (lit == in_lit) continue;
                int var = abs(lit);
                // add to set
                variables.insert (var);
                // if (variables.find (var) == variables.end ()}// && variable_types [var] != 4) {
                    
                // } 
            }
        }
    }

    void variables_from_clauses_with_ids (int in_lit, set<int> &variables, set<int> &cls_ids) {
        for (auto cls_idx : lit2cls_idxs[in_lit]) {
            // skip deleted clauses
            if (cnf_extractor->clauses[cls_idx].deleted) continue;
            
            cls_ids.insert (cls_idx);

            for (auto lit : cnf_extractor->clauses[cls_idx].literals) {
                if (lit == in_lit) continue;
                int var = abs(lit);
                // add to set
                if (variable_types [var] != 4)
                    variables.insert (var);
            }
        }
    }

    // vector<int> get_problem_variables () {
    //     set<int> problem_variables;

    //     for (int var = 1; var <= cnf_extractor->nvars; var++ ) {
    //         if (variable_types [var] == 4) {
    //             // Get variables from clauses
    //             variables_from_clauses (var, problem_variables);
    //             variables_from_clauses (-var, problem_variables);
    //         }
    //     }

    //     return vector<int> (problem_variables.begin (), problem_variables.end ());
    // }

    void get_problem_variables (set<int> e_vars, set<int> &p_vars, set<int> &cls_ids) {

        for (auto var : e_vars) {
            variables_from_clauses_with_ids (var, p_vars, cls_ids);
            variables_from_clauses_with_ids (-var, p_vars, cls_ids);
        }

    }

    void get_encoding_variables (int in_var, set<int> &variables) {

        set<int> frontier;

        frontier.insert (in_var);

        while (!frontier.empty ()) {
            set<int> next_frontier;

            for (auto var: frontier) {
                
                // touched variables
                set<int> new_variables;
                variables_from_clauses (var, new_variables);
                variables_from_clauses (-var, new_variables);

                for (auto new_var : new_variables) {
                    if (seen_e_vars.find (new_var) != seen_e_vars.end ())
                        continue;
                    if (variable_types [new_var] != 4) 
                        continue;
                    seen_e_vars.insert (new_var);
                    variables.insert (new_var);
                    next_frontier.insert (new_var);
                }
            }

            frontier.clear ();
            frontier.insert (next_frontier.begin(), next_frontier.end());
            next_frontier.clear();
        }
    }

    void expand_encoding_variables (int var) {
        set<int> e_vars, p_vars, cls_ids;

        // expand encoding variables
        get_encoding_variables (var, e_vars); 

        // expand to problem variables and get
        get_problem_variables (e_vars, p_vars, cls_ids);

        // add to list of found constraints
        encoding_variable_list.push_back (vector<int> (e_vars.begin (), e_vars.end ()));
        problem_variable_list.push_back (vector<int> (p_vars.begin (), p_vars.end ()));
        cls_ids_list.push_back (vector<int> (cls_ids.begin (), cls_ids.end ()));
    }


    // Variable types:
    //    0 : untyped (initial)
    //    1 : pure (first pass)
    //    2 : unpure (first pass)
    //    3 : problem (some of the pure from first pass)
    //    4 : encoding (some of the pure from first pass)
    void classify_variables () {

        string log_s;

        literal_types.clear ();
        variable_types.clear ();

        int nvars = cnf_extractor->nvars;
        for (unsigned i = literal_types.size(); i <= 2*nvars; i++ )
            literal_types.push_back (0);
        
        // will I ever need to reset variable types?
        // Yes, if clauses are deleted...
        for (int i = 0; i <= 2*nvars; i++) {
            literal_types[i] = 0;
        }

        for (int i = 0; i <= nvars; i++) {
            variable_types.push_back (0);
        }

        make_maps ();

        // reset maps
        lit_dependencies.clear ();
        rev_lit_dependencies.clear ();
        
        set<int> frontier;
        vector<int> problem_variables;
        // check if each lit is pure and build dependency map
        for (int lit = -nvars; lit <= nvars; lit++) {
            if (!lit) continue; // not a literal

            if (variable_max_cls_size [abs (lit)] > 3 || variable_max_cls_size [abs (lit)] == 0)
                literal_types [lit2var (lit)] = 2;
            else if (is_pure_formula (lit)) {
                literal_types [lit2var (lit)] = 1;
                // preload frontier with pure literals
                frontier.insert (lit);
            } else 
                literal_types [lit2var (lit)] = 2;
        }

        for (int i = 1; i <= nvars; i++) {
            if (literal_types [lit2var (-i)] == 2 && literal_types [lit2var (i)] == 2)
                variable_types[i] = 2;
        }

        // process dependencies
        bool first_pass = true;
        while (!frontier.empty ()) {
            set<int> next_frontier;

            // get non dependent variables (all unpure or encoding)
            for (auto lit: frontier) {
                // skip non pure, or already assigned types
                int lit_type = literal_types [lit2var (lit)]; 
                if (lit_type == 2 || lit_type == 4) continue;
                lit_type = literal_types [lit2var (-lit)]; 
                if (lit_type == 2 || lit_type == 4) continue;

                int var_type = variable_types [abs (lit)];
                if (var_type == 2 || var_type == 4) continue;

                //logging
                log_s = "checking literal: " + to_string(lit);
                log_comment (log_s , 3);

                // check if non dependent
                bool encoding = true;
                for (auto dep_lit: lit_dependencies[lit]) {
                    int dep_type = literal_types [lit2var (dep_lit)];
                    int var_type = variable_types [abs (dep_lit)];
                    if (dep_type == 1 && var_type == 0) {
                        encoding = false;
                        break;
                    }
                }
                if (encoding) {
                    //logging
                    log_s = "new encoding literal found: " + to_string(lit);
                    log_comment (log_s , 3);

                    literal_types [lit2var (lit)] = 4;
                    variable_types [abs (lit)] = 4;

                    bool problem_variable = true;
                    // add reverse depends onto frontier
                    for (auto rev_dep_lit: rev_lit_dependencies[lit]) {
                        if (literal_types [lit2var (rev_dep_lit)] == 1)
                            problem_variable = false;
                        if (next_frontier.find (rev_dep_lit) == next_frontier.end ()) {
                            next_frontier.insert (rev_dep_lit);
                            next_frontier.insert (-rev_dep_lit);
                        }
                    }
                    for (auto rev_dep_lit: rev_lit_dependencies[-lit]) {
                        if (literal_types [lit2var (rev_dep_lit)] == 1)
                            problem_variable = false;
                        if (next_frontier.find (rev_dep_lit) == next_frontier.end ()){
                            next_frontier.insert (rev_dep_lit);
                            next_frontier.insert (-rev_dep_lit);
                        }
                    }
                    // if (problem_variable) 
                    //     problem_variables.insert (abs(lit));
                }
            }

            if (first_pass) log_comment ("Finished first pass" , 3);

            // cout << "c size " << next_frontier.size () << endl;

            first_pass = false;
            frontier.clear ();
            frontier.insert (next_frontier.begin(), next_frontier.end());
            next_frontier.clear();
        }


        encoding_variable_list.clear ();
        problem_variable_list.clear ();
        cls_ids_list.clear ();
        seen_e_vars.clear();

        // Group encoding variables
        for (int var = 1; var <= nvars; var++) {
            if (variable_types [var] == 4 && seen_e_vars.find (var) == seen_e_vars.end ())
                expand_encoding_variables (var);
        }

        // get problem variables from encoding variables (closure of encoding clauses)
        // problem_variables = get_problem_variables ();

        //logging (maps)
        // log_comment ("problem variables " , 3);
        // log_s = "";
        // for (auto lit : problem_variables ) {
        //     log_s += to_string (lit) + " ";
        // } log_comment (log_s, 3);

        // log_comment ("encoding variables " , 3);
        // log_s = "";
        // for (int i = 1; i <= nvars; i++ ) {
        //     if (variable_types[i] == 4)
        //         log_s += to_string (i) + " ";
        // } log_comment (log_s, 3);

    }

};

}

#endif
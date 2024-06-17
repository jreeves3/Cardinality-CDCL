#ifndef DIRECT_AMO_HPP
#define DIRECT_AMO_HPP

#include "cnf2knf.hpp"


namespace cnf2knf {

using namespace std;

class Direct_AMO : public Extraction_engine {

    public: 

        // unordered_map<tuple<int, int>, int, pair_key_hash> clause_id_map;
        // unordered_map<int, set<int>> edge_map;

        // ordered map for determinism with clause order shuffling
        // logarithmic operations
        map<tuple<int, int>, int, compare_pair> clause_id_map;
        map<int, set<int>> edge_map;

        using Extraction_engine::Extraction_engine;

        // Option values

        void init (unordered_map<string, string> engine_options) {

            if (engine_options.find ("max count") != engine_options.end()) 
                int max_count = stoi (engine_options["max count"]);

        }

        void clear_data () {
          clause_id_map.clear();
          edge_map.clear();
        }

        void run (double timeout) {
            int l1,l2;

            this->stats = new Stats(); // start clock running
            this->timeout = timeout;

            generate_maps();

            // logging (maps)
            log_comment ("cls id map " , 4);
            for (auto it = clause_id_map.begin() ; it != clause_id_map.end (); it++ ) {
                string temp_s = to_string(get<0>(it->first)) + " , " + to_string (get<1>(it->first)) + " : " + to_string (it->second);
                log_comment (temp_s, 4);
            }
            log_comment ("edge map " , 4);
            for (auto it = edge_map.begin() ; it != edge_map.end (); it++ ) {
                string temp_s = to_string(it->first) + " : ";
                for (auto it2 = it->second.begin(); it2 != it->second.end(); it2++) {
                    temp_s += to_string (*it2) + " ";
                }
                log_comment (temp_s, 4);
            }


            while (clause_id_map.size ()) {

                if (stats->get_elapsed_time() > timeout) {
                    stats->set_end_time();
                    reached_timeout = true; 
                    break;
                }

                auto it = clause_id_map.begin ();
                l1 = get<0>(it->first);
                l2 = get<1>(it->first);

                expand_clique (l1);

                sort (clique_set.begin (), clique_set.end (), [](int l1, int l2) { return abs(l1) < abs(l2); });

                if (clique_set.size () < 3) {
                    // not interesting
                    l1 = clique_set[0];
                    l2 = clique_set[1];
                    remove_edge (l1, l2);
                    continue;
                }

                find_clique_clauses ();

                // logging (clique set and ids)
                string temp_s = "clique set : ";
                for (auto var : clique_set) temp_s += to_string (var) + " ";
                log_comment (temp_s, 1);
                temp_s = "clique ids : ";
                for (auto idx : clique_clause_ids) temp_s += to_string (idx) + " ";
                log_comment (temp_s, 1);

                if (clique_set.size () <= 4) {
                    small_clique_literals.push_back (clique_set);
                    small_clique_clauses.push_back (clique_clause_ids);
                }
                else {
                    emit_AMO ();
                }
            }
        }

        double find_small_AMOs () {
            auto start_time = chrono::system_clock::now();
            bool present;

            for (int i = 0; i < small_clique_literals.size() ; i++) {
                clique_set = small_clique_literals[i];
                clique_clause_ids = small_clique_clauses[i];

                present = true;
                for (auto cls_idx : clique_clause_ids) {
                    if (cnf_extractor->clauses[cls_idx].deleted) {present = false; break;}
                }

                if (present) emit_AMO ();
            }

            auto end_time = chrono::system_clock::now();
            chrono::duration<double>  total_time = end_time - start_time;

            return (total_time.count ());
        }

        void write_stats () {}


    private:

    // expanded clique set
    vector<int> clique_set;
    vector<int> clique_clause_ids;

    vector<vector<int>> small_clique_literals;
    vector<vector<int>> small_clique_clauses;

    void generate_maps () {
        int l1,l2;

        for (int cls_idx = 0; cls_idx < cnf_extractor->clauses.size(); cls_idx++) {
            // skip deleted clauses
            if (cnf_extractor->clauses[cls_idx].deleted) continue;

            // skip non-binary clauses
            if (cnf_extractor->clauses[cls_idx].get_size () != 2) continue;

            // abs(l1) < abs(l2)
            // store negation of literal since we are looking for
            //   direct AMOs and literals in constraint are negated
            if (abs (cnf_extractor->clauses[cls_idx].literals[0]) < abs (cnf_extractor->clauses[cls_idx].literals[1])) {
                l1 = - cnf_extractor->clauses[cls_idx].literals[0];
                l2 = - cnf_extractor->clauses[cls_idx].literals[1];
            } else {
                l2 = - cnf_extractor->clauses[cls_idx].literals[0];
                l1 = - cnf_extractor->clauses[cls_idx].literals[1];
            }

            // insert clause index into index map
            clause_id_map[tuple<int,int>{l1,l2}] = cls_idx;

            // insert edge into both literals edge map
            edge_map[l1].insert (l2);
            edge_map[l2].insert (l1);

        }
    }

    void expand_clique (int lit) {
        clique_set.clear();
        bool include;
        set<int> clique_set_local;
        clique_set_local.insert (lit);

        assert (edge_map.find (lit) != edge_map.end ());
        for (auto olit : edge_map[lit]) {
            include = true;
            for (auto it = clique_set_local.begin() ; it != clique_set_local.end(); it++) {
                int clit = *it;
                if (olit != clit && edge_map[olit].find (clit) == edge_map[olit].end()) {
                    include = false;
                    break;
                }
            }
            if (include) clique_set_local.insert (olit);
        }

        // using sets in case there are duplicates
        clique_set.assign( clique_set_local.begin(), clique_set_local.end() );
    }


    void remove_edge (int l1, int l2) {
        assert (abs(l1) < abs(l2));
        tuple<int,int> edge_pair;
        edge_pair = tuple<int,int>{l1,l2};
        int removed;

        removed = clause_id_map.erase (edge_pair);
        assert (removed);

        removed = edge_map[l1].erase (l2);
        assert (removed);

        removed = edge_map[l2].erase (l1);
        assert (removed);

    }

    void find_clique_clauses () {
        clique_clause_ids.clear();
        int l1,l2, cls_id;
        
        for (int i = 0; i < clique_set.size() ; i++) {
            l1 = clique_set[i];

            //logging
            string temp_s = "find ids with " + to_string(l1) + " , ";

            for (int j = i+1; j < clique_set.size() ; j++) {
                l2 = clique_set[j];

                assert (clause_id_map.find (tuple<int,int>{l1,l2}) != clause_id_map.end());

                cls_id = clause_id_map[tuple<int,int>{l1,l2}];
                clique_clause_ids.push_back (cls_id);

                //logging
                string temp_j = temp_s +  to_string (l2) + " :  " + to_string (cls_id);
                log_comment (temp_j, 3);

                remove_edge (l1,l2);
            }
        }
    }

    void emit_AMO () {
        int csize = clique_set.size() - 1;
        vector<int> klause_literals;
        for (auto lit : clique_set) klause_literals.push_back (-lit);
        Klause klause(klause_literals, csize);
        cnf_extractor->add_klause (klause, clique_clause_ids);

        stats->nconstraints++;
        if (stats->constraint_sizes.find (csize+1) == stats->constraint_sizes.end ())
            stats->constraint_sizes[csize+1] = 0;
        stats->constraint_sizes[csize+1]++;

        // logging (deleted clause ids)
        string temp_s = "deleted ids : ";
        for (auto cls_idx : clique_clause_ids) temp_s += to_string(cls_idx) + " ";
        log_comment(temp_s,4);

        // if (find (clique_set.begin (), clique_set.end() ,(189)) != clique_set.end()) {
        //     cout << csize << endl;
        //     cout << "variables :";
        //     for (auto var : clique_set) cout << var << " ";
        //     cout << endl;

        //     exit (0);
        // }
 
    }

};

}

#endif

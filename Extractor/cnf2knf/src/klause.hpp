#ifndef KLAUSE_HPP
#define KLAUSE_HPP

#include "cnf2knf.hpp"


namespace cnf2knf {

using namespace std;

class Klause {

    public:

        int         cardinality_bound;  // Cardinality_bound on clause
                                        //   Sum of the literals is at least cardinality_bound
        bool        deleted;            // Clause was deleted from the formula
        vector<int> literals;           // Literals in clause
        
        
        Klause (vector<int> literals, int cardinality_bound) {
            this->cardinality_bound = cardinality_bound;
            this->deleted = false;

            for (auto lit : literals) this->literals.push_back(lit);
        }
        
        // return size of clause
        int get_size () { return literals.size(); }

        // return true if this is a cardinality clause (not a clause)
        bool is_klause () { return cardinality_bound > 1; }
        

};

}


#endif
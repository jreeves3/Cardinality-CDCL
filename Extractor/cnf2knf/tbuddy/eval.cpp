/*========================================================================
  Copyright (c) 2022 Randal E. Bryant, Carnegie Mellon University
  
  Permission is hereby granted, free of charge, to any person
  obtaining a copy of this software and associated documentation files
  (the "Software"), to deal in the Software without restriction,
  including without limitation the rights to use, copy, modify, merge,
  publish, distribute, sublicense, and/or sell copies of the Software,
  and to permit persons to whom the Software is furnished to do so,
  subject to the following conditions:
  
  The above copyright notice and this permission notice shall be
  included in all copies or substantial portions of the Software.
  
  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
  EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
  MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
  NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS
  BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN
  ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
  CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
  SOFTWARE.
========================================================================*/



#include <ctype.h>
#include <algorithm>
#include <unordered_set>
#include <map>

#include "eval.hpp"
#include "prover.h"

using namespace trustbdd;

// GC Parameters
// Minimum number of dead nodes to trigger GC
#define COLLECT_MIN 10000
// Minimum fraction of dead:total nodes to trigger GC
#define COLLECT_FRACTION 0.10


static int next_term_id = 1;

Term::Term (tbdd t) { 
    term_id = next_term_id++;
    tfun = t;
    node_count = bdd_nodecount(t.get_root());
    is_active = true;
}

Term::~Term() {
    deactivate();
}

// Returns number of dead nodes generated
int Term::deactivate() {
    tfun = tbdd_null();  // Should delete reference to previous value
    is_active = false;
    int rval = node_count;
    node_count = 0;
    return rval;
}

TermSet::TermSet(int nv, int nd, ilist var_order, int vlevel) {
    nvar = nv;
    ndata = nd;
    verblevel = vlevel;
    tbdd_set_verbose(vlevel);
    int rcode = tbdd_init_noproof(nvar, var_order);
    if (rcode != 0) {
	std::cout << "c BDD Initialization failed.  Return code = " << rcode << std::endl;
	exit(1);
    }
    total_count = 0;
    dead_count = 0;
    and_count = 0;
    quant_count = 0;
    max_bdd = 0;
    root = bdd_false();
    next_term_id = 1;
}

TermSet::~TermSet() {
    for (Term *t : terms)
	delete t;
    tbdd_done();
}

void TermSet::check_gc() {
    if (dead_count >= COLLECT_MIN && (double) dead_count / total_count >= COLLECT_FRACTION) {
	if (verblevel >= 2) {
	    std::cout << "c Initiating GC.  Estimated total nodes = " << 
		total_count << ".  Estimated dead nodes = " << dead_count << std::endl;
	}
	bdd_gbc();
	total_count -= dead_count;
	dead_count = 0;
    }
}
  
long int TermSet::bdd_size_limit() {
    // Shouldn't require BDDs beyond quadratic size 
    return (long) ndata * ndata;
    // return (long) 99999999;
}

int TermSet::add(tbdd t) {
    Term *tp = new Term(t);
    terms.push_back(tp);
    max_bdd = max(max_bdd, tp->get_node_count());
    if (max_bdd > bdd_size_limit()) {
	cout << "c ERROR.  BDD size " << max_bdd << " exceeds limit " << bdd_size_limit() << endl;
	return -1;
    }
    return tp->get_term_id();
}

Term *TermSet::get_term(int tid) {
    if (tid < 1 || tid > terms.size()) {
	std::cout << "c ERROR.  Invalid term id " << tid << ". Currently have " << terms.size() << " terms" << std::endl;
	return NULL;
    }
    Term *tp = terms[tid-1];
    if (!tp->active()) {
	std::cout << "c ERROR. Invalid term id " << tid << ". Deactivated" << std::endl;
	return NULL;
    }
    return tp;
}

int TermSet::add_clause(ilist literals) {
    BDD R = BDD_build_clause(literals);
    bdd r = bdd(R);
    if (verblevel >= 3) {
	std::cout << "c Build BDD for clause" << endl;
    }
    tbdd t = tbdd_trust(r);
    int tid = add(t);
    if (tid > 0 && verblevel >= 3) {
	Term *tp = get_term(tid);
	std::cout << "c Read clause of length " << ilist_length(literals) <<  ". BDD size = " << tp->get_node_count() << std::endl;
    }
    return tid;
}

int TermSet::add_clause(int *ldata, int len) {
    ilist llist = ilist_copy_list(ldata, len);
    return add_clause(llist);
}

int TermSet::conjunct(int tid1, int tid2) {
    Term *tp1 = get_term(tid1);
    Term *tp2 = get_term(tid2);
    if (!tp1 || !tp2)
	return -1;
    tbdd tr1 = tp1->get_fun();
    tbdd tr2 = tp2->get_fun();
    tbdd t = tbdd_and(tr1, tr2);
    int tid = add(t);
    dead_count += tp1->deactivate();
    dead_count += tp2->deactivate();
    check_gc();
    and_count++;
    return tid;
}

int TermSet::equantify(int tid, int var) {
    Term *tp = get_term(tid);
    if (!tp)
	return -1;
    bdd r = tp->get_root();
    bdd varbdd = bdd_makeset(&var, 1);
    tbdd t = tbdd_trust(bdd_exist(r, varbdd));
    int ntid = add(t);
    dead_count += tp->deactivate();
    check_gc();
    quant_count++;
    return ntid;
}

int TermSet::find_bucket_level(int tid) {
    Term *tp = get_term(tid);
    if (tp == NULL)
	return -1;
    bdd r = tp->get_root();
    bdd support = bdd_support(r);
    int level = nvar + 1;
    while (support != bdd_true()) {
	int var = bdd_var(support);
	int vlevel = bdd_var2level(var);
	if (var > ndata && vlevel < level)
	    level = vlevel;
	support = bdd_high(support);
    }    
    if (level == nvar+1)
	level = 0;
    return level;
}


bool TermSet::bucket_reduce() {
    vector<vector<int>> buckets;
    buckets.resize(nvar+1);
    int tcount = 0;
    int bcount = 0;
    for (int i = 1; i <= terms.size(); i++) {
	Term *tp = terms[i-1];
	int tid = tp->get_term_id();
	if (!tp->active())
	    continue;
	bdd r = tp->get_root();
	if (r == bdd_false()) {
	    // Formula is trivially false
	    root = bdd_false();
	    return true;
	}
	if (r != bdd_true()) {
	    int level = find_bucket_level(tid);
	    if (level < 0) {
		return false;
	    }
	    if (buckets[level].size() == 0)
		bcount++;
	    buckets[level].push_back(tid);
	    tcount++;
	}
    }
    if (verblevel >= 3)
	std::cout << "c Placed " << tcount << " terms into " << bcount << " buckets." << std::endl;

    for (int bxlevel = 1 ; bxlevel <= nvar+1; bxlevel++) {
	// Want to leave level 0 for last
	int blevel = bxlevel % (nvar+1);
	int bvar = blevel == 0 ? 0 : bdd_level2var(blevel);
	if (buckets[blevel].size() == 0) {
	    if (blevel == 0) {
		if (verblevel >= 2) {
		    std::cout << "c Bucket " << blevel << " empty.  Result is tautology" << std::endl;
		    root = bdd_true();
		    return true;
		}
	    }
	    if (verblevel >= 3)
		std::cout << "c Bucket " << blevel << " empty.  Skipping" << std::endl;
	    continue;
	}
	int next_idx = 0;
	while (next_idx < buckets[blevel].size() - 1) {
	    int tid1 = buckets[blevel][next_idx++];
	    int tid2 = buckets[blevel][next_idx++];
	    int tid = conjunct(tid1, tid2);
	    if (tid < 0)
		return false;
	    Term *tp = get_term(tid);
	    if (tp == NULL)
		return false;
	    bdd r = tp->get_root();
	    if (r == bdd_false()) {
		if (verblevel >= 3)
		    std::cout << "c Bucket " << blevel << " Conjunction of terms " 
			      << tid1 << " and " << tid2 << " yields FALSE" << std::endl;
		root = bdd_false();
		return true;
	    }
	    int level = find_bucket_level(tid);
	    buckets[level].push_back(tid);
	    if (verblevel >= 3)
		std::cout << "c Bucket " << blevel << " Conjunction of terms " 
			  << tid1 << " and " << tid2 << " yields term " 
			  << tid << " with " << tp->get_node_count() << " nodes, and with top level " << level << std::endl;
	}
	if (next_idx == buckets[blevel].size()-1) {
	    int tid1 = buckets[blevel][next_idx];
	    if (blevel == 0) {
		Term *tp = get_term(tid1);
		root = tp->get_root();
		if (verblevel >= 1) {
		    std::cout << "c Bucket reduction yields term " << tid1 
			      << " with " << tp->get_node_count() << " nodes" << std::endl;
		}
		return true;
	    }
	    int tid = equantify(tid1, bvar);
	    if (tid < 0)
		return false;
	    Term *tp = get_term(tid);
	    bdd r = tp->get_root();
	    if (r == bdd_true()) {
		if (verblevel >= 3)
		    std::cout << "c Bucket " << blevel << " Quantification of term " 
			      << tid1 << " yields TRUE" << std::endl;
	    } else {
		int level = find_bucket_level(tid);
		buckets[level].push_back(tid);
		if (verblevel >= 3) {
		    std::cout << "c Bucket " << blevel << " Quantification of term " 
			      << tid1 << " by variable " << bvar << " yields term " << tid 
			      << " with top level " << level << std::endl;
		}

	    }
	}
    }
    // Shouldn't get here
    if (verblevel >= 1) {
	std::cout << "c ERROR.  Ran off end of buckets with no result\n";
    }
    return false;
}

void TermSet::show_statistics() {
    bddStat s;
    bdd_stats(s);
    std::cout << endl << "c " << and_count << " conjunctions, " << quant_count << " quantifications." << std::endl;
    //    bdd_printstat();
    std::cout << "c Total BDD nodes: " << s.produced <<std::endl;
    std::cout << "c Max BDD size: " << max_bdd << std::endl;
}

bool TermSet::cardinality_converter(vector<int> &lits, int *lower, int *upper) {
    // Layer of BDDs at current level in representation
    vector<bdd> layer;
    vector<bdd> hchildren;
    vector<bdd> lchildren;

    if (root == bdd_true() || root == bdd_false()) {
	// Trivially true or false
	lits.clear();
	for (int v = 1; v <= ndata; v++)
	    lits.push_back(v);
	*lower = root == bdd_true() ? 0 : ndata;
	*upper = root == bdd_true() ? ndata : 0;
	return true;
    }

    if (root == bdd_true() || root == bdd_false())
	return false;
    layer.push_back(root);
    lits.clear();
    for (int lcount = 0; lcount < ndata; lcount++) {
	int var = 0;
	hchildren.clear();
	lchildren.clear();
	for (bdd b : layer) {
	    if (b == bdd_true() || b == bdd_false()) {
		hchildren.push_back(b);
		lchildren.push_back(b);
	    } else {
		int bvar = bdd_var(b);
		if (var == 0)
		    var = bvar;
		else if (var != bvar)
		    return false;
		hchildren.push_back(bdd_high(b));
		lchildren.push_back(bdd_low(b));
	    }
	}
	int p;
	bool compatible = true;
	layer.clear();
	for (p = 0; p < 2; p++) {
	    compatible = true;
	    for (int i = 0; compatible && i < hchildren.size()-1; i++) {
		if (hchildren[(1-p)+i] != lchildren[p+i])
		    compatible = false;
	    }
	    if (compatible) {
		if (p == 0) {
		    layer.push_back(hchildren[0]);
		    for (bdd b : lchildren)
			layer.push_back(b);
		} else {
		    layer.push_back(lchildren[0]);
		    for (bdd b : hchildren)
			layer.push_back(b);
		}
		break;
	    }
	}
	if (!compatible)
	    return false;
	if (var)
	    lits.push_back(p ? var : -var);
	else if (lcount < ndata-1)
	    return false;
    }
    int l, h;
    for (l = 0; l < ndata; l++) {
	if (layer[l] == bdd_true())
	    break;
    }
    for (h = ndata; h > 0; h--) {
	if (layer[h] == bdd_true())
	    break;
    }
    if (l > h) {
	l = 1;
	h = 0;
    }
    *lower = l;
    *upper = h;
    return true;
}

Ordering::Ordering(int nv, int nd, int vlevel) {
    nvar = nv;
    ndata = nd;
    verblevel = vlevel;
    encoded_edge.resize(nv-nd);
    data_neighbor.resize(nv-nd);
    encoding_neighbor.resize(nd);
}

void Ordering::add_clause(int *ldata, int len) {
    // Number of encoding variables
    int nencode = nvar - ndata;
    if (verblevel >= 5) {
	cout << "c Ordering.  Adding clause:";
	for (int i = 0; i < len; i++)
	    cout << " " << ldata[i];
	cout << endl;
    }
    for (int i = 0; i < len; i++) {
	int v1 = abs(ldata[i]);
	for (int j=i+1; j < len; j++) {
	    int v2 = abs(ldata[j]);
	    if (v1 <= ndata) {
		if (v2 > ndata) {
		    data_neighbor[v2-ndata-1].insert(v1);
		    encoding_neighbor[v1-1].insert(v2);
		}
	    } else if (v2 <= ndata) {
		data_neighbor[v1-ndata-1].insert(v2);
		encoding_neighbor[v2-1].insert(v1);
	    } else {
		int vlow = min(v1, v2);
		int vhigh = max(v1, v2);
		int uidx = (vlow-ndata-1) * nencode + (vhigh-ndata-1);
		if (unique_edge.find(uidx) == unique_edge.end()) {
		    int eidx = edge_list.size();
		    edge_list.resize(eidx+1);
		    edge_list[eidx].node1 = vlow;
		    edge_list[eidx].node2 = vhigh;
		    edge_list[eidx].weight = 1.0;
		    unique_edge[uidx] = eidx;
		    encoded_edge[vlow-ndata-1].insert(eidx);
		    encoded_edge[vhigh-ndata-1].insert(eidx);
		    if (verblevel >= 5)
			cout << "c   Added edge #" << eidx << 
			    " (" << vlow << "," << vhigh << ") weight = " << edge_list[eidx].weight << endl;
		}
	    }
	}
    }
}

// Add weights to edges
void Ordering::add_weights() {
    int nencode = nvar - ndata;
    // Add edges between encoding variables that are affected by same data variable
    for (int dv = 1; dv <= ndata; dv++) {
	//	float wt = 1.0/(1+encoding_neighbor[dv-1].size());
	float wt = 0.75;
	for (int vlow : encoding_neighbor[dv-1])
	    for (int vhigh : encoding_neighbor[dv-1]) {
		if (vlow >= vhigh)
		    continue;
		int uidx = (vlow-ndata-1) * nencode + (vhigh-ndata-1);
		if (unique_edge.find(uidx) == unique_edge.end()) {
		    int eidx = edge_list.size();
		    edge_list.resize(eidx+1);
		    edge_list[eidx].node1 = vlow;
		    edge_list[eidx].node2 = vhigh;
		    edge_list[eidx].weight = wt;
		    unique_edge[uidx] = eidx;
		    encoded_edge[vlow-ndata-1].insert(eidx);
		    encoded_edge[vhigh-ndata-1].insert(eidx);
		    if (verblevel >= 5)
			cout << "c   Added edge #" << eidx << 
			    " (" << vlow << "," << vhigh << ") weight = " << edge_list[eidx].weight << endl;
		}
	    }
    }
    // No longer need these
    unique_edge.clear();
    encoding_neighbor.clear();
}

// Perform Dijkstra's algorithm on weighted graph.
// Add nodes to visited in order.
// For each visited node, give its path length
// Return sum of all path lengths
// If all_nodes, then include disconnected nodes
float Ordering::shortest_paths(int vsource, vector <int> &visited, vector <int> &length, bool all_nodes) {
    if (verblevel >= 4)
	cout << "c Finding shortest paths from " << vsource << endl;
    map<float,unordered_set<int>*> pqueue;
    vector<float>sofar;
    visited.clear();
    length.clear();
    int nencode = nvar-ndata;
    float infinity = nencode;
    sofar.resize(nencode, infinity);
    float dist = 0.0;
    float dsum = 0.0;
    pqueue[dist] = new unordered_set<int>({ vsource });
    sofar[vsource-ndata-1] = dist;

    while (pqueue.size() > 0) {
	auto iter = pqueue.begin();
	dist = iter->first;
	unordered_set<int> *nodes = iter->second;
	pqueue.erase(iter);
	for (int ev : *nodes) {
	    if (dist <= sofar[ev-ndata-1]) {
		visited.push_back(ev);
		length.push_back(dist);
		dsum += dist;
		if (verblevel >= 5)
		    cout << "c   Visiting " << ev << " distance = " << dist << endl;
		for (int eidx: encoded_edge[ev-ndata-1]) {
		    int ov = edge_list[eidx].node1 == ev ? edge_list[eidx].node2 : edge_list[eidx].node1;
		    float new_dist = dist + edge_list[eidx].weight;
		    if (new_dist < sofar[ov-ndata-1]) {
			sofar[ov-ndata-1] = new_dist;
			if (pqueue.find(new_dist) == pqueue.end())
			    pqueue[new_dist] = new unordered_set<int>({ ov });
			else
			    pqueue[new_dist]->insert(ov);
		    }
		}

	    }
	}
	delete nodes;
    }
    if (verblevel >= 4) {
	int ev = visited[visited.size()-1];
	dist = length[length.size()-1];
	cout << "c   Furthest neighbor " << ev << " distance = " << dist 
	     << ". Length sum = " << dsum << endl; 
    }
    if (all_nodes && visited.size() < nencode) {
	if (verblevel >= 4)
	    cout << "c   Unreached nodes:";
	for (int i = 0; i < nencode; i++)
	    if (sofar[i] == infinity) {
		int ev = ndata + 1 + i;
		visited.push_back(ev);
		length.push_back(infinity);
		if (verblevel >= 4)
		    cout << " " << ev;
	    }
	if (verblevel >= 4)
	    cout << endl;
    }
    return dsum;
}

// Look for corners of graph by series of hops from random starting vertex
// Each hop goes to furthest away vertex

// Number of starting points
#define START_COUNT 6
// Maximum number of hops for each starting point
#define MAX_HOP 3

// Minimum number of encoding nodes to start hopping
#define NODE_THRESHOLD 5


// Generate an ordering for the encoded variables
void Ordering::order_encoded(vector<int> &evar) {
    vector<int> length;
    evar.clear();
    int nencode = nvar-ndata;
    if (nencode < NODE_THRESHOLD) {
	for (int ev = ndata+1; ev <= nvar; ev++)
	    evar.push_back(ev);
	return;
    }
    add_weights();
    // What is the best starting vertex sofar
    int best_source = ndata+1;
    float best_distance = 0;
    float best_sum = 0;
    for (int t = 0; t < min(nencode, START_COUNT); t++) {
	float r = (float) random() / RAND_MAX;
	int vsource = ndata + 1 + (int) (nencode * r);
	float hdistance = 0.0;
	float hsum = 0.0;
	int hop;
	for (hop = 0; hop < MAX_HOP; hop++) {
	    float dsum = shortest_paths(vsource, evar, length, false);
	    float dist = length.back();
	    if (dist > hdistance || dist == hdistance && dsum > hsum) {
		vsource = evar.back();
		hdistance = dist;
		hsum = dsum;
	    } else
		// Not improving
		break;
	}
	if (hdistance > best_distance || hdistance == best_distance && hsum > best_sum) {
	    best_source = vsource;
	    best_distance = hdistance;
	    best_sum = hsum;
	}
	if (verblevel >= 4) {
	    cout << "c Try " << t << ": " << hop << " hops got vsource = " 
		 << vsource << " distance = " << hdistance << " sum = " << hsum << endl;
	}
    }
    // Use best starting point for variable ordering
    shortest_paths(best_source, evar, length, true);
    if (verblevel >= 4) {
	cout << "c Generated ordering:";
	for (int ev : evar)
	    cout << " " << ev;
	cout << endl;
    }
}


ilist Ordering::generate_ordering(unsigned seed) {
    srandom(seed);
    ilist result = ilist_new(nvar);
    unordered_set<int> data_added;
    vector<int> evar;
    order_encoded(evar);
    for (int ev : evar) {
	result = ilist_push(result, ev);
	for (int dv : data_neighbor[ev-ndata-1]) {
	    if (data_added.find(dv) == data_added.end()) {
		result = ilist_push(result, dv);
		data_added.insert(dv);
	    }
	}
    }
    for (int dv = 1; dv <= ndata; dv++) {
	if (data_added.find(dv) == data_added.end()) {
	    result = ilist_push(result, dv);
	}
    }
    return result;
}

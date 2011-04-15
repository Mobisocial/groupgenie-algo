#include <cstdlib>
#include <iostream>
#include <iomanip>
#include <sstream>
#include <boost/bind.hpp>
#include <boost/regex.hpp>
#include <boost/lexical_cast.hpp>
#include <boost/algorithm/string.hpp>
#include <boost/bimap.hpp>
#include <boost/bimap/set_of.hpp>
#include <boost/bimap/multiset_of.hpp>
#include <boost/dynamic_bitset.hpp>
#include <boost/program_options/variables_map.hpp>
#include <boost/program_options/options_description.hpp>
#include <boost/program_options/parsers.hpp>
#include <boost/filesystem/fstream.hpp>
#include <boost/graph/adjacency_list.hpp>
#include <boost/graph/graphviz.hpp>
#include <boost/intrusive/set.hpp>
#include <boost/date_time/posix_time/posix_time.hpp>
#include <map>
#include <set>

#include "entity.h"

namespace po = boost::program_options;
namespace fs = boost::filesystem;
namespace in = boost::intrusive;
namespace gr = boost; //weird but they didnt subspace it
namespace pt = boost::posix_time;


typedef std::vector<unsigned int> members_t;
typedef float score_t;
struct group {
    members_t members;
    score_t weight;
    unsigned int index;
    group() : weight(0), index(0) {}
};
struct relation {
    score_t uni;
    score_t inter;
    score_t low_index_diff;
    score_t high_index_diff;
    score_t low_index_overshare;
    score_t high_index_overshare;
    relation() : uni(0), inter(0), low_index_diff(0), high_index_diff(0), low_index_overshare(0), high_index_overshare(0) {}
};

typedef gr::adjacency_list<gr::setS, gr::setS, gr::undirectedS, group, relation> connectedness_graph;
    
typedef std::map<members_t, connectedness_graph::vertex_descriptor> initial_group_partition_map;

typedef in::set_member_hook<in::optimize_size<true> > hook_type;
enum move_type { none, merge, dominate, intersect, discard } m;
struct move {
    score_t e;
    move_type t;
    connectedness_graph::vertex_descriptor a;
    connectedness_graph::vertex_descriptor b;
    hook_type by_a;
    hook_type by_b;
    hook_type by_e;
};
struct order_move_a {
    bool operator () (const move& a, const move& b) const {
        return a.a < b.a;
    }
};
struct order_move_b {
    bool operator () (const move& a, const move& b) const {
        return a.b < b.b;
    }
};
struct order_move_e {
    bool operator () (const move& a, const move& b) const {
        if(a.e == b.e)
            return a.t < b.t;
        return a.e < b.e;
    }
};
typedef in::member_hook<move, hook_type, &move::by_a> hook_move_by_a;
typedef in::member_hook<move, hook_type, &move::by_b> hook_move_by_b;
typedef in::member_hook<move, hook_type, &move::by_e> hook_move_by_e;
typedef in::multiset<move, hook_move_by_a, in::compare<order_move_a> > move_by_a;
typedef in::multiset<move, hook_move_by_b, in::compare<order_move_b> > move_by_b;
typedef in::multiset<move, hook_move_by_e, in::compare<order_move_e> > move_by_e;

typedef std::set<connectedness_graph::vertex_descriptor> update_list;


boost::regex re_terms("([^:]+): ([^\r\n]+[\r\n]+(?:\\s+[^\r\n]+[\r\n]+)*)");
boost::regex re_email("(?:(?:\"([^\"]+)\"\\s+<)|(?:(?:^|,)\\s*([^<,@\"]+)\\s+<))?(\\b[A-Z0-9._%+-]+@[A-Z0-9.-]+\\.[A-Z]{2,4}\\b)", boost::regex::icase);

typedef std::vector<std::vector<score_t> > p_vec;
typedef std::vector<score_t> c_vec;


inline score_t overshare(const p_vec& conditionals, const members_t& m, unsigned int p) {
    score_t total = 0;
    unsigned int count = 0;
    for(members_t::const_iterator i = m.begin(); i != m.end(); ++i) {
        if(p == *i) 
            continue;
        total += conditionals[*i][p];
        ++count;
    }
    return total / count;
}

void update_relation(relation& r, const group& p, const group& q, const p_vec& conditionals) {
    r.uni = r.inter = r.low_index_diff = r.high_index_diff = r.low_index_overshare = r.high_index_overshare = 0;
    score_t* p_diff = p.index > q.index ? &r.high_index_diff : &r.low_index_diff;
    score_t* q_diff = q.index > p.index ? &r.high_index_diff : &r.low_index_diff;
    score_t* p_over = p.index > q.index ? &r.high_index_overshare : &r.low_index_overshare;
    score_t* q_over = q.index > p.index ? &r.high_index_overshare : &r.low_index_overshare;
    members_t::const_iterator i = p.members.begin();
    members_t::const_iterator j = q.members.begin();
    bool inter = false;
    while(i != p.members.end() && j != q.members.end()) {
        if(*i == *j) {
            inter = true;
            break;
        } else if(*i < *j) {
            ++i;
        } else {
            ++j;
        }
    }
    //quick bail out
    if(!inter)
        return;
    i = p.members.begin();
    j = q.members.begin();
    std::vector<unsigned int> combined;
    combined.reserve(p.members.size() + q.members.size());
    std::set_union(p.members.begin(), p.members.end(), q.members.begin(), q.members.end(), std::inserter(combined, combined.end()));
    while(i != p.members.end() && j != q.members.end()) {
        if(*i == *j) {
            //this person is reachable by both partitions
            r.uni += p.weight + q.weight;
            r.inter += p.weight + q.weight;
            ++i;
            ++j;
        } else if(*i < *j) {
            //this person is reached via p, but not q
            r.uni += p.weight;
            *p_diff += p.weight;
            *p_over += overshare(conditionals, combined, *i) * q.weight;
            ++i;
        } else {
            //this person is reached via q, but not p
            r.uni += q.weight;
            *q_diff += q.weight;
            *q_over += overshare(conditionals, combined, *j) * p.weight;
            ++j;
        }
    }
    //remaining i are all > the last j
    while(i != p.members.end()) {
        r.uni += p.weight;
        *p_diff += p.weight;
        *p_over += overshare(conditionals, combined, *i) * q.weight;
        ++i;
    }
    //remaining j are all > the last i
    while(j != q.members.end()) {
        r.uni += q.weight;
        *q_diff += q.weight;
        *q_over += overshare(conditionals, combined, *j) * p.weight;
        ++j;
    }
}
void update_relation(relation& r, const group& p, const group& q, score_t overshare) {
    r.uni = r.inter = r.low_index_diff = r.high_index_diff = r.low_index_overshare = r.high_index_overshare = 0;
    score_t* p_diff = p.index > q.index ? &r.high_index_diff : &r.low_index_diff;
    score_t* q_diff = q.index > p.index ? &r.high_index_diff : &r.low_index_diff;
    score_t* p_over = p.index > q.index ? &r.high_index_overshare : &r.low_index_overshare;
    score_t* q_over = q.index > p.index ? &r.high_index_overshare : &r.low_index_overshare;
    members_t::const_iterator i = p.members.begin();
    members_t::const_iterator j = q.members.begin();
    while(i != p.members.end() && j != q.members.end()) {
        if(*i == *j) {
            //this person is reachable by both partitions
            r.uni += p.weight + q.weight;
            r.inter += p.weight + q.weight;
            ++i;
            ++j;
        } else if(*i < *j) {
            //this person is reached via p, but not q
            r.uni += p.weight;
            *p_diff += p.weight;
            *p_over += overshare * q.weight;
            ++i;
        } else {
            //this person is reached via q, but not p
            r.uni += q.weight;
            *q_diff += q.weight;
            *q_over += overshare * p.weight;
            ++j;
        }
    }
    //remaining i are all > the last j
    while(i != p.members.end()) {
        r.uni += p.weight;
        *p_diff += p.weight;
        *p_over += overshare * q.weight;
        ++i;
    }
    //remaining j are all > the last i
    while(j != q.members.end()) {
        r.uni += q.weight;
        *q_diff += q.weight;
        *q_over += overshare * p.weight;
        ++j;
    }
}

class move_cache {
public:
    move_cache(const connectedness_graph& _ct, bool _no_merge, bool _no_intersect, bool _no_dominate, bool _no_discard, const p_vec& _conditionals, score_t _overshare_weight)
    : ct(_ct)
    , no_merge(_no_merge)
    , no_intersect(_no_intersect)
    , no_dominate(_no_dominate)
    , no_discard(_no_discard)
    , conditionals(_conditionals)
    , overshare_weight(_overshare_weight)
    {
        connectedness_graph::vertex_iterator v, v_e, v2;
        if(!no_discard) {
            for(boost::tie(v, v_e) = gr::vertices(ct); v != v_e; ++v) {
                add_discard_move(*v);
            }
        }
        if(!no_merge || !no_intersect || !no_dominate) {
            for(boost::tie(v, v_e) = gr::vertices(ct); v != v_e; ++v) {
                v2 = v;
                for(++v2; v2 != v_e; ++v2) {
                    add_combine_move(*v, *v2);
                }
            }
        }
    }
    void remove_moves(connectedness_graph::vertex_descriptor a, update_list& ul, bool discarding) {
        move dummy;
        dummy.a = a;
        dummy.b = a;
        std::set<move*> moves;
        std::pair<move_by_a::iterator, move_by_a::iterator> ia = by_a.equal_range(dummy);
        for(move_by_a::iterator i = ia.first; i != ia.second; ++i) {
            moves.insert(&*i);
            if(i->t != discard) {
                by_b.erase(by_b.iterator_to(*i));
            }
        }
        by_a.erase(ia.first, ia.second);
        std::pair<move_by_b::iterator, move_by_b::iterator> ib = by_b.equal_range(dummy);
        for(move_by_b::iterator i = ib.first; i != ib.second; ++i) {
            moves.insert(&*i);
            by_a.erase(by_a.iterator_to(*i));
        }
        by_b.erase(ib.first, ib.second);
        for(std::set<move*>::iterator i = moves.begin(); i != moves.end(); ++i) {
            by_e.erase(by_e.iterator_to(**i));
            if(!discarding && (*i)->t != discard) {
                ul.insert((*i)->a);
                ul.insert((*i)->b);
            }
            delete *i;
        }
    }
    void add_discard_move(connectedness_graph::vertex_descriptor v) {
        if(no_discard)
            return;
        const group& s = ct[v];
        
        score_t discard_error = s.members.size() * s.weight;
        move* m = new move();
        m->t = discard;
        m->a = v;
        m->e = discard_error;
        by_a.insert(*m);
        by_e.insert(*m);
    }
    void add_combine_move(connectedness_graph::vertex_descriptor a, connectedness_graph::vertex_descriptor b) {
        const group& s = ct[a];
        const group& t = ct[b];

        relation r;
        if(!conditionals.empty()) {
            update_relation(r, s, t, conditionals);
        } else {
            update_relation(r, s, t, overshare_weight);
        }
        if(r.inter <= 0)
            return;

        const group& l = s.index < t.index ? s : t;
        const group& h = s.index > t.index ? s : t;
        connectedness_graph::vertex_descriptor ma, mb;

        score_t min_error = std::numeric_limits<score_t>::max();
        move_type m = none;
        
        score_t merge_error = r.low_index_overshare + r.high_index_overshare;
        if(!no_merge && merge_error < min_error) {
            ma = a;
            mb = b;
            m = merge;
            min_error = merge_error;
        }

        score_t intersect_error = r.high_index_diff + r.low_index_diff;
        if(!no_intersect && intersect_error < min_error) {
            ma = a;
            mb = b;
            m = intersect;
            min_error = intersect_error;
        }

        score_t low_dominate = r.high_index_diff + r.low_index_overshare;
        if(!no_dominate && low_dominate < min_error) {
            ma = s.index < t.index ? a : b;
            mb = s.index > t.index ? a : b;
            m = dominate;
            min_error = low_dominate;
        }
        score_t high_dominate = r.low_index_diff + r.high_index_overshare;
        if(!no_dominate && high_dominate < min_error) {
            ma = s.index > t.index ? a : b;
            mb = s.index < t.index ? a : b;
            m = dominate;
            min_error = high_dominate;
        }
        
        if(m != none) {
            move* nm = new move();
            nm->a = ma;
            nm->b = mb;
            nm->e = min_error;
            nm->t = m;
            
            by_a.insert(*nm);
            by_b.insert(*nm);
            by_e.insert(*nm);
        }
    }
    const move* best_move() const {
        if(by_e.empty()) {
            return NULL;
        }
        return &*by_e.begin();
    }
    std::size_t move_count() const {
        return by_e.size();
    }
private:
    move_by_a by_a;
    move_by_b by_b;
    move_by_e by_e;
    const connectedness_graph& ct;
    bool no_merge;
    bool no_intersect;
    bool no_dominate;
    bool no_discard;
    const p_vec& conditionals;
    score_t overshare_weight;
};

int main(int argc, char* argv[])
{
    std::vector<fs::path> from;
    std::vector<fs::path> entity;
    score_t overshare_weight;
    std::string ignore_string, save_base;
    unsigned int threshold;
    unsigned int person_threshold;
    bool no_merge;
    bool no_dominate;
    bool no_intersect;
    bool no_discard;
    bool no_individuals;
    bool compress_only;
    unsigned int remove_most_common;
    std::vector<unsigned int> save_at_v;
    std::set<unsigned int> save_at;
    score_t save_fraction;
    std::vector<std::string> remove_these;
    bool save_times;
    bool save_moves, save_groups, save_scores;
    
    //[Gmail]/Sent Mail
    po::options_description general_options("General");
    general_options.add_options()
        ("help", "list options");
    po::options_description file_options("Load");
    file_options.add_options()
        ("ignore", po::value<std::string>(&ignore_string)->default_value("@lists\\.|@googlegroups\\.|@yahoogroups\\.|@mailman\\.|@facebookmail\\.|noreply|do[-_]not[-_]reply|^buzz\\+"), "ignore messages with a recipient matching this expression")
        ("entity-raw", po::value<std::vector<fs::path> >(&entity), "paths to load data ONLY for entities")
        ("load-raw", po::value<std::vector<fs::path> >(&from), "paths to load data from");
    po::options_description run_options("Run");
    run_options.add_options()
        ("compress", po::value<bool>(&compress_only)->default_value(0), "compress groups only")
        ("no-discard", po::value<bool>(&no_discard)->default_value(0), "don't consider discard moves")
        ("no-dominate", po::value<bool>(&no_dominate)->default_value(0), "don't consider dominate moves")
        ("no-intersect", po::value<bool>(&no_intersect)->default_value(0), "don't consider intersect moves")
        ("no-merge", po::value<bool>(&no_merge)->default_value(0), "don't consider merge moves")

        ("save", po::value<std::string>(&save_base), "base path to save the data at")
        ("save-fraction", po::value<score_t>(&save_fraction)->default_value(0), "save group data at these fraction steps")
        ("save-at", po::value<std::vector<unsigned int> >(&save_at_v), "save data at these values")
        ("save-moves", po::value<bool>(&save_moves)->default_value(0), "save move data")
        ("save-groups", po::value<bool>(&save_groups)->default_value(0), "save group data")
        ("save-scores", po::value<bool>(&save_scores)->default_value(0), "save scores")
        ("save-times", po::value<bool>(&save_times)->default_value(0), "save times")

        ("conditionals", "overshare penalty based on conditionals")
        ("penalty", po::value<score_t>(&overshare_weight)->default_value(.5), "overshare penalty, ignored for conditionals")
        ("remove-most-common", po::value<unsigned int>(&remove_most_common)->default_value(1), "remove the most common individual (owner)")
        ("remove", po::value<std::vector<std::string> >(&remove_these), "remove these mail addresses")
        ("no-individuals", po::value<bool>(&no_individuals)->default_value(0), "ignore individuals")
        ("threshold", po::value<unsigned int>(&threshold)->default_value(1), "minimum mails for group")
        ("person-threshold", po::value<unsigned int>(&person_threshold)->default_value(2), "minimum mails for person");
    
    po::options_description all_options("Email Topology Options");
    all_options
        .add(general_options)
        .add(file_options)
        .add(run_options);

    if(argc < 2) {
        std::cout << all_options << std::endl;
        return 1;
    }

    po::variables_map vm;
    try {
        int options_style = po::command_line_style::default_style;
        po::store(po::parse_command_line(argc, argv, all_options, options_style), vm);
        po::notify(vm);
    } catch(std::exception& e) {
        std::cout << all_options << std::endl;
        std::cout << "Command line parsing failed: " << e.what() << std::endl;
        return 1;
    }
    
    if(vm.count("help")) {
        std::cout << all_options << std::endl;
        return 1;
    }
    std::copy(save_at_v.begin(), save_at_v.end(), std::inserter(save_at, save_at.end()));

    email_id_bimap email_id;
    connectedness_graph cg;
    initial_group_partition_map igpm;
    entity_map em;

    if(!vm.count("load-raw")) {
        std::cout << "must load some data" << std::endl;
        return 1;
    }
    
    std::size_t initial_mails = 0;
    pt::ptime load_start = pt::microsec_clock::universal_time();
    std::size_t max_id = 0;
    std::vector<char> buffer(128 * 1024);
    std::set<std::string> removed;
    try {
        boost::regex re_ignore(ignore_string);
        boost::regex re_loader("([^\t]+)");
        std::cout << "resolving entities" << std::endl;
        for(std::vector<fs::path>::iterator i = entity.begin(); i != entity.end(); ++i) {
            if(!fs::exists(*i))
                throw std::runtime_error(std::string("input file not found: ") + i->file_string());
            std::cout << "loading " << i->file_string();
            fs::ifstream in(*i);
            //we don't care about messages here
            while(in.good()) {
                in.getline(&buffer[0], buffer.size());
                std::string line = &buffer[0];
                boost::algorithm::trim(line);
                if(line == "-") {
                    break;
                }
                bool first = true;
                for(boost::sregex_iterator j(line.begin(), line.end(), re_loader), e; j != e; ++j) {
                    if(first) {
                        first = false;
                    } else {
                        std::string email_address = (*j)[0].str();
                        if(regex_search(email_address, re_ignore)) {
                            removed.insert(email_address);
                            continue;
                        }
                        std::pair<email_id_bimap::map_by<email>::iterator, bool> result = email_id.by<email>().insert(
                            email_id_bimap::map_by<email>::value_type(email_address, email_id.size()));
                        if(result.second)
                            std::cout << "@" << std::flush;
                    }
                }
            }
            while(in.good()) {
                in.getline(&buffer[0], buffer.size());
                std::string line = &buffer[0];
                boost::algorithm::trim(line);
                
                std::string email_address;
                bool first = true;
                for(boost::sregex_iterator j(line.begin(), line.end(), re_loader), e; j != e; ++j) {
                    if(first) {
                        first = false;
                        email_address = (*j)[0].str();
                        if(regex_search(email_address, re_ignore)) {
                            break;
                        }
                    } else {
                        std::string name = (*j)[0].str();
                        try {
                            em[email_address].insert(name);
                        } catch(std::exception& e) {
                            std::cout <<  "err missing: " << email_address << std::endl;
                            throw;
                        }
                    }
                }
            }
            std::cout << std::endl;
        }
        resolve_entities(em, email_id);
        for(std::vector<fs::path>::iterator i = from.begin(); i != from.end(); ++i) {
            if(!fs::exists(*i))
                throw std::runtime_error(std::string("input file not found: ") + i->file_string());
            std::cout << "loading " << i->file_string();
            fs::ifstream in(*i);
            while(in.good()) {
                in.getline(&buffer[0], buffer.size());
                std::string line = &buffer[0];
                boost::algorithm::trim(line);
                if(line == "-") {
                    break;
                }
                members_t g;
                unsigned int count = 0;
                bool first = true;
                for(boost::sregex_iterator j(line.begin(), line.end(), re_loader), e; j != e; ++j) {
                    if(first) {
                        first = false;
                        std::string number = (*j)[0].str();
                        count = boost::lexical_cast<unsigned int>(number);
                    } else {
                        std::string email_address = (*j)[0].str();
                        if(regex_search(email_address, re_ignore)) {
                            removed.insert(email_address);
                            continue;
                        }
                        std::pair<email_id_bimap::map_by<email>::iterator, bool> result = email_id.by<email>().insert(
                            email_id_bimap::map_by<email>::value_type(email_address, email_id.size()));
                        if(result.second)
                            std::cout << "@" << std::flush;
                        if(std::find(g.begin(), g.end(), result.first->second) == g.end()) {
                            g.push_back(result.first->second);
                        }
                    }
                }

                if(g.empty()) {
                    //no emails? wtfs
                    continue;
                }
                std::sort(g.begin(), g.end());
                initial_group_partition_map::iterator r = igpm.find(g);
                if(r == igpm.end()) {
                    connectedness_graph::vertex_descriptor node = gr::add_vertex(cg);
                    cg[node].members = g;
                    cg[node].weight = count;
                    igpm.insert(r, std::make_pair(g, node));
                } else {
                    connectedness_graph::vertex_descriptor node = r->second;
                    cg[node].weight += count;
                }
                initial_mails += count;
                std::cout << "." << std::flush;
            }
            //no need to load em
            std::cout << std::endl;
        }
        max_id = email_id.size();
    } catch(std::exception& e) {
        std::cout << "failed to load data: " << e.what() << std::endl;
        return 1;
    }
    
    std::cout << "removed: ";
    std::copy(removed.begin(), removed.end(), std::ostream_iterator<std::string>(std::cout, " "));
    std::cout << std::endl;

    pt::ptime load_end = pt::microsec_clock::universal_time();

    pt::ptime process_start = pt::microsec_clock::universal_time();
    std::map<unsigned int, score_t> ppl;
    for(connectedness_graph::vertex_iterator i = gr::vertices(cg).first; i != gr::vertices(cg).second;) {
        if(cg[*i].weight >= threshold) {
            for(members_t::iterator j = cg[*i].members.begin(); j != cg[*i].members.end(); ++j) {
                ppl[*j] += cg[*i].weight;
            }
            ++i;
        } else {
            connectedness_graph::vertex_iterator to_erase = i++;
            gr::clear_vertex(*to_erase, cg);
            gr::remove_vertex(*to_erase, cg);
        }
    }
    //remove the owner, todo, this is evil because now there are dupe groups if A was owner and A B C and B C existed
    if(!ppl.empty()) {
        unsigned int max_person = ppl.begin()->first;
        score_t max_val = ppl.begin()->second;
        for(std::map<unsigned int, score_t>::iterator j = ppl.begin(); j != ppl.end(); ++j) {
            if(j->second > max_val) {
                max_val = j->second;
                max_person = j->first;
            }
        }
        std::cout << "most metioned " << email_id.by<bit>().equal_range(max_person).first->second << " : " << max_val << std::endl;
        while(remove_most_common) {
            std::cout << "removing metioned " << email_id.by<bit>().equal_range(max_person).first->second << " : " << max_val << std::endl;
            for(connectedness_graph::vertex_iterator i = gr::vertices(cg).first; i != gr::vertices(cg).second;) {
                members_t::iterator k = std::find(cg[*i].members.begin(), cg[*i].members.end(), max_person);
                if(k != cg[*i].members.end()) {
                    cg[*i].members.erase(k);
                }
                if(cg[*i].members.empty()) {
                    connectedness_graph::vertex_iterator to_delete = i;
                    ++i;
                    gr::clear_vertex(*to_delete, cg);
                    gr::remove_vertex(*to_delete, cg);
                } else {
                    ++i;
                }
            }
            ppl.erase(max_person);
            max_person = ppl.begin()->first;
            max_val = ppl.begin()->second;
            for(std::map<unsigned int, score_t>::iterator j = ppl.begin(); j != ppl.end(); ++j) {
                if(j->second > max_val) {
                    max_val = j->second;
                    max_person = j->first;
                }
            }
            std::cout << "next most metioned " << email_id.by<bit>().equal_range(max_person).first->second << " : " << max_val << std::endl;
            --remove_most_common;
        }
        std::set<unsigned int> ids_to_remove;
        for(std::vector<std::string>::iterator i = remove_these.begin(); i != remove_these.end(); ++i) {
            email_id_bimap::map_by<email>::iterator result = email_id.by<email>().find(*i);
            if(result != email_id.by<email>().end()) {
                ids_to_remove.insert(result->second);
            }
        }
        for(std::map<unsigned int, score_t>::iterator j = ppl.begin(); j != ppl.end();) {
            if(j->second >= person_threshold && !ids_to_remove.count(j->first)) {
                std::map<unsigned int, score_t>::iterator to_delete = j++;
                ppl.erase(to_delete);
            } else {
                ++j;
            }
        }
        for(connectedness_graph::vertex_iterator i = gr::vertices(cg).first; i != gr::vertices(cg).second;) {
            members_t& m = cg[*i].members;
            for(std::size_t o = 0; o < m.size();) {
                if(ppl.find(m[o]) != ppl.end()) {
                    m.erase(m.begin() + o);
                } else {
                    ++o;
                }
            }
            if(m.empty()) {
                connectedness_graph::vertex_iterator to_delete = i;
                ++i;
                gr::clear_vertex(*to_delete, cg);
                gr::remove_vertex(*to_delete, cg);
            } else {
                ++i;
            }
        }
    }
    if(no_individuals) {
        for(connectedness_graph::vertex_iterator i = gr::vertices(cg).first; i != gr::vertices(cg).second;) {
            if(cg[*i].members.size() > 1) {
                ++i;
            } else {
                connectedness_graph::vertex_iterator to_erase = i++;
                gr::clear_vertex(*to_erase, cg);
                gr::remove_vertex(*to_erase, cg);
            }
        }
    }
    if(compress_only) {
        std::ostringstream fn;
        fn << save_base << "-compressed.txt";
        fs::path path(fn.str());
        if(fs::exists(path))
            fs::remove(path);
        fs::ofstream out(path);
        
        connectedness_graph::vertex_iterator v, v_e;
        for(boost::tie(v, v_e) = gr::vertices(cg); v != v_e; ++v) {
            group& g = cg[*v];
            std::set<std::string> names;
            for(members_t::const_iterator i = g.members.begin(); i != g.members.end(); ++i) {
                names.insert(email_id.by<bit>().equal_range(*i).first->second);
            }
            out << g.weight << " ";
            std::copy(names.begin(), names.end(), std::ostream_iterator<std::string>(out, " "));
            out << std::endl;
        }
        out << "-";
        return 0;
    }
    //normalize group weights for large groups
    for(connectedness_graph::vertex_iterator i = gr::vertices(cg).first; i != gr::vertices(cg).second; ++i) {
        if(cg[*i].members.size() < 20) 
            continue;
        cg[*i].weight *= score_t(20) / cg[*i].members.size();
    }
    unsigned int vertex_number = 0;
    for(connectedness_graph::vertex_iterator i = gr::vertices(cg).first; i != gr::vertices(cg).second; ++i) {
        cg[*i].index = vertex_number++;
    }
    pt::ptime process_end = pt::microsec_clock::universal_time();
    
    pt::ptime conditionals_start = pt::microsec_clock::universal_time();
    c_vec counts;
    p_vec conditionals;
    if(vm.count("conditionals")) {
        counts.resize(max_id);
        conditionals.resize(max_id);
        std::cout << "computing conditionals" << std::endl;
        for(p_vec::iterator i = conditionals.begin(); i != conditionals.end(); ++i) {
            i->resize(max_id);
        }
        for(connectedness_graph::vertex_iterator v = gr::vertices(cg).first; v != gr::vertices(cg).second; ++v) {
            group& g = cg[*v];
            for(members_t::const_iterator i = g.members.begin(); i != g.members.end(); ++i) {
                if(*i >= counts.size()) {
                    std::cout << "bad index? " << *i << " vs " << counts.size() << std::endl;
                }
                counts[*i] += g.weight;
                for(members_t::const_iterator j = g.members.begin(); j != g.members.end(); ++j) {
                    conditionals[*i][*j] += g.weight;
                }
            }
        }
        for(unsigned int i = 0; i < max_id; ++i) {
            for(unsigned int j = 0; j < max_id; ++j) {
                conditionals[i][j] = 1.0 - conditionals[i][j] / counts[i]; // P(!J | I)
            }
        }
    }
    pt::ptime conditionals_end = pt::microsec_clock::universal_time();
    
    connectedness_graph& ct(cg);
    boost::scoped_ptr<fs::ofstream> moves;
    if(!save_base.empty() && save_moves) {
        std::ostringstream fn;
        fn << save_base << "-moves.txt";
        fs::path path(fn.str());
        if(fs::exists(path))
            fs::remove(path);
        moves.reset(new fs::ofstream(path));
    }
    boost::scoped_ptr<fs::ofstream> scores;
    if(!save_base.empty() && save_scores) {
        std::ostringstream fn;
        fn << save_base << "-scores.txt";
        fs::path path(fn.str());
        if(fs::exists(path))
            fs::remove(path);
        scores.reset(new fs::ofstream(path));
    }
    
    pt::ptime move_cache_start = pt::microsec_clock::universal_time();
    std::cout << "initializing move cache" << std::endl;
    move_cache mc(ct, no_merge, no_intersect, no_dominate, no_discard, conditionals, overshare_weight);
    std::size_t initial_moves = mc.move_count();
    std::size_t initial_groups = gr::num_vertices(ct);
    pt::ptime move_cache_end = pt::microsec_clock::universal_time();
    pt::ptime algo_start = pt::microsec_clock::universal_time();
    std::cout << "running from " << gr::num_vertices(ct) << " groups" << std::endl;
    score_t total_dropped_discard = 0;
    score_t total_dropped_intersect = 0;
    score_t total_dropped_dominate = 0;
    score_t total_overshare_dominate = 0;
    score_t total_overshare_merge = 0;
    
    score_t initial_score = 0;
    connectedness_graph::vertex_iterator v, v_e;
    for(boost::tie(v, v_e) = gr::vertices(ct); v != v_e; ++v) {
        group& g = ct[*v];
        initial_score += g.members.size() * g.weight;
    }
    
    std::vector<bool> saved_fractions(ceil(1.0 / save_fraction));
    
    for(int iteration = 0; gr::num_vertices(ct) > 0; ++iteration) {
        score_t current_score = 0;
        connectedness_graph::vertex_iterator v, v_e;
        for(boost::tie(v, v_e) = gr::vertices(ct); v != v_e; ++v) {
            group& g = ct[*v];
            current_score += g.weight * g.members.size();
        }
        if(scores) {
            (*scores) << gr::num_vertices(ct) << " " << current_score << " " 
                << total_dropped_discard << " "
                << total_dropped_intersect << " "
                << total_dropped_dominate << " "
                << total_overshare_dominate << " "
                << total_overshare_merge << " ";
        }

        std::vector<std::string> save_names;
        if(!save_base.empty() && save_groups && save_at.count(gr::num_vertices(ct))) {
            std::ostringstream fn;
            fn << save_base << "-" << std::setfill('0') << std::setw(6) << gr::num_vertices(ct) << ".txt";
            save_names.push_back(fn.str());
        }
        //if we're out of moves, then all the remaing fractions are satisfied by this grouping
        if(!save_base.empty() && save_fraction != 0.0 && gr::num_vertices(ct) == 1) {
            int k = 0;
            for(score_t fr = save_fraction; fr <= 1.0; fr += save_fraction, ++k) {
                //once a frac is done, there is nothing higher left
                if(saved_fractions[k])
                    break;
                std::ostringstream fn;
                fn << save_base << "-" << fr << ".txt";
                save_names.push_back(fn.str());
            }
        }
        for(std::vector<std::string>::iterator k = save_names.begin(); k != save_names.end(); ++k) {
            fs::path path(*k);
            if(fs::exists(path))
                fs::remove(path);
            fs::ofstream out(path);
            connectedness_graph::vertex_iterator v, v_e;
            for(boost::tie(v, v_e) = gr::vertices(ct); v != v_e; ++v) {
                group& g = ct[*v];
                std::set<std::string> names;
                for(members_t::const_iterator i = g.members.begin(); i != g.members.end(); ++i) {
                    names.insert(email_id.by<bit>().equal_range(*i).first->second);
                }
                out << (g.members.size() * g.weight) << " ";
                std::copy(names.begin(), names.end(), std::ostream_iterator<std::string>(out, " "));
                out << std::endl;
            }
        }
        save_names.clear();
        if(gr::num_vertices(ct) == 1) {
            std::cout << std::endl;
            break;
        }
        const move* bm = mc.best_move();
        if(!bm) {
            std::cout << std::endl;
            std::cout << "no move possible aborting" << std::endl;
            return 1;
        }

        score_t min_error = bm->e;
        move_type m = bm->t;
        connectedness_graph::vertex_descriptor a = bm->a;
        connectedness_graph::vertex_descriptor b = bm->b;
        relation r;
        if(m != discard) {
            if(!conditionals.empty()) {
                update_relation(r, ct[a], ct[b], conditionals);
            } else {
                update_relation(r, ct[a], ct[b], overshare_weight);
            }
        }
        
        //before modifying the groups, check if we have achieved a new value fraction bucket.
        if(!save_base.empty() && save_fraction != 0.0) {
            int k = 0;
            for(score_t fr = save_fraction; fr <= 1.0; fr += save_fraction, ++k) {
                //once a frac is done, there is nothing higher left
                if(saved_fractions[k])
                    break;
                if((current_score - min_error) / initial_score < fr) {
                    std::ostringstream fn;
                    fn << save_base << "-" << fr << ".txt";
                    saved_fractions[k] = true;
                    save_names.push_back(fn.str());
                }
            }
        }
        for(std::vector<std::string>::iterator k = save_names.begin(); k != save_names.end(); ++k) {
            fs::path path(*k);
            if(fs::exists(path))
                fs::remove(path);
            fs::ofstream out(path);
            connectedness_graph::vertex_iterator v, v_e;
            for(boost::tie(v, v_e) = gr::vertices(ct); v != v_e; ++v) {
                group& g = ct[*v];
                std::set<std::string> names;
                for(members_t::const_iterator i = g.members.begin(); i != g.members.end(); ++i) {
                    names.insert(email_id.by<bit>().equal_range(*i).first->second);
                }
                out << (g.members.size() * g.weight) << " ";
                std::copy(names.begin(), names.end(), std::ostream_iterator<std::string>(out, " "));
                out << std::endl;
            }
        }
        
        
        update_list ul;
        // std::cout << "err " << min_error << " ";
        //apply the move
        switch(m) {
        case merge: {
            std::cout << "M" << std::flush;
            if(scores) {
                *scores << "M ";
                
                group& s = ct[a];
                group& t = ct[b];
                group& l = s.index < t.index ? s : t;
                group& h = s.index > t.index ? s : t;

                score_t h_unique = r.high_index_diff / h.weight;
                score_t l_unique = r.low_index_diff / l.weight;

                score_t eff_overshare = (r.high_index_overshare + r.low_index_overshare);
                score_t eff_weight = (h_unique * l.weight + l_unique * h.weight);

                *scores << eff_overshare << " " << eff_weight << std::endl;
            }
            total_overshare_merge += r.high_index_overshare + r.low_index_overshare;
            if(moves) {
                group& s = ct[a];
                group& t = ct[b];
                group& l = s.index < t.index ? s : t;
                group& h = s.index > t.index ? s : t;

                score_t h_unique = r.high_index_diff / h.weight;
                score_t l_unique = r.low_index_diff / l.weight;

                score_t eff_penalty = (r.high_index_overshare + r.low_index_overshare) / (h_unique * l.weight + l_unique * h.weight);
                (*moves) << "merge E=" << min_error << " G=" << gr::num_vertices(ct) 
                    << " eff penalty=" << eff_penalty << std::endl;
                {
                    group& g = ct[a];
                    std::set<std::string> names;
                    for(members_t::const_iterator i = g.members.begin(); i != g.members.end(); ++i) {
                        names.insert(email_id.by<bit>().equal_range(*i).first->second);
                    }
                    (*moves) << "\t" << g.members.size() * g.weight << " ";
                    std::copy(names.begin(), names.end(), std::ostream_iterator<std::string>(*moves, " "));
                    (*moves) << std::endl;
                }
                {
                    group& g = ct[b];
                    std::set<std::string> names;
                    for(members_t::const_iterator i = g.members.begin(); i != g.members.end(); ++i) {
                        names.insert(email_id.by<bit>().equal_range(*i).first->second);
                    }
                    (*moves) << "\t" << g.members.size() * g.weight << " ";
                    std::copy(names.begin(), names.end(), std::ostream_iterator<std::string>(*moves, " "));
                    (*moves) << std::endl;
                }
                
            }
            members_t n;
            std::set_union(ct[a].members.begin(), ct[a].members.end(), ct[b].members.begin(), ct[b].members.end(), std::inserter(n, n.end()));
            std::swap(ct[a].members, n);
            ct[a].weight = (r.uni - min_error) / ct[a].members.size();
            mc.remove_moves(a, ul, false);
            mc.remove_moves(b, ul, false);
            gr::remove_vertex(b, ct);
            break;
        }
        case intersect: {
            std::cout << "I" << std::flush;
            if(scores) {
                *scores << "I" << std::endl;
            }
            if(moves) {
                (*moves) << "intersect E=" << min_error << " G=" << gr::num_vertices(ct) << std::endl;
                {
                    group& g = ct[a];
                    std::set<std::string> names;
                    for(members_t::const_iterator i = g.members.begin(); i != g.members.end(); ++i) {
                        names.insert(email_id.by<bit>().equal_range(*i).first->second);
                    }
                    (*moves) << "\t" << g.members.size() * g.weight << " ";
                    std::copy(names.begin(), names.end(), std::ostream_iterator<std::string>(*moves, " "));
                    (*moves) << std::endl;
                }
                {
                    group& g = ct[b];
                    std::set<std::string> names;
                    for(members_t::const_iterator i = g.members.begin(); i != g.members.end(); ++i) {
                        names.insert(email_id.by<bit>().equal_range(*i).first->second);
                    }
                    (*moves) << "\t" << g.members.size() * g.weight << " ";
                    std::copy(names.begin(), names.end(), std::ostream_iterator<std::string>(*moves, " "));
                    (*moves) << std::endl;
                }
                
            }
            total_dropped_intersect += min_error;
            members_t n;
            std::set_intersection(ct[a].members.begin(), ct[a].members.end(), ct[b].members.begin(), ct[b].members.end(), std::inserter(n, n.end()));
            std::swap(ct[a].members, n);
            ct[a].weight = (r.uni - min_error) / ct[a].members.size();
            connectedness_graph::adjacency_iterator v, v_e;
            mc.remove_moves(a, ul, false);
            mc.remove_moves(b, ul, false);
            gr::remove_vertex(b, ct);
            break;
        }
        case discard: {
            std::cout << "-" << std::flush;
            if(scores) {
                *scores << "-" << std::endl;
            }
            total_dropped_discard += min_error;
            if(moves) {
                (*moves) << "discard E=" << min_error << " G=" << gr::num_vertices(ct) << std::endl;
                group& g = ct[a];
                std::set<std::string> names;
                for(members_t::const_iterator i = g.members.begin(); i != g.members.end(); ++i) {
                    names.insert(email_id.by<bit>().equal_range(*i).first->second);
                }
                (*moves) << "\t" << g.members.size() * g.weight << " ";
                std::copy(names.begin(), names.end(), std::ostream_iterator<std::string>(*moves, " "));
                (*moves) << std::endl;
            }
            mc.remove_moves(a, ul, true);
            gr::remove_vertex(a, ct);
            break;
        }
        case dominate: {
            std::cout << "D" << std::flush;
            if(scores) {
                *scores << "D ";
                group& s = ct[a];
                group& t = ct[b];
                group& l = s.index < t.index ? s : t;
                group& h = s.index > t.index ? s : t;

                score_t h_unique = r.high_index_diff / h.weight;
                score_t l_unique = r.low_index_diff / l.weight;

                score_t eff_overshare = (r.high_index_diff + r.low_index_overshare) < (r.low_index_diff + r.high_index_overshare) ? 
                    r.low_index_overshare:
                    r.high_index_overshare;
                score_t eff_weight = (r.high_index_diff + r.low_index_overshare) < (r.low_index_diff + r.high_index_overshare) ? 
                    (l_unique * h.weight):
                    (h_unique * h.weight);
                    
                *scores << eff_overshare << " " << eff_weight << std::endl;

            }
            {
                group& s = ct[a];
                group& t = ct[b];
                group& l = s.index < t.index ? s : t;
                group& h = s.index > t.index ? s : t;

                score_t h_unique = r.high_index_diff / h.weight;
                score_t l_unique = r.low_index_diff / l.weight;

                score_t eff_overshare = (r.high_index_diff + r.low_index_overshare) < (r.low_index_diff + r.high_index_overshare) ? 
                    r.low_index_overshare:
                    r.high_index_overshare;
                score_t eff_drop = (r.high_index_diff + r.low_index_overshare) < (r.low_index_diff + r.high_index_overshare) ? 
                    r.high_index_diff:
                    r.low_index_diff;
                    
                total_overshare_dominate += eff_overshare;
                total_dropped_dominate += eff_drop;
            }
            if(moves) {
                group& s = ct[a];
                group& t = ct[b];
                group& l = s.index < t.index ? s : t;
                group& h = s.index > t.index ? s : t;

                score_t h_unique = r.high_index_diff / h.weight;
                score_t l_unique = r.low_index_diff / l.weight;

                score_t eff_penalty = (r.high_index_diff + r.low_index_overshare) < (r.low_index_diff + r.high_index_overshare) ? 
                    r.low_index_overshare / (l_unique * h.weight):
                    r.high_index_overshare / (h_unique * h.weight);
                (*moves) << "dominate E=" << min_error << " G=" << gr::num_vertices(ct) << " eff penalty=" << eff_penalty << std::endl;
                {
                    group& g = ct[a];
                    std::set<std::string> names;
                    for(members_t::const_iterator i = g.members.begin(); i != g.members.end(); ++i) {
                        names.insert(email_id.by<bit>().equal_range(*i).first->second);
                    }
                    (*moves) << "\t" << g.members.size() * g.weight << " ";
                    std::copy(names.begin(), names.end(), std::ostream_iterator<std::string>(*moves, " "));
                    (*moves) << std::endl;
                }
                {
                    group& g = ct[b];
                    std::set<std::string> names;
                    for(members_t::const_iterator i = g.members.begin(); i != g.members.end(); ++i) {
                        names.insert(email_id.by<bit>().equal_range(*i).first->second);
                    }
                    (*moves) << "\t" << g.members.size() * g.weight << " ";
                    std::copy(names.begin(), names.end(), std::ostream_iterator<std::string>(*moves, " "));
                    (*moves) << std::endl;
                }
                
            }
            ct[a].weight = (r.uni - min_error) / ct[a].members.size();
            mc.remove_moves(a, ul, false);
            mc.remove_moves(b, ul, false);
            gr::remove_vertex(b, ct);
            break;
        }
        }

        //update weights
        if(m != discard) {
            mc.add_discard_move(a);
            for(update_list::iterator i = ul.begin(); i != ul.end(); ++i) {
                if(a != *i && b != *i)
                    mc.add_combine_move(a, *i);
            }
            if(moves) {
                group& g = ct[a];
                std::set<std::string> names;
                for(members_t::const_iterator i = g.members.begin(); i != g.members.end(); ++i) {
                    names.insert(email_id.by<bit>().equal_range(*i).first->second);
                }
                (*moves) << "\t=" << g.members.size() * g.weight << " ";
                std::copy(names.begin(), names.end(), std::ostream_iterator<std::string>(*moves, " "));
                (*moves) << std::endl;
            }
        }
    }
    pt::ptime algo_end = pt::microsec_clock::universal_time();
    struct rusage usage;
    getrusage(RUSAGE_SELF, &usage);
    if(!save_base.empty() && save_times) {
        std::ostringstream fn;
        fn << save_base << "-times.txt";
        fs::path path(fn.str());
        if(fs::exists(path))
            fs::remove(path);
        fs::ofstream out(path);
        out << "\t" << initial_mails
            << "\t" << initial_groups
            << "\t" << initial_moves
            << "\t" << (load_end - load_start).total_microseconds()
            << "\t" << (process_end - process_start).total_microseconds() 
            << "\t" << (conditionals_end - conditionals_start).total_microseconds() 
            << "\t" << (move_cache_end - move_cache_start).total_microseconds() 
            << "\t" << (algo_end - algo_start).total_microseconds()
            << "\t" << (unsigned long)usage.ru_maxrss
            << "\t" << usage.ru_ixrss
            << "\t" << usage.ru_idrss
            << "\t" << usage.ru_isrss
            << std::endl;
            
    }
    return 0;
}

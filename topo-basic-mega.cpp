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
#include <boost/program_options/variables_map.hpp>
#include <boost/program_options/options_description.hpp>
#include <boost/program_options/parsers.hpp>
#include <boost/filesystem/fstream.hpp>
#include <map>
#include <set>

#include "entity.h"

namespace po = boost::program_options;
namespace fs = boost::filesystem;


typedef std::vector<unsigned int> members_t;
typedef float score_t;
struct group {
    bool dead;
    members_t members;
    score_t weight;
    group() : weight(0), dead(false) {}
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
typedef std::vector<group> group_list;
    
typedef std::map<members_t, unsigned int> initial_group_partition_map;


enum move_type { none, discard, merge, dominate, intersect } m;
struct move {
    score_t e;
    move_type t;
    unsigned int a;
    unsigned int b;
};
typedef std::vector<move> move_list;

typedef std::vector<std::vector<score_t> > p_vec;
typedef std::vector<score_t> c_vec;


boost::regex re_terms("([^:]+): ([^\r\n]+[\r\n]+(?:\\s+[^\r\n]+[\r\n]+)*)");
boost::regex re_email("(?:(?:\"([^\"]+)\"\\s+<)|(?:(?:^|,)\\s*([^<,@\"]+)\\s+<))?(\\b[A-Z0-9._%+-]+@[A-Z0-9.-]+\\.[A-Z]{2,4}\\b)", boost::regex::icase);


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

void update_relation(relation& r, const group_list& g, unsigned int p_i, unsigned int q_i, const p_vec& conditionals) {
    const group& p = g[p_i];
    const group& q = g[q_i];
    r.uni = r.inter = r.low_index_diff = r.high_index_diff = r.low_index_overshare = r.high_index_overshare = 0;
    score_t* p_diff = p_i > q_i ? &r.high_index_diff : &r.low_index_diff;
    score_t* q_diff = q_i > p_i ? &r.high_index_diff : &r.low_index_diff;
    score_t* p_over = p_i > q_i ? &r.high_index_overshare : &r.low_index_overshare;
    score_t* q_over = q_i > p_i ? &r.high_index_overshare : &r.low_index_overshare;
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
void update_relation(relation& r, const group_list& g, unsigned int p_i, unsigned int q_i,  score_t overshare) {
    const group& p = g[p_i];
    const group& q = g[q_i];
    r.uni = r.inter = r.low_index_diff = r.high_index_diff = r.low_index_overshare = r.high_index_overshare = 0;
    score_t* p_diff = p_i > q_i ? &r.high_index_diff : &r.low_index_diff;
    score_t* q_diff = q_i > p_i ? &r.high_index_diff : &r.low_index_diff;
    score_t* p_over = p_i > q_i ? &r.high_index_overshare : &r.low_index_overshare;
    score_t* q_over = q_i > p_i ? &r.high_index_overshare : &r.low_index_overshare;
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
    //bail if there is no intersection
    if(r.inter <= 0)
        return;
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
typedef std::set<unsigned int> update_list;

class move_cache {
public:
    move_cache(const group_list& _ct, bool _no_merge, bool _no_intersect, bool _no_dominate, bool _no_discard, const p_vec& _conditionals, score_t _overshare_weight)
    : ct(_ct)
    , no_merge(_no_merge)
    , no_intersect(_no_intersect)
    , no_dominate(_no_dominate)
    , no_discard(_no_discard)
    , conditionals(_conditionals)
    , overshare_weight(_overshare_weight)
    {
        //need lots of virtual memory :-)
        moves.reserve(ct.size() * ct.size());
        for(unsigned int i = 0; i < ct.size(); ++i) {
            add_discard_move(i);
        }
        for(unsigned int i = 0; i < ct.size(); ++i) {
            for(unsigned int j = i + 1; j < ct.size(); ++j) {
                add_combine_move(i, j);
            }
        }        
    }
    //b is removed, a will be updated, this is reflected in the update list
    void remove_moves(unsigned int a, unsigned int b, update_list& ul) {
        for(unsigned int i = 0; i < moves.size();) {
            move& m = moves[i];
            if(m.a == a || m.a == b || 
                m.t != discard && (m.b == a || m.b == b)) 
            {
                if(m.t != discard) {
                    ul.insert(m.a);
                    ul.insert(m.b);
                }
                std::swap(m, moves.back());
                moves.pop_back();
            } else {
                ++i;
            }
        }
    }
    //a is removed, no update list
    void remove_moves(unsigned int a) {
        for(unsigned int i = 0; i < moves.size();) {
            move& m = moves[i];
            if(m.a == a ||
                (m.t == intersect || m.t == merge) && 
                (m.b == a))
            {
                std::swap(m, moves.back());
                moves.pop_back();
            } else {
                ++i;
            }
        }
    }
    void add_discard_move(unsigned int v) {
        if(no_discard)
            return;
        const group& s = ct[v];
        
        score_t discard_error = s.members.size() * s.weight;
        move m;
        m.t = discard;
        m.a = v;
        m.e = discard_error;
        moves.push_back(m);
    }
    void add_combine_move(unsigned int a, unsigned int b) {
        relation r;
        const group& s = ct[a];
        const group& t = ct[b];
        if(!conditionals.empty()) {
            update_relation(r, ct, a, b, conditionals);
        } else {
            update_relation(r, ct, a, b, overshare_weight);
        }
        if(r.inter <= 0)
            return;
        const group& l = a < b ? s : t;
        const group& h = a < b ? s : t;
        unsigned int ma, mb;

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
            ma = a < b ? a : b;
            mb = a > b ? a : b;
            m = dominate;
            min_error = low_dominate;
        }
        score_t high_dominate = r.low_index_diff + r.high_index_overshare;
        if(!no_dominate && high_dominate < min_error) {
            ma = a > b ? a : b;
            mb = a < b ? a : b;
            m = dominate;
            min_error = high_dominate;
        }
        
        if(m != none) {
            move nm;
            nm.a = ma;
            nm.b = mb;
            nm.e = min_error;
            nm.t = m;
            
            moves.push_back(nm);
        }
    }
    move best_move() const {
        if(moves.empty()) {
            throw std::runtime_error("no move left");
        }
        score_t min_error = std::numeric_limits<score_t>::max();
        unsigned int best = ~0U;
        for(unsigned int i = 0; i < moves.size(); ++i) {
            const move& m = moves[i];
            if(m.e < min_error) {
                best = i;
                min_error = m.e;
            }
        }
        return moves[best];
    }
private:
    move_list moves;
    const group_list& ct;
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
    bool remove_most_common;
    std::vector<unsigned int> save_at_v;
    std::set<unsigned int> save_at;
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
        ("no-discard", po::value<bool>(&no_discard)->default_value(0), "don't consider discard moves")
        ("no-dominate", po::value<bool>(&no_dominate)->default_value(0), "don't consider dominate moves")
        ("no-intersect", po::value<bool>(&no_intersect)->default_value(0), "don't consider intersect moves")
        ("no-merge", po::value<bool>(&no_merge)->default_value(0), "don't consider merge moves")

        ("save", po::value<std::string>(&save_base), "base path to save the data at")
        ("save-at", po::value<std::vector<unsigned int> >(&save_at_v), "save data at these values")
        ("save-moves", po::value<bool>(&save_moves)->default_value(0), "save move data")
        ("save-groups", po::value<bool>(&save_groups)->default_value(0), "save group data")
        ("save-scores", po::value<bool>(&save_scores)->default_value(0), "save scores")

        ("conditionals", "overshare penalty based on conditionals")
        ("penalty", po::value<score_t>(&overshare_weight)->default_value(.5), "overshare penalty, ignored for conditionals")
        ("remove-most-common", po::value<bool>(&remove_most_common)->default_value(1), "remove the most common individual (owner)")
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
    group_list cg;
    initial_group_partition_map igpm;
    entity_map em;

    if(!vm.count("load-raw")) {
        std::cout << "must load some data" << std::endl;
        return 1;
    }

    std::size_t max_id = 0;
    std::vector<char> buffer(128 * 1024);
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
                            g.clear();
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
                    unsigned int node = cg.size();
                    cg.push_back(group());
                    cg.back().members = g;
                    cg.back().weight = count;
                    igpm.insert(r, std::make_pair(g, node));
                } else {
                    unsigned int node = r->second;
                    cg[node].weight += count;
                }
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

    std::map<unsigned int, score_t> ppl;
    for(unsigned int i = 0; i < cg.size();) {
        if(cg[i].weight >= threshold) {
            for(members_t::iterator j = cg[i].members.begin(); j != cg[i].members.end(); ++j) {
                ppl[*j] += cg[i].weight;
            }
            ++i;
        } else {
            std::swap(cg[i], cg.back());
            cg.pop_back();
        }
    }
    //remove the owner, todo, this is evil because now there are dupe groups if A was owner and A B C and B C existed
    if(!ppl.empty()) {
        if(remove_most_common) {
            unsigned int max_person = ppl.begin()->first;
            score_t max_val = ppl.begin()->second;
            for(std::map<unsigned int, score_t>::iterator j = ppl.begin(); j != ppl.end(); ++j) {
                if(j->second > max_val) {
                    max_val = j->second;
                    max_person = j->first;
                }
            }
            for(unsigned int i = 0; i < cg.size();) {
                members_t::iterator k = std::find(cg[i].members.begin(), cg[i].members.end(), max_person);
                if(k != cg[i].members.end()) {
                    cg[i].members.erase(k);
                }
                if(cg[i].members.empty()) {
                    std::swap(cg[i], cg.back());
                    cg.pop_back();
                } else {
                    ++i;
                }
            }
        }
        for(std::map<unsigned int, score_t>::iterator j = ppl.begin(); j != ppl.end();) {
            if(j->second >= person_threshold) {
                std::map<unsigned int, score_t>::iterator to_delete = j++;
                ppl.erase(to_delete);
            } else {
                ++j;
            }
        }
        for(unsigned int i = 0; i < cg.size();) {
            members_t& m = cg[i].members;
            for(std::size_t o = 0; o < m.size();) {
                if(ppl.find(m[o]) != ppl.end()) {
                    m.erase(m.begin() + o);
                } else {
                    ++o;
                }
            }
            if(m.empty()) {
                std::swap(cg[i], cg.back());
                cg.pop_back();
            } else {
                ++i;
            }
        }
    }
    if(no_individuals) {
        for(unsigned int i = 0; i < cg.size();) {
            if(cg[i].members.size() > 1) {
                ++i;
            } else {
                std::swap(cg[i], cg.back());
                cg.pop_back();
            }
        }
    }
    //normalize group weights for large groups
    for(unsigned int i = 0; i < cg.size(); ++i) {
        if(cg[i].members.size() < 20) 
            continue;
        cg[i].weight *= score_t(20) / cg[i].members.size();
    }
        
    c_vec counts;
    p_vec conditionals;
    if(vm.count("conditionals")) {
        counts.resize(max_id);
        conditionals.resize(max_id);
        std::cout << "computing conditionals" << std::endl;
        for(p_vec::iterator i = conditionals.begin(); i != conditionals.end(); ++i) {
            i->resize(max_id);
        }
        for(unsigned int i = 0; i < cg.size(); ++i) {
            group& g = cg[i];
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
    
    update_list ul;
    std::cout << "initializing move cache" << std::endl;
    move_cache mc(cg, no_merge, no_intersect, no_dominate, no_discard, conditionals, overshare_weight);
    std::cout << "running from " << cg.size() << " groups" << std::endl;
    for(int iteration = 0; iteration < cg.size() - 1; ++iteration) {
        unsigned int num_g = cg.size() - iteration;
        if(!save_base.empty() && save_groups && save_at.count(num_g)) {
            std::ostringstream fn;
            fn << save_base << "-" << std::setfill('0') << std::setw(6) <<  num_g << ".txt";
            fs::path path(fn.str());
            if(fs::exists(path))
                fs::remove(path);
            fs::ofstream out(path);
            for(unsigned int i = 0; i < cg.size(); ++i) {
                group& g = cg[i];
                if(g.dead)
                    continue;
                std::set<std::string> names;
                for(members_t::const_iterator i = g.members.begin(); i != g.members.end(); ++i) {
                    names.insert(email_id.by<bit>().equal_range(*i).first->second);
                }
                out << (g.members.size() * g.weight) << " ";
                std::copy(names.begin(), names.end(), std::ostream_iterator<std::string>(out, " "));
                out << std::endl;
            }
        }
        if(scores) {
            score_t s = 0;
            for(unsigned int i = 0; i < cg.size(); ++i) {
                group& g = cg[i];
                if(g.dead)
                    continue;
                s += g.members.size() * g.weight;
            }
            (*scores) << num_g << " " << s << " ";
        }
        
        move bm;
        try {
            bm = mc.best_move();
        } catch(...) {
            std::cout << std::endl;
            std::cout << "no move possible aborting" << std::endl;
            return 1;
        }
    
        score_t min_error = bm.e;
        move_type m = bm.t;
        unsigned int a = bm.a;
        unsigned int b = bm.b;
        relation r;
        if(m != discard) {
            if(!conditionals.empty()) {
                update_relation(r, cg, a, b, conditionals);
            } else {
                update_relation(r, cg, a, b, overshare_weight);
            }
        }
    
        ul.clear();
        // std::cout << "err " << min_error << " ";
        //apply the move
        switch(m) {
        case merge: {
            std::cout << "M" << std::flush;
            if(scores) {
                *scores << "M" << std::endl;
            }
            if(moves) {
                group& s = cg[a];
                group& t = cg[b];
                group& l = a < b ? s : t;
                group& h = a > b ? s : t;
    
                score_t h_unique = r.high_index_diff / h.weight;
                score_t l_unique = r.low_index_diff / l.weight;
    
                score_t eff_penalty = (r.high_index_overshare + r.low_index_overshare) / (h_unique * l.weight + l_unique * h.weight);
                (*moves) << "merge E=" << min_error << " G=" << num_g
                    << " eff penalty=" << eff_penalty << std::endl;
                {
                    group& g = cg[a];
                    std::set<std::string> names;
                    for(members_t::const_iterator i = g.members.begin(); i != g.members.end(); ++i) {
                        names.insert(email_id.by<bit>().equal_range(*i).first->second);
                    }
                    (*moves) << "\t" << g.members.size() * g.weight << " ";
                    std::copy(names.begin(), names.end(), std::ostream_iterator<std::string>(*moves, " "));
                    (*moves) << std::endl;
                }
                {
                    group& g = cg[b];
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
            std::set_union(cg[a].members.begin(), cg[a].members.end(), cg[b].members.begin(), cg[b].members.end(), std::inserter(n, n.end()));
            std::swap(cg[a].members, n);
            cg[a].weight = (r.uni - min_error) / cg[a].members.size();
            mc.remove_moves(a, b, ul);
            cg[b].dead = true;
            break;
        }
        case intersect: {
            std::cout << "I" << std::flush;
            if(scores) {
                *scores << "I" << std::endl;
            }
            if(moves) {
                (*moves) << "intersect E=" << min_error << " G=" << num_g << std::endl;
                {
                    group& g = cg[a];
                    std::set<std::string> names;
                    for(members_t::const_iterator i = g.members.begin(); i != g.members.end(); ++i) {
                        names.insert(email_id.by<bit>().equal_range(*i).first->second);
                    }
                    (*moves) << "\t" << g.members.size() * g.weight << " ";
                    std::copy(names.begin(), names.end(), std::ostream_iterator<std::string>(*moves, " "));
                    (*moves) << std::endl;
                }
                {
                    group& g = cg[b];
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
            std::set_intersection(cg[a].members.begin(), cg[a].members.end(), cg[b].members.begin(), cg[b].members.end(), std::inserter(n, n.end()));
            std::swap(cg[a].members, n);
            cg[a].weight = (r.uni - min_error) / cg[a].members.size();
            mc.remove_moves(a, b, ul);
            cg[b].dead = true;
            break;
        }
        case discard: {
            std::cout << "-" << std::flush;
            if(scores) {
                *scores << "-" << std::endl;
            }
            if(moves) {
                (*moves) << "discard E=" << min_error << " G=" << num_g << std::endl;
                group& g = cg[a];
                std::set<std::string> names;
                for(members_t::const_iterator i = g.members.begin(); i != g.members.end(); ++i) {
                    names.insert(email_id.by<bit>().equal_range(*i).first->second);
                }
                (*moves) << "\t" << g.members.size() * g.weight << " ";
                std::copy(names.begin(), names.end(), std::ostream_iterator<std::string>(*moves, " "));
                (*moves) << std::endl;
            }
            mc.remove_moves(a);
            cg[a].dead = true;
            break;
        }
        case dominate: {
            std::cout << "D" << std::flush;
            if(scores) {
                *scores << "D" << std::endl;
            }
            if(moves) {
                group& s = cg[a];
                group& t = cg[b];
                group& l = a < b ? s : t;
                group& h = a > b ? s : t;
    
                score_t h_unique = r.high_index_diff / h.weight;
                score_t l_unique = r.low_index_diff / l.weight;
    
                score_t eff_penalty = (r.high_index_diff + r.low_index_overshare) < (r.low_index_diff + r.high_index_overshare) ? 
                    r.low_index_overshare / (l_unique * h.weight):
                    r.high_index_overshare / (h_unique * h.weight);
                (*moves) << "dominate E=" << min_error << " G=" << num_g << " eff penalty=" << eff_penalty << std::endl;
                {
                    group& g = cg[a];
                    std::set<std::string> names;
                    for(members_t::const_iterator i = g.members.begin(); i != g.members.end(); ++i) {
                        names.insert(email_id.by<bit>().equal_range(*i).first->second);
                    }
                    (*moves) << "\t" << g.members.size() * g.weight << " ";
                    std::copy(names.begin(), names.end(), std::ostream_iterator<std::string>(*moves, " "));
                    (*moves) << std::endl;
                }
                {
                    group& g = cg[b];
                    std::set<std::string> names;
                    for(members_t::const_iterator i = g.members.begin(); i != g.members.end(); ++i) {
                        names.insert(email_id.by<bit>().equal_range(*i).first->second);
                    }
                    (*moves) << "\t" << g.members.size() * g.weight << " ";
                    std::copy(names.begin(), names.end(), std::ostream_iterator<std::string>(*moves, " "));
                    (*moves) << std::endl;
                }
                
            }
            cg[a].weight = (r.uni - min_error) / cg[a].members.size();
            mc.remove_moves(a, b, ul);
            cg[b].dead = true;
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
                group& g = cg[a];
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
    std::cout << std::endl;
    return 0;
}

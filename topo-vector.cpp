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
#include <boost/graph/graph_traits.hpp>
#include <boost/graph/graphviz.hpp>
#include <boost/graph/kruskal_min_spanning_tree.hpp>
#include <map>
#include <set>
#include "entity.h"

namespace po = boost::program_options;
namespace fs = boost::filesystem;
namespace gr = boost; //weird but they didnt subspace it


typedef float score_t;
typedef std::map<unsigned int, score_t> members_t;
struct group {
    members_t members;
    score_t weight;
    unsigned int index;
    score_t error;
    group() : weight(0), index(0), error(0) {}
};
struct relation {
    score_t error;
    bool inter;
    score_t unrepresented;
    relation() : error(0), inter(false){}
};

typedef gr::adjacency_list<gr::setS, gr::setS, gr::undirectedS, group, relation> connectedness_graph;
    
typedef std::set<std::string> message_id_set;
//ordering function (ordered on the lowest member that is different, if all the same then the shorter sequence is lower)
struct group_member_compare {
    bool operator() (const members_t& a, const members_t& b) const {
        members_t::const_iterator i = a.begin();
        members_t::const_iterator j = b.begin();
        while(i != a.end() && j != b.end()) {
            if(i->first == j->first) {
                ++i;
                ++j;
            } else if(i->first < j->first) {
                return true;
            } else {
                return false;
            }
        }
        if(i != a.end()) {
            return false;
        }
        if(j != b.end()) {
            return true;
        }
        return false;
    }
};
typedef std::map<members_t, connectedness_graph::vertex_descriptor, group_member_compare> initial_group_partition_map;

boost::regex re_terms("([^:]+): ([^\r\n]+[\r\n]+(?:\\s+[^\r\n]+[\r\n]+)*)");
boost::regex re_email("(?:(?:\"([^\"]+)\"\\s+<)|(?:(?:^|,)\\s*([^<,@\"]+)\\s+<))?(\\b[A-Z0-9._%+-]+@[A-Z0-9.-]+\\.[A-Z]{2,4}\\b)", boost::regex::icase);

typedef std::vector<std::vector<score_t> > p_vec;
typedef std::vector<score_t> c_vec;


inline score_t overshare(const p_vec& conditionals, const members_t& m, unsigned int p) {
    score_t partial = 0;
    score_t total = 0;
    for(members_t::const_iterator i = m.begin(); i != m.end(); ++i) {
        if(p == i->first) 
            continue;
        partial += conditionals[i->first][p];
        ++total;
    }
    //if there is no one outside the current user it means that we have no penalty
    if(total == 0)
        return 0;
    return partial / total;
}

void update_group(group& p, const p_vec& conditionals) {
    p.error = 0;
    for(members_t::const_iterator i = p.members.begin(); i != p.members.end(); ++i) {
        score_t overshare_weight = overshare(conditionals, p.members, i->first);
        bool in_p = true;
        p.error += in_p ? i->second - overshare_weight * (p.weight - i->second) : 0;
    }
}
void update_group(group& p, score_t overshare) {
    p.error = 0;
    for(members_t::const_iterator i = p.members.begin(); i != p.members.end(); ++i) {
        bool in_p = overshare * (p.weight - i->second) < i->second;
        p.error += in_p ? i->second - overshare * (p.weight - i->second) : 0;
    }
}

void update_relation(relation& r, const group& p, const group& q, score_t overshare) {
    r.error = 0;
    r.inter = false;
    r.unrepresented = 0;
    score_t mag_p = 0, mag_q = 0;
    members_t::const_iterator i = p.members.begin();
    members_t::const_iterator j = q.members.begin();
    while(i != p.members.end() && j != q.members.end()) {
        if(i->first == j->first) {
            bool in_p = overshare * (p.weight - i->second) < i->second;
            bool in_q = overshare * (q.weight - j->second) < j->second;
            if(in_p && in_q) 
                r.inter = true;
            bool in_merge = overshare * (p.weight + q.weight - i->second - j->second) < i->second + j->second;
            score_t o = (in_p ? i->second - overshare * (p.weight - i->second): 0) + (in_q ? j->second - overshare * (q.weight - j->second) : 0);
            score_t n = in_merge ? (i->second + j->second) - overshare * (p.weight + q.weight - i->second - j->second) : 0;
            r.error += o - n;
            mag_p += (!in_p ? i->second : 0) * (!in_p ? i->second : 0);
            mag_q += (!in_q ? j->second : 0) * (!in_q ? j->second : 0);
            r.unrepresented += (!in_p ? i->second : 0) * (!in_q ? j->second : 0);
            ++i;
            ++j;
        } else if(i->first < j->first) {
            //this person is reached via p, but not q
            bool in_p = overshare * (p.weight - i->second) < i->second;
            bool in_merge = overshare * (p.weight + q.weight - i->second) < i->second;
            score_t o = (in_p ? i->second - overshare * (p.weight - i->second) : 0);
            score_t n = in_merge ? (i->second - overshare * (p.weight + q.weight - i->second)) : 0;
            r.error += o - n;
            mag_p += (!in_p ? i->second : 0) * (!in_p ? i->second : 0);
            ++i;
        } else {
            //this person is reached via q, but not p
            bool in_q = overshare * (q.weight - j->second) < j->second;
            bool in_merge = overshare * (p.weight + q.weight - j->second) < j->second;
            score_t o = (in_q ? j->second - overshare * (q.weight - j->second) : 0);
            score_t n = in_merge ? (j->second - overshare * (p.weight + q.weight - j->second)) : 0;
            r.error += o - n;
            mag_q += (!in_q ? j->second : 0) * (!in_q ? j->second : 0);
            ++j;
        }
    }
    //remaining i are all > the last j
    while(i != p.members.end()) {
        bool in_p = overshare * (p.weight - i->second) < i->second;
        bool in_merge = overshare * (p.weight + q.weight - i->second) < i->second;
        score_t o = (in_p ? i->second - overshare * (p.weight - i->second) : 0);
        score_t n = in_merge ? (i->second - overshare * (p.weight + q.weight - i->second)) : 0;
        r.error += o - n;
        mag_p += (!in_p ? i->second : 0) * (!in_p ? i->second : 0);
        ++i;
    }
    //remaining j are all > the last i
    while(j != q.members.end()) {
        bool in_q = overshare * (q.weight - j->second) < j->second;
        bool in_merge = overshare * (p.weight + q.weight - j->second) < j->second;
        score_t o = (in_q ? j->second - overshare * (q.weight - j->second) : 0);
        score_t n = in_merge ? (j->second - overshare * (p.weight + q.weight - j->second)) : 0;
        r.error += o - n;
        mag_q += (!in_q ? j->second : 0) * (!in_q ? j->second : 0);
        ++j;
    }
    r.unrepresented /= sqrt(mag_p + mag_q);
}

void merge_it(members_t& m, const group& p, const group& q) {
    m.clear();
    members_t::const_iterator i = p.members.begin();
    members_t::const_iterator j = q.members.begin();
    while(i != p.members.end() && j != q.members.end()) {
        if(i->first == j->first) {
            m.insert(m.end(), std::make_pair(i->first, i->second + j->second));
            ++i;
            ++j;
        } else if(i->first < j->first) {
            //this person is reached via p, but not q
            m.insert(m.end(), std::make_pair(i->first, i->second));
            ++i;
        } else {
            //this person is reached via q, but not p
            m.insert(m.end(), std::make_pair(j->first, j->second));
            ++j;
        }
    }
    //remaining i are all > the last j
    while(i != p.members.end()) {
        m.insert(m.end(), std::make_pair(i->first, i->second));
        ++i;
    }
    //remaining j are all > the last i
    while(j != q.members.end()) {
        m.insert(m.end(), std::make_pair(j->first, j->second));
        ++j;
    }
}
void update_relation(relation& r, const group& p, const group& q, const p_vec& conditionals) {
    r.error = 0;
    r.inter = false;
    r.unrepresented = 0;
    score_t mag_p = 0, mag_q = 0;
    members_t::const_iterator i = p.members.begin();
    members_t::const_iterator j = q.members.begin();
    bool inter = false;
    while(i != p.members.end() && j != q.members.end()) {
        if(i->first == j->first) {
            inter = true;
            break;
            ++i;
            ++j;
        } else if(i->first < j->first) {
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
    members_t combined;
    merge_it(combined, p, q);
    while(i != p.members.end() && j != q.members.end()) {
        if(i->first == j->first) {
            score_t overshare_weight = overshare(conditionals, combined, i->first);
            bool in_p = true;
            bool in_q = true;
            if(in_p && in_q) 
                r.inter = true;
            bool in_merge = true;
            score_t o = (in_p ? i->second - overshare_weight * (p.weight - i->second): 0) + (in_q ? j->second - overshare_weight * (q.weight - j->second) : 0);
            score_t n = in_merge ? (i->second + j->second) - overshare_weight * (p.weight + q.weight - i->second - j->second) : 0;
            r.error += o - n;
            mag_p += (!in_p ? i->second : 0) * (!in_p ? i->second : 0);
            mag_q += (!in_q ? j->second : 0) * (!in_q ? j->second : 0);
            r.unrepresented += (!in_p ? i->second : 0) * (!in_q ? j->second : 0);
            ++i;
            ++j;
        } else if(i->first < j->first) {
            score_t overshare_weight = overshare(conditionals, combined, i->first);
            //this person is reached via p, but not q
            bool in_p = true;
            bool in_merge = true;
            score_t o = (in_p ? i->second - overshare_weight * (p.weight - i->second) : 0);
            score_t n = in_merge ? (i->second - overshare_weight * (p.weight + q.weight - i->second)) : 0;
            r.error += o - n;
            mag_p += (!in_p ? i->second : 0) * (!in_p ? i->second : 0);
            ++i;
        } else {
            score_t overshare_weight = overshare(conditionals, combined, i->first);
            //this person is reached via q, but not p
            bool in_q = true;
            bool in_merge = true;
            score_t o = (in_q ? j->second - overshare_weight * (q.weight - j->second) : 0);
            score_t n = in_merge ? (j->second - overshare_weight * (p.weight + q.weight - j->second)) : 0;
            r.error += o - n;
            mag_q += (!in_q ? j->second : 0) * (!in_q ? j->second : 0);
            ++j;
        }
    }
    //remaining i are all > the last j
    while(i != p.members.end()) {
        score_t overshare_weight = overshare(conditionals, combined, i->first);
        bool in_p = true;
        bool in_merge = true;
        score_t o = (in_p ? i->second - overshare_weight * (p.weight - i->second) : 0);
        score_t n = in_merge ? (i->second - overshare_weight * (p.weight + q.weight - i->second)) : 0;
        r.error += o - n;
        mag_p += (!in_p ? i->second : 0) * (!in_p ? i->second : 0);
        ++i;
    }
    //remaining j are all > the last i
    while(j != q.members.end()) {
        score_t overshare_weight = overshare(conditionals, combined, i->first);
        bool in_q = true;
        bool in_merge = true;
        score_t o = (in_q ? j->second - overshare_weight * (q.weight - j->second) : 0);
        score_t n = in_merge ? (j->second - overshare_weight * (p.weight + q.weight - j->second)) : 0;
        r.error += o - n;
        mag_q += (!in_q ? j->second : 0) * (!in_q ? j->second : 0);
        ++j;
    }
    r.unrepresented /= sqrt(mag_p + mag_q);
}



int main(int argc, char* argv[])
{
    std::vector<fs::path> from;
    std::vector<fs::path> entity;
    score_t overshare_weight;
    std::string ignore_string, save_base;
    unsigned int threshold;
    unsigned int person_threshold;
    bool no_merge;
    bool no_discard;
    bool no_individuals;
    unsigned int remove_most_common;
    std::vector<unsigned int> save_at_v;
    std::set<unsigned int> save_at;
    std::vector<std::string> remove_these;
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
        ("run", "run it")
        ("no-discard", po::value<bool>(&no_discard)->default_value(0), "don't consider discard moves")
        ("no-merge", po::value<bool>(&no_merge)->default_value(0), "don't consider merge moves")
        ("no-individuals", po::value<bool>(&no_individuals)->default_value(0), "ignore individuals")

        ("save", po::value<std::string>(&save_base), "base path to save the data at")
        ("save-at", po::value<std::vector<unsigned int> >(&save_at_v), "save data at these values")
        ("save-moves", po::value<bool>(&save_moves)->default_value(0), "save move data")
        ("save-groups", po::value<bool>(&save_groups)->default_value(0), "save group data")
        ("save-scores", po::value<bool>(&save_scores)->default_value(0), "save scores")

        ("conditionals", "overshare penalty based on conditionals")
        ("remove-most-common", po::value<unsigned int>(&remove_most_common)->default_value(1), "remove the most common individual (owner)")
        ("penalty", po::value<score_t>(&overshare_weight)->default_value(1), "overshare penalty (ignored for conditionals)")
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
                        g.insert(std::make_pair(result.first->second, 1));
                    }
                }

                if(g.empty()) {
                    //no emails? wtfs
                    continue;
                }
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
    for(connectedness_graph::vertex_iterator i = gr::vertices(cg).first; i != gr::vertices(cg).second;) {
        if(cg[*i].weight >= threshold) {
            for(members_t::iterator j = cg[*i].members.begin(); j != cg[*i].members.end(); ++j) {
                ppl[j->first] += cg[*i].weight;
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
                cg[*i].members.erase(max_person);
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

        for(std::map<unsigned int, score_t>::iterator j = ppl.begin(); j != ppl.end(); ++j) {
            for(connectedness_graph::vertex_iterator i = gr::vertices(cg).first; i != gr::vertices(cg).second;) {
                cg[*i].members.erase(j->first);
                if(cg[*i].members.empty()) {
                    connectedness_graph::vertex_iterator to_delete = i;
                    ++i;
                    gr::clear_vertex(*to_delete, cg);
                    gr::remove_vertex(*to_delete, cg);
                } else {
                    ++i;
                }
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
    //normalize group weights for large groups
    for(connectedness_graph::vertex_iterator i = gr::vertices(cg).first; i != gr::vertices(cg).second; ++i) {
        if(cg[*i].members.size() < 20) 
            continue;
        cg[*i].weight *= score_t(20) / cg[*i].members.size();
    }
    //per person values are in message-people units
    for(connectedness_graph::vertex_iterator i = gr::vertices(cg).first; i != gr::vertices(cg).second; ++i) {
        for(members_t::iterator j = cg[*i].members.begin(); j != cg[*i].members.end(); ++j) {
            j->second *= cg[*i].weight;
        }
    }
    unsigned int vertex_number = 0;
    for(connectedness_graph::vertex_iterator i = gr::vertices(cg).first; i != gr::vertices(cg).second; ++i) {
        cg[*i].index = vertex_number++;
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
        for(connectedness_graph::vertex_iterator v = gr::vertices(cg).first; v != gr::vertices(cg).second; ++v) {
            group& g = cg[*v];
            for(members_t::const_iterator i = g.members.begin(); i != g.members.end(); ++i) {
                if(i->first >= counts.size()) {
                    std::cout << "bad index? " << i->first << " vs " << counts.size() << std::endl;
                }
                counts[i->first] += g.weight;
                for(members_t::const_iterator j = g.members.begin(); j != g.members.end(); ++j) {
                    conditionals[i->first][j->first] += g.weight;
                }
            }
        }
        for(unsigned int i = 0; i < max_id; ++i) {
            for(unsigned int j = 0; j < max_id; ++j) {
                conditionals[i][j] = 1.0 - conditionals[i][j] / counts[i]; // P(!J | I)
            }
        }
    }
    
    std::cout << "computing initial connectedness" << std::endl;
    for(connectedness_graph::vertex_iterator i = gr::vertices(cg).first; i != gr::vertices(cg).second; ++i) {
        if(!conditionals.empty()) {
            update_group(cg[*i], conditionals);
        } else {
            update_group(cg[*i], overshare_weight);
        }
        connectedness_graph::vertex_iterator j = i;
        for(++j; j != gr::vertices(cg).second; ++j) {
            connectedness_graph::edge_descriptor e;
            unsigned int uni, inter, lid, hid;
            relation r;
            if(!conditionals.empty()) {
                update_relation(r, cg[*i], cg[*j], conditionals);
            } else {
                update_relation(r, cg[*i], cg[*j], overshare_weight);
            }
            if(!r.inter)
                continue;
            e = gr::add_edge(*i, *j, cg).first;
            cg[e] = r;
        }
    }

    connectedness_graph ct(cg);
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
    
    
    std::cout << "running from " << gr::num_vertices(ct) << " groups" << std::endl;
    for(int iteration = 0; gr::num_vertices(ct) > 0; ++iteration) {
        if(!save_base.empty() && save_groups && save_at.count(gr::num_vertices(ct))) {
            std::ostringstream fn;
            fn << save_base << "-" << std::setfill('0') << std::setw(6) << gr::num_vertices(ct) << ".txt";
            fs::path path(fn.str());
            if(fs::exists(path))
                fs::remove(path);
            fs::ofstream out(path);
            gr::graph_traits<connectedness_graph>::vertex_iterator v, v_e;
            for(boost::tie(v, v_e) = gr::vertices(ct); v != v_e; ++v) {
                group& g = ct[*v];
                std::set<std::string> names;
                for(members_t::const_iterator i = g.members.begin(); i != g.members.end(); ++i) {
                    if(!conditionals.empty() || overshare_weight * (g.weight - i->second) < i->second)
                        names.insert(email_id.by<bit>().equal_range(i->first).first->second);
                }
                out << g.error << " ";
                std::copy(names.begin(), names.end(), std::ostream_iterator<std::string>(out, " "));
                out << std::endl;
            }
        }
        if(scores) {
            score_t s = 0;
            gr::graph_traits<connectedness_graph>::vertex_iterator v, v_e;
            for(boost::tie(v, v_e) = gr::vertices(ct); v != v_e; ++v) {
                group& g = ct[*v];
                s += g.error;
            }
            (*scores) << gr::num_vertices(ct) << " " << s <<  " ";
        }
        if(gr::num_vertices(ct) == 1) {
            std::cout << std::endl;
            break;
        }
        score_t min_error = std::numeric_limits<score_t>::max();
        score_t most_compatible = -std::numeric_limits<score_t>::max();
        enum move_type { none, discard, merge } m;
        connectedness_graph::vertex_descriptor a;
        connectedness_graph::vertex_descriptor b;
        connectedness_graph::edge_descriptor ab;
        
        m = none;
        //iterated and pick a move
        gr::graph_traits<connectedness_graph>::edge_iterator e, e_e;
        if(!no_merge) {
            for(boost::tie(e, e_e) = gr::edges(ct); e != e_e; ++e) {
                relation& r = ct[*e];
                if(r.error < min_error || r.error == min_error && r.unrepresented > most_compatible) {
                    if(r.error == min_error)
                        most_compatible = r.unrepresented;
                    else 
                        most_compatible = -std::numeric_limits<score_t>::max();
                    a = gr::source(*e, ct);
                    b = gr::target(*e, ct);
                    ab = *e;
                    m = merge;
                    min_error = r.error;
                }
            }
        }

        if(!no_discard) {
            gr::graph_traits<connectedness_graph>::vertex_iterator v, v_e;
            for(boost::tie(v, v_e) = gr::vertices(ct); v != v_e; ++v) {
                group& s = ct[*v];
                if(s.error < min_error) {
                    a = *v;
                    m = discard;
                    min_error = s.error;
                }
            }
        }
        if(m == none) {
            std::cout << std::endl;
            std::cout << "no move possible aborting" << std::endl;
            return 1;
        }

        // std::cout << "err " << min_error << " ";
        //apply the move
        switch(m) {
        case merge: {
            std::cout << "M" << std::flush;
            if(scores) {
                *scores << "M" << std::endl;
            }
            if(moves) {
                (*moves) << "merge E=" << min_error << " G=" << gr::num_vertices(ct) << std::endl;
                {
                    group& g = ct[a];
                    std::set<std::string> names;
                    for(members_t::const_iterator i = g.members.begin(); i != g.members.end(); ++i) {
                        if(!conditionals.empty() || overshare_weight * (g.weight - i->second) < i->second)
                            names.insert(email_id.by<bit>().equal_range(i->first).first->second);
                    }
                    (*moves) << "\t" << g.error << " ";
                    std::copy(names.begin(), names.end(), std::ostream_iterator<std::string>(*moves, " "));
                    (*moves) << std::endl;
                }
                {
                    group& g = ct[b];
                    std::set<std::string> names;
                    for(members_t::const_iterator i = g.members.begin(); i != g.members.end(); ++i) {
                        if(!conditionals.empty() || overshare_weight * (g.weight - i->second) < i->second)
                            names.insert(email_id.by<bit>().equal_range(i->first).first->second);
                    }
                    (*moves) << "\t" << g.error << " ";
                    std::copy(names.begin(), names.end(), std::ostream_iterator<std::string>(*moves, " "));
                    (*moves) << std::endl;
                }
                
            }

            members_t n;
            merge_it(n, ct[a], ct[b]);
            std::swap(ct[a].members, n);
            ct[a].weight = ct[a].weight + ct[b].weight;
            connectedness_graph::adjacency_iterator v, v_e;
            for(boost::tie(v, v_e) = gr::adjacent_vertices(b, ct); v != v_e; ++v) {
                if(a == *v)
                    continue;
                if(!gr::edge(a, *v, ct).second) {
                    gr::add_edge(a, *v, ct);
                }
            }
            gr::clear_vertex(b, ct);
            gr::remove_vertex(b, ct);
            break;
        }
        case discard: {
            std::cout << "-" << std::flush;
            if(scores) {
                *scores << "-" << std::endl;
            }
            if(moves) {
                (*moves) << "discard E=" << ct[a].error << " G=" << gr::num_vertices(ct) << std::endl;
                {
                    group& g = ct[a];
                    std::set<std::string> names;
                    for(members_t::const_iterator i = g.members.begin(); i != g.members.end(); ++i) {
                        if(!conditionals.empty() || overshare_weight * (g.weight - i->second) < i->second)
                            names.insert(email_id.by<bit>().equal_range(i->first).first->second);
                    }
                    (*moves) << "\t" << ct[a].error << " ";
                    std::copy(names.begin(), names.end(), std::ostream_iterator<std::string>(*moves, " "));
                    (*moves) << std::endl;
                }
            }
            gr::clear_vertex(a, ct);
            gr::remove_vertex(a, ct);
            break;
        }
        }

        //update weights
        if(m != discard) {
            gr::graph_traits<connectedness_graph>::out_edge_iterator ei, ee;
            for(boost::tie(ei,ee) = gr::out_edges(a, ct); ei != ee;) {
                relation& r = ct[*ei];
                if(!conditionals.empty()) {
                    update_relation(r, ct[gr::source(*ei, ct)], ct[gr::target(*ei, ct)], conditionals);
                } else {
                    update_relation(r, ct[gr::source(*ei, ct)], ct[gr::target(*ei, ct)], overshare_weight);
                }
                //intersection may have removed an edge
                if(!r.inter) {
                    gr::graph_traits<connectedness_graph>::out_edge_iterator to_delete = ei++;
                    gr::remove_edge(to_delete, ct);
                } else {
                    ++ei;
                }
            }
            if(!conditionals.empty()) {
                update_group(ct[a], conditionals);
            } else {
                update_group(ct[a], overshare_weight);
            }

            if(moves) {
                group& g = ct[a];
                std::set<std::string> names;
                for(members_t::const_iterator i = g.members.begin(); i != g.members.end(); ++i) {
                    if(!conditionals.empty() || overshare_weight * (g.weight - i->second) < i->second)
                        names.insert(email_id.by<bit>().equal_range(i->first).first->second);
                }
                (*moves) << "\t=" << g.error << " ";
                std::copy(names.begin(), names.end(), std::ostream_iterator<std::string>(*moves, " "));
                (*moves) << std::endl;
            }

        }
    }
    return 0;
}

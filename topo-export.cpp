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
#include <boost/graph/betweenness_centrality.hpp>
#include <boost/graph/graphml.hpp>
#include <map>
#include <set>
#include "entity.h"

namespace po = boost::program_options;
namespace fs = boost::filesystem;
namespace gr = boost; //weird but they didnt subspace it


typedef std::set<unsigned int> members_t;
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

struct person {
    std::string name;
    unsigned int id;
    person() : id(0) {}
};

struct edge {
    score_t weight;
    edge() : weight(0) {}
};

typedef gr::adjacency_list<gr::setS, gr::setS, gr::undirectedS, group, relation> connectedness_graph;
typedef gr::adjacency_list<gr::setS, gr::setS, gr::undirectedS, person, edge> people_graph;
    
typedef std::set<std::string> message_id_set;
typedef std::map<members_t, connectedness_graph::vertex_descriptor> initial_group_partition_map;


boost::regex re_terms("([^:]+): ([^\r\n]+[\r\n]+(?:\\s+[^\r\n]+[\r\n]+)*)");
boost::regex re_email("(?:(?:\"([^\"]+)\"\\s+<)|(?:(?:^|,)\\s*([^<,@\"]+)\\s+<))?(\\b[A-Z0-9._%+-]+@[A-Z0-9.-]+\\.[A-Z]{2,4}\\b)", boost::regex::icase);

int main(int argc, char* argv[])
{
    std::vector<fs::path> from;
    std::vector<fs::path> entity;
    std::string ignore_string, save_base;
    unsigned int threshold;
    unsigned int person_threshold;
    bool no_individuals;
    bool remove_most_common;
    std::vector<unsigned int> save_at_v;
    std::set<unsigned int> save_at;
    
    //[Gmail]/Sent Mail
    po::options_description general_options("General");
    general_options.add_options()
        ("help", "list options");
    po::options_description file_options("Load");
    file_options.add_options()
        ("ignore", po::value<std::string>(&ignore_string)->default_value("@lists\\.|@googlegroups\\.|@yahoogroups\\.|@mailman\\.|@facebookmail\\.|noreply|do[-_]not[-_]reply|^buzz\\+"), "ignore messages with a recipient matching this expression")
        ("entity-raw", po::value<std::vector<fs::path> >(&entity), "paths to load data ONLY for entities")
        ("load-raw", po::value<std::vector<fs::path> >(&from), "paths to load data from");
    po::options_description run_options("Export Options");
    run_options.add_options()
        ("save", po::value<std::string>(&save_base), "base path to save the data at")
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
    connectedness_graph cg;
    initial_group_partition_map igpm;
    entity_map em;

    if(!vm.count("load-raw")) {
        std::cout << "must load something" << std::endl;
        return 1;
    }
    if(!vm.count("save")) {
        std::cout << "must save something" << std::endl;
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
                        g.insert(result.first->second);
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
        if(remove_most_common) {
            unsigned int max_person = ppl.begin()->first;
            score_t max_val = ppl.begin()->second;
            for(std::map<unsigned int, score_t>::iterator j = ppl.begin(); j != ppl.end(); ++j) {
                if(j->second > max_val) {
                    max_val = j->second;
                    max_person = j->first;
                }
            }
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
        }
        for(std::map<unsigned int, score_t>::iterator j = ppl.begin(); j != ppl.end();) {
            if(j->second >= person_threshold) {
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
    unsigned int vertex_number = 0;
    for(connectedness_graph::vertex_iterator i = gr::vertices(cg).first; i != gr::vertices(cg).second; ++i) {
        cg[*i].index = vertex_number++;
    }
    
    std::cout << "converting to person graph" << std::endl;
    people_graph pg;
    std::map<unsigned int, people_graph::vertex_descriptor> remaining_people;
    for(connectedness_graph::vertex_iterator i = gr::vertices(cg).first; i != gr::vertices(cg).second; ++i) {
        group& g = cg[*i];
        for(members_t::const_iterator j = g.members.begin(); j != g.members.end(); ++j) {
            //if there is a new person represented add them to the map
            std::pair<std::map<unsigned int, people_graph::vertex_descriptor>::iterator, bool> res =
                remaining_people.insert(std::make_pair(*j, people_graph::vertex_descriptor()));
            if(res.second) {
                res.first->second = gr::add_vertex(pg);
                person& p = pg[res.first->second];
                p.id = res.first->first;
                p.name = email_id.by<bit>().equal_range(p.id).first->second;
            }
        }
    }
    for(connectedness_graph::vertex_iterator i = gr::vertices(cg).first; i != gr::vertices(cg).second; ++i) {
        group& g = cg[*i];
        for(members_t::const_iterator j = g.members.begin(); j != g.members.end(); ++j) {
            members_t::const_iterator k = j;
            for(++k; k != g.members.end(); ++k) {
                //duplicates eliminated by setS type container
                people_graph::edge_descriptor l = gr::add_edge(remaining_people[*j], remaining_people[*k], pg).first;
                edge& e = pg[l];
                e.weight += g.weight;
            }
        }
    }
    fs::path path(save_base);
    if(fs::exists(path))
        fs::remove(path);
    fs::ofstream out(path);

    gr::dynamic_properties dp;
    dp.property("label", get(&person::name, pg));
    dp.property("weight", gr::get(&edge::weight, pg));

    gr::write_graphml(out, pg, gr::get(&person::id, pg), dp, false);
    return 0;
}

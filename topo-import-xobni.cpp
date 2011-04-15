#include <cstdlib>
#include <iostream>
#include <iomanip>
#include <sstream>
#include <boost/bind.hpp>
#include <boost/lexical_cast.hpp>
#include <boost/algorithm/string.hpp>
#include <boost/regex.hpp>
#include <boost/bimap.hpp>
#include <boost/bimap/set_of.hpp>
#include <boost/bimap/multiset_of.hpp>
#include <boost/program_options/variables_map.hpp>
#include <boost/program_options/options_description.hpp>
#include <boost/program_options/parsers.hpp>
#include <boost/filesystem/fstream.hpp>
#include <boost/graph/adjacency_list.hpp>
#include <boost/graph/graph_traits.hpp>
#include <boost/graph/graphviz.hpp>
#include <json_spirit/json_spirit_reader_template.h>
#include <map>
#include <set>
#include "entity.h"

namespace po = boost::program_options;
namespace fs = boost::filesystem;
namespace gr = boost; //weird but they didnt subspace it
namespace js = json_spirit;

typedef std::set<unsigned int> members_t;
typedef unsigned int score_t;
struct group {
    members_t members;
    score_t weight;
};
struct relation {
};

typedef gr::adjacency_list<gr::setS, gr::setS, gr::undirectedS, group, relation> connectedness_graph;
    
typedef std::set<std::string> message_id_set;
typedef std::map<members_t, connectedness_graph::vertex_descriptor> initial_group_partition_map;

int main(int argc, char* argv[])
{
    std::string server;
    std::string port;
    std::string user;
    std::string folder;
    std::string password;
    fs::path from;
    fs::path to;
    bool inbox;
    bool include_bcc;
    
    //[Gmail]/Sent Mail
    po::options_description general_options("General");
    general_options.add_options()
        ("help", "list options");
    po::options_description file_options("Load");
    file_options.add_options()
        ("save-raw", po::value<fs::path>(&to), "path to save the data (after download phase)");
    po::options_description source_options("Download");
    source_options.add_options()
        ("load", po::value<fs::path>(&from), "xobni data file")
        ("bcc", po::value<bool>(&include_bcc)->default_value(false), "include bccs")
        ("inbox", po::value<bool>(&inbox)->default_value(false), "get inbox instead of sent");
        
    po::options_description run_options("Run");
    
    po::options_description all_options("Email Topology Options");
    all_options
        .add(general_options)
        .add(file_options)
        .add(source_options);

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

    email_id_bimap email_id;
    connectedness_graph cg;
    entity_map em;
    initial_group_partition_map igpm;

    if(!vm.count("save-raw")) {
        std::cout << "you must specify --save-raw with a file name" << std::endl;
        return 1;
    }
    if(!vm.count("load") || !fs::exists(from)) {
        std::cout << "missing source data file" << std::endl;
        return 1;
    }
    fs::ifstream in(from);    
    std::vector<char> buffer(128 * 1024);
    std::cout << "loading " << from;
    while(in.good()) {
        in.getline(&buffer[0], buffer.size());
        std::string line = &buffer[0];
        boost::algorithm::trim(line);
        
        try {
            js::mValue val;
            js::read_string_or_throw(line, val);
            js::mObject& mail = val.get_obj();
            js::mValue& from = mail["from"];

            bool is_sent = from.type() == js::str_type && from.get_str() == "C0";
            if(is_sent && inbox) continue;
            if(!is_sent && !inbox) continue;

            members_t g;
            const char* lists_nobcc[] = { "from", "to", "cc", NULL };
            const char* lists_bcc[] = { "from", "to", "cc", "bcc", NULL };
            const char** lists = include_bcc ? lists_bcc : lists_nobcc;
            for(const char** list = lists; *list; ++list) {
                js::mValue& f = mail[*list];
                if(f.type() == js::str_type) {
                    std::pair<email_id_bimap::map_by<email>::iterator, bool> result = email_id.by<email>().insert(
                        email_id_bimap::map_by<email>::value_type(f.get_str(), email_id.size()));
                    if(result.second)
                        std::cout << "@" << std::flush;
                    g.insert(result.first->second);
                } else if(f.type() == js::array_type) {
                    js::mArray& a = f.get_array();
                    for(js::mArray::iterator i = a.begin(); i != a.end(); ++i) {
                        std::pair<email_id_bimap::map_by<email>::iterator, bool> result = email_id.by<email>().insert(
                            email_id_bimap::map_by<email>::value_type(i->get_str(), email_id.size()));
                        if(result.second)
                            std::cout << "@" << std::flush;
                        g.insert(result.first->second);
                    }
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
                cg[node].weight = 1;
                igpm.insert(r, std::make_pair(g, node));
            } else {
                connectedness_graph::vertex_descriptor node = r->second;
                cg[node].weight += 1;
            }
            std::cout << "." << std::flush;
        } catch(...) {
            std::cout << "?" << std::flush;
            continue;
        }
    }
    
    std::cout << std::endl;
    if(fs::exists(to))
        fs::remove(to);
    fs::ofstream out(to);
    std::cout << "saving data to " << to.file_string();        
    for(connectedness_graph::vertex_iterator i = gr::vertices(cg).first; i != gr::vertices(cg).second; ++i) {
        out << (unsigned long long)cg[*i].weight;
        for(members_t::iterator j = cg[*i].members.begin(); j != cg[*i].members.end(); ++j) {
            out << "\t" << email_id.by<bit>().equal_range(*j).first->second;
        }
        out << std::endl;
    }
    out << "-" << std::endl;
    for(entity_map::iterator i = em.begin(); i != em.end(); ++i) {
        out << i->first;
        for(std::set<std::string>::iterator k = i->second.begin(); k != i->second.end(); ++k) {
            out << "\t" << *k; 
        }
        out << std::endl;
    }
    return 0;
}

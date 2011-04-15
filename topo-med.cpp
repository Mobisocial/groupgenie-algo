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
    members_t members;
    score_t weight;
    group() : weight(0) {}
};

typedef std::vector<group> group_list;
    
typedef std::map<members_t, unsigned int> initial_group_partition_map;

int main(int argc, char* argv[])
{
    std::vector<fs::path> from;
    std::vector<fs::path> entity;
    score_t discard_weight;
    std::string ignore_string;
    unsigned int threshold;
    unsigned int person_threshold;
    bool no_individuals;
    bool remove_most_common;
    bool no_score;
    bool mfg_only;
    std::vector<fs::path> starters; 
    
    po::options_description general_options("General");
    general_options.add_options()
        ("help", "list options");
    po::options_description file_options("Load");
    file_options.add_options()
        ("ignore", po::value<std::string>(&ignore_string)->default_value("@lists\\.|@googlegroups\\.|@yahoogroups\\.|@mailman\\.|@facebookmail\\.|noreply|do[-_]not[-_]reply|^buzz\\+"), "ignore messages with a recipient matching this expression")
        ("entity-raw", po::value<std::vector<fs::path> >(&entity), "paths to load data ONLY for entities")
        ("load-raw", po::value<std::vector<fs::path> >(&from), "paths to load data from")
        ("load-starters", po::value<std::vector<fs::path> >(&starters), "paths to load topology starting point from")
        ("no-score", po::value<bool>(&no_score)->default_value(false), "the input data file does not include a score at the beginning");
    po::options_description run_options("Run");
    run_options.add_options()
        ("penalty", po::value<score_t>(&discard_weight)->default_value(1), "discard penalty")
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

    email_id_bimap email_id;
    group_list cg;
    initial_group_partition_map igpm;
    group_list topo_tg;
    entity_map em;

    if(!vm.count("load-raw")) {
        std::cout << "must load some data" << std::endl;
        return 1;
    }

    std::size_t max_id = 0;
    std::vector<char> buffer(128 * 1024);
    boost::regex re_ignore(ignore_string);
    boost::regex re_loader("([^\\s]+)");
    try {
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
                        count = boost::lexical_cast<score_t>(number);
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

    members_t blank;
    members_t all;
    for(unsigned int i = 0; i < cg.size(); ++i) {
        members_t new_all;
        std::set_union(all.begin(), all.end(),  cg[i].members.begin(),  cg[i].members.end(), std::back_inserter(new_all));
        std::swap(new_all, all);
    }
    std::size_t total_people = all.size();

    for(std::vector<fs::path>::iterator st = starters.begin(); st != starters.end(); ++st) {
        if(!fs::exists(*st)) {
            std::cout << "input file not found: " << *st << std::endl;
            return 1;
        }
        std::list<members_t> topo;
        std::cout << "loading topology - " << *st;
        fs::ifstream in(*st);
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
                if(!no_score && first) {
                    first = false;
                    std::string number = (*j)[0].str();
                    count = boost::lexical_cast<score_t>(number);
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
            topo.push_back(g);
            std::cout << "." << std::flush;
        }
        std::cout << std::endl;

        {
            std::cout << "computing edit distance";
            fs::ofstream out(st->branch_path() / ("edit-distance-" + st->leaf()));

            members_t temp;
            for(unsigned int i = 0; i < cg.size(); ++i) {
                std::size_t extra_blank = 0;
                std::size_t missing_blank = cg[i].members.size();
                score_t blank_score = score_t(missing_blank);

                std::size_t extra_all = all.size() - cg[i].members.size();
                std::size_t missing_all = 0;
                score_t all_score = score_t(extra_all) * discard_weight;
        
                score_t max_distance = blank_score; //std::min(blank_score, all_score);
                score_t min_distance = max_distance;
        
                for(std::list<members_t>::iterator j = topo.begin(); j != topo.end(); ++j) {
                    temp.clear();
                    std::set_difference(cg[i].members.begin(), cg[i].members.end(), j->begin(), j->end(), std::back_inserter(temp));
                    std::size_t extra = temp.size();
                    temp.clear();
                    std::set_difference(j->begin(), j->end(), cg[i].members.begin(), cg[i].members.end(), std::back_inserter(temp));
                    std::size_t missing = temp.size();
            
                    score_t score = score_t(missing) + score_t(extra) * discard_weight;
                    min_distance = std::min(score, min_distance);
                }
        
                out << cg[i].weight << "\t" << min_distance << "\t" << max_distance << std::endl;
                std::cout << "." << std::flush;
            }
        }
        {
            std::cout << "computing manufactured groups";
            fs::ofstream out(st->branch_path() / ("mfg-groups-" + st->leaf()));
    
            std::set<members_t> filtered;
            for(unsigned int i = 0; i < cg.size(); ++i) {
                filtered.insert(cg[i].members);
            }

            for(std::list<members_t>::iterator j = topo.begin(); j != topo.end(); ++j) {
                if(filtered.find(*j) == filtered.end()) {
                    std::set<std::string> names;
                    for(members_t::const_iterator i = j->begin(); i != j->end(); ++i) {
                        names.insert(email_id.by<bit>().equal_range(*i).first->second);
                    }
                    std::copy(names.begin(), names.end(), std::ostream_iterator<std::string>(out, " "));
                    out << std::endl;
                }
            }
        }
    }
    

    std::cout << std::endl;
    return 0;
}

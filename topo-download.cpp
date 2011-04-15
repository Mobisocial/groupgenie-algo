#include <cstdlib>
#include <iostream>
#include <iomanip>
#include <sstream>
#include <boost/bind.hpp>
#include <boost/asio.hpp>
#include <boost/asio/ssl.hpp>
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
namespace asio = boost::asio;
namespace gr = boost; //weird but they didnt subspace it

boost::regex re_crlf("\r\n");
template <typename StreamType>
std::string asio_read_until_crlf(StreamType& s) {
    asio::streambuf buf;
    asio::read_until(s, buf, re_crlf);
    asio::streambuf::const_buffers_type bufs = buf.data();
    return std::string(
        asio::buffers_begin(buf.data()),
        asio::buffers_end(buf.data()));
}

boost::regex re_byte_buffer("\\{(\\d+)\\}");

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

typedef gr::adjacency_list<gr::setS, gr::setS, gr::undirectedS, group, relation> connectedness_graph;
    
typedef std::set<std::string> message_id_set;
typedef std::map<members_t, connectedness_graph::vertex_descriptor> initial_group_partition_map;

struct log_handler {
    void operator() (const std::string& resp, const std::list<std::string>& args) const {
        std::cout << resp;
        std::copy(args.begin(), args.end(), std::ostream_iterator<std::string>(std::cout, "\n"));
        std::cout << std::flush;
    }
};

boost::regex re_terms("([^:]+): ([^\r\n]+[\r\n]+(?:\\s+[^\r\n]+[\r\n]+)*)");
boost::regex re_email("(?:(?:\"([^\"]+)\"\\s+<)|(?:(?:^|,)\\s*([^<,@\"]+)\\s+<))?(\\b[A-Z0-9._%+-]+@[A-Z0-9.-]+\\.[A-Z]{2,4}\\b)", boost::regex::icase);
struct header_handler {
    header_handler(email_id_bimap& _email_id, connectedness_graph& _cg, entity_map& _em, message_id_set& _message_id, initial_group_partition_map& _igpm) 
        : email_id(_email_id)
        , cg(_cg) 
        , em(_em)
        , message_id(_message_id)
        , igpm(_igpm)
    {   
    }
    void operator() (const std::string& resp, const std::list<std::string>& args) const {
        //TODO: find old entry and just bump it!!!!

        //this updates the index of our message data as we read it back
        if(args.empty())
            throw std::runtime_error("no header returned!");
            
        members_t g;
        for(boost::sregex_iterator i(args.front().begin(), args.front().end(), re_terms), e; i != e; ++i) {
            const boost::smatch& what = *i;
            std::string field = what[1].str();
            if(boost::algorithm::iequals(field, "Message-ID")) {
                std::string id = what[2].str();
                boost::algorithm::trim(id);
                std::pair<message_id_set::iterator, bool> result = message_id.insert(id);
                //skip this duplicate message
                if(!result.second)
                    return;
                
            } else if(boost::algorithm::iequals(field, "From") || boost::algorithm::iequals(field, "To") || boost::algorithm::iequals(field, "Cc")) {
                std::string data = what[2].str();
                boost::replace_all(data, "\n", "");
                boost::replace_all(data, "\r", "");
                for(boost::sregex_iterator j(data.begin(), data.end(), re_email), e; j != e; ++j) {
                    std::string name = (*j)[1].str();
                    if(name.empty())
                        name = (*j)[2].str();
                    std::string email_address = (*j)[3].str();
                    boost::algorithm::to_lower(email_address);
                    boost::algorithm::trim(name);
                    std::pair<email_id_bimap::map_by<email>::iterator, bool> result = email_id.by<email>().insert(
                        email_id_bimap::map_by<email>::value_type(email_address, email_id.size()));
                    if(result.second)
                        std::cout << "@" << std::flush;
                    if(!name.empty() && boost::to_lower_copy(name) != email_address)
                        em[email_address].insert(name);
                    g.insert(result.first->second);
                }
            }
        }
        if(g.empty()) {
            return;
        }
        
        initial_group_partition_map::iterator r = igpm.find(g);
        if(r == igpm.end()) {
            connectedness_graph::vertex_descriptor node = gr::add_vertex(cg);
            cg[node].members = g;
            cg[node].weight = 1;
            igpm.insert(r, std::make_pair(g, node));
        } else {
            connectedness_graph::vertex_descriptor node = r->second;
            cg[node].weight++;
        }
        std::cout << "." << std::flush;
    }
    email_id_bimap& email_id;
    entity_map& em;
    connectedness_graph& cg;
    message_id_set& message_id;      
    initial_group_partition_map& igpm;  
};

int main(int argc, char* argv[])
{
    std::string server;
    std::string port;
    std::string user;
    std::string folder;
    std::string password;
    std::vector<fs::path> from;
    std::vector<fs::path> entity;
    fs::path to;
    
    //[Gmail]/Sent Mail
    po::options_description general_options("General");
    general_options.add_options()
        ("help", "list options");
    po::options_description file_options("Load");
    file_options.add_options()
        ("save-raw", po::value<fs::path>(&to), "path to save the data (after download phase)");
    po::options_description download_options("Download");
    download_options.add_options()
        ("server", po::value<std::string>(&server), "imap server dns/ip")
        ("port", po::value<std::string>(&port)->default_value("993"), "imap port")
        ("folder", po::value<std::string>(&folder)->default_value("Sent"), "imap folder")
        ("user", po::value<std::string>(&user), "imap username")
        ("password", po::value<std::string>(&password), "imap password (will ask if not specified)");
    po::options_description run_options("Run");
    
    po::options_description all_options("Email Topology Options");
    all_options
        .add(general_options)
        .add(file_options)
        .add(download_options);

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
    if(!vm.count("password")) {
        password = getpass("Password: ");
    }
    if(server.empty()) {
        std::cout << "missing server for download" << std::endl;
        return 1;
    }
    if(user.empty()) {
        std::cout << "missing user for download" << std::endl;
        return 1;
    }
    if(password.empty()) {
        std::cout << "missing user for download" << std::endl;
        return 1;
    }
    //this is our network block, downloads all messages headers
    try
    {
        std::cout << "downloading " << folder << " from " << server << std::endl;
        //use to dedupe if there are dupes
        message_id_set message_id;        

        typedef boost::function<void (const std::string&, const std::list<std::string>& args)> untagged_handler;
        std::string pending_tag = "* ";
        std::list<std::string> pending_command;
        pending_command.push_back("WAIT_FOR_ACK");
        untagged_handler pending_handler;
        unsigned int command_id = 0;

        //The sequence of imap commands we want to run
        std::list<std::list<std::string> > commands;
        std::list<untagged_handler> handlers;

        handlers.push_back(log_handler());
        commands.push_back(std::list<std::string>());
        std::ostringstream login_os;
        login_os << "LOGIN \"" << user << "\" {" << password.size() << "}";
        commands.back().push_back(login_os.str()); 
        commands.back().push_back(password); 

        handlers.push_back(log_handler());
        commands.push_back(std::list<std::string>());
        commands.back().push_back("LIST \"\" *"); 

        handlers.push_back(log_handler());
        commands.push_back(std::list<std::string>());
        commands.back().push_back("SELECT \"" + folder + "\""); 

        handlers.push_back(header_handler(email_id, cg, em, message_id, igpm));
        commands.push_back(std::list<std::string>());
        commands.back().push_back("FETCH 1:* (BODY.PEEK[HEADER.FIELDS (MESSAGE-ID FROM TO CC)])");
        commands.push_back(std::list<std::string>());

        handlers.push_back(log_handler());
        commands.back().push_back("LOGOUT");
    
        //open ssl connection to the server, no cert checking
        asio::io_service io_service;
        asio::ip::tcp::resolver resolver(io_service);
        asio::ip::tcp::resolver::query query(server, port);
        asio::ip::tcp::resolver::iterator iterator = resolver.resolve(query);
        asio::ssl::context context(io_service, asio::ssl::context::sslv23);
        context.set_verify_mode(asio::ssl::context::verify_none);
        asio::ssl::stream<asio::ip::tcp::socket> socket(io_service, context);
        socket.lowest_layer().connect(*iterator);
        socket.handshake(asio::ssl::stream_base::client);
        asio::streambuf buf;

        while(true) {
            //read the next line of data
            std::size_t line_length = asio::read_until(socket, buf, re_crlf);
            std::string line(
                asio::buffers_begin(buf.data()),
                asio::buffers_begin(buf.data()) + line_length);
            buf.consume(line_length);
            boost::match_results<std::string::iterator> what;
            std::size_t initial = 0;
            std::list<std::string> args;
            //the line may be split into segments with chunks of data embedded, this is the case
            //for bodies or message header blocks that are returned, we only handle this case if it
            //comes in untagged response (*) not a continuation (+), i think that is normal
            while(regex_search(line.begin() + initial, line.end(), what, re_byte_buffer, boost::match_default)) {
                unsigned int bytes = boost::lexical_cast<unsigned int>(what[1].str());
                if(buf.size() < bytes)
                    asio::read(socket, buf, asio::transfer_at_least(bytes - buf.size()));
                args.push_back(
                    std::string(
                        asio::buffers_begin(buf.data()),
                        asio::buffers_begin(buf.data()) + bytes));
                buf.consume(bytes);
                line.resize(what[1].second - line.begin());
                initial = line.size();
                //read the next line of data
                line_length = asio::read_until(socket, buf, re_crlf);
                line += std::string(
                    asio::buffers_begin(buf.data()),
                    asio::buffers_begin(buf.data()) + line_length);
                buf.consume(line_length);
            }
            if(boost::algorithm::starts_with(line, pending_tag)) {
                //if the command is being completed, then we will go here, bail out if the response wasn't ok
                if(!boost::algorithm::starts_with(line, pending_tag + "OK")) {
                    std::cout << line;
                    throw std::runtime_error("command failed");
                }
                //pull the next command off the list
                pending_tag = "A" + boost::lexical_cast<std::string>(command_id++) + " ";
                if(commands.size() == 0)
                    break;
                pending_handler = handlers.front();
                pending_command = commands.front();
                commands.pop_front();
                handlers.pop_front();

                //send the command along with any data arguments
                std::cout << pending_tag << pending_command.front() << std::endl;
                asio::write(socket, asio::buffer(pending_tag.data(), pending_tag.size()));
                for(std::list<std::string>::iterator i = pending_command.begin(); i != pending_command.end(); ++i) {
                    if(i != pending_command.begin()) {
                        //print the continuation response
                        std::size_t line_length = asio::read_until(socket, buf, re_crlf);
                        std::string line(
                            asio::buffers_begin(buf.data()),
                            asio::buffers_begin(buf.data()) + line_length);
                        buf.consume(line_length);
                        std::cout << line << std::flush;
                        if(!boost::algorithm::starts_with(line, "+ ")) {
                            throw std::runtime_error("bad response when writing extra data");
                        }
                    } else {
                        //print it out as well (but not the args)
                        std::cout << *i << std::endl;
                    }
                    asio::write(socket, asio::buffer(i->data(), i->size()));
                    asio::write(socket, asio::buffer("\r\n", 2));
                }
            } else if(boost::algorithm::starts_with(line, "* ")) {
                //if there is a registered handler, dispatch to it
                if(pending_handler)
                    pending_handler(line, args);
            } else {
                throw std::runtime_error("unrecognized response");
            }
        }
    }
    catch (std::exception& e) {
        std::cout << "Exception: " << e.what() << std::endl;
        return 1;
    }
    std::cout << std::endl;
    
    if(to.empty()) {
        std::cout << "Missing output file for save" << std::endl;
        return 1;
    }
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

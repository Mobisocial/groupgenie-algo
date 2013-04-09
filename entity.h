
boost::regex re_chunk("\\b[\\w\\d-]+\\b");
bool entities_match(const std::set<std::string>& a, const std::set<std::string>& b) {
    for(std::set<std::string>::const_iterator i = a.begin(); i != a.end(); ++i) {
        for(std::set<std::string>::const_iterator j = b.begin(); j != b.end(); ++j) {
            std::string one = *i;
            std::string two = *j;
            boost::algorithm::to_lower(one);
            boost::algorithm::to_lower(two);
            if(one == two)
                return true;

            boost::sregex_iterator e;
            
            std::list<std::string> one_parts;
            for(boost::sregex_iterator i(one.begin(), one.end(), re_chunk), e; i != e; ++i) {
                one_parts.push_back((*i)[0]);
            }
            std::list<std::string> two_parts;
            for(boost::sregex_iterator i(two.begin(), two.end(), re_chunk), e; i != e; ++i) {
                two_parts.push_back((*i)[0]);
            }
            
            if(one_parts.size() < two_parts.size())
                one_parts.swap(two_parts);
            
            std::size_t num = one_parts.size();
            std::vector<std::list<std::string>::iterator > matched;
            for(std::list<std::string>::iterator i = one_parts.begin(); i != one_parts.end(); ++i) {
                for(std::list<std::string>::iterator j = two_parts.begin(); j != two_parts.end(); ++j) {
                    if (*i == *j) {
                        matched.push_back(i);
                        two_parts.erase(j);
                        break;
                    }
                }
            }
            for(std::vector<std::list<std::string>::iterator>::iterator i = matched.begin(); i != matched.end(); ++i) {
                one_parts.erase(*i);
            }
            matched.clear();
            //atleast one must fully match
            if(one_parts.size() == num)
                continue;
            for(std::list<std::string>::iterator i = one_parts.begin(); i != one_parts.end(); ++i) {
                for(std::list<std::string>::iterator j = two_parts.begin(); j != two_parts.end(); ++j) {
                    if(i->empty() || j->empty())
                        continue;
                    if ((*i)[0] == (*j)[0] && (i->size() == 1 || j->size() == 1)) {
                        matched.push_back(i);
                        two_parts.erase(j);
                        break;
                    }
                }
            }
            for(std::vector<std::list<std::string>::iterator>::iterator i = matched.begin(); i != matched.end(); ++i) {
                one_parts.erase(*i);
            }
            if(one_parts.size() == 0) 
                return true;
        }
    }
    return false;
}
typedef std::map<std::string, std::set<std::string> > entity_map;
struct email  {};
struct bit    {};

typedef boost::bimaps::bimap <
    boost::bimaps::set_of<boost::bimaps::tagged< std::string, email > >,
    boost::bimaps::multiset_of<boost::bimaps::tagged< unsigned int, bit > >,
    boost::bimaps::set_of_relation<>
> email_id_bimap;

void resolve_entities(entity_map& em, email_id_bimap& email_id) {
    //entity res
    for(entity_map::iterator i = em.begin(); i != em.end(); ++i) {
        entity_map::iterator j = i;
        for(++j; j != em.end(); ++j) {
            if(entities_match(i->second, j->second)) {
                try {
                    std::cout << i->first << " == " << j->first << std::endl;
                    email_id.by<email>().erase(j->first);
                    email_id.by<email>().insert(email_id_bimap::map_by<email>::value_type(j->first, email_id.by<email>().at(i->first)));
                } catch (std::exception& e) {
                    std::cout << "failed looking up " << j->first << ": " << e.what() << std::endl;
                }
            }
        }
    }
}
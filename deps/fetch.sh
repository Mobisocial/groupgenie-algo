#!/bin/bash
if [ ! -f boost_1_45_0.tar.bz2 ]; then
    curl -L http://downloads.sourceforge.net/project/boost/boost/1.45.0/boost_1_45_0.tar.bz2 > boost_1_45_0.tar.bz2 || rm boost_1_45_0.tar.bz2
fi
if [ ! -d boost_1_45_0 ]; then
    tar -xjvf boost_1_45_0.tar.bz2
    pushd boost_1_45_0/
    ./bootstrap.sh
    ./bjam link=static variant=release  address-model=32_64 architecture=combined --with-system --with-filesystem --with-graph --with-regex --with-program_options
    popd
fi

unzip json_spirit_v4.03.zip

cmake_minimum_required(VERSION 3.24)
project(btree)

set(CMAKE_CXX_STANDARD 17)

add_executable(btree main.cpp)
set(CMAKE_CXX_FLAGS "-Ofast -g3 -march=native")
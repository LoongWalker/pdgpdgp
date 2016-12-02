
add_library(DatalogDynCIPDG MODULE dyncipdg.cpp ControlDependence.cpp 
  ../utils/ValToStrDB.cpp ../utils/utils.cpp )

find_library(Z3_LIB z3)
message(STATUS ${Z3_LIB})

target_link_libraries(DatalogDynCIPDG ${Z3_LIB})


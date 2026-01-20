cmake_minimum_required(VERSION 3.20)
project(MyProj LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

# ---- Threading support ----
find_package(Threads REQUIRED)

# ---- Z3 build options (must be set BEFORE add_subdirectory) ----
# Z3_BUILD_LIBZ3_SHARED: build libz3 as shared (ON) or static (OFF).
set(Z3_BUILD_LIBZ3_SHARED OFF CACHE BOOL "Build Z3 as a shared library" FORCE)

# Optional: avoid building Z3 examples (keeps builds smaller)
set(Z3_BUILD_EXAMPLES ON CACHE BOOL "" FORCE)
set(Z3_BUILD_TEST_EXECUTABLES OFF CACHE BOOL "" FORCE)

# ---- Add Z3 from submodule ----
add_subdirectory(external/z3)

# ---- main target ----
add_executable(myproj src/main.cpp)
target_link_libraries(myproj PRIVATE libz3)

# ---- test target ----
enable_testing()
add_executable(myproj_tests src/test.cpp)
target_link_libraries(myproj_tests PRIVATE libz3 Threads::Threads)
add_test( NAME myproj_basic_tests COMMAND myproj_tests)

add_executable(example_groups src/example_groups.cpp)
target_link_libraries(example_groups PRIVATE libz3 Threads::Threads)
add_test( NAME example_groups_tests COMMAND example_groups)

# Add Z3 include directories
target_include_directories(myproj PRIVATE 
    ${CMAKE_SOURCE_DIR}/external/z3/src/api
    ${CMAKE_SOURCE_DIR}/external/z3/src/api/c++)

target_include_directories(myproj_tests PRIVATE 
    ${CMAKE_SOURCE_DIR}/external/z3/src/api
    ${CMAKE_SOURCE_DIR}/external/z3/src/api/c++)

target_include_directories(example_groups PRIVATE 
    ${CMAKE_SOURCE_DIR}/external/z3/src/api
    ${CMAKE_SOURCE_DIR}/external/z3/src/api/c++)

# If you build Z3 as a DLL (Z3_BUILD_LIBZ3_SHARED=ON),
# copy the DLL next to your exe so it runs from VS Code build folder.
add_custom_command(TARGET myproj POST_BUILD
  COMMAND ${CMAKE_COMMAND} -E copy_if_different
          $<TARGET_FILE:libz3>
          $<TARGET_FILE_DIR:myproj>
)

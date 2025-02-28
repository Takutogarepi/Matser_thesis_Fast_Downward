# Usage:
#         cmake -S src -B builds/release
#         cmake --build builds/release
# The first call caches settings in the build directory and reads
# them from the cache on subsequent builds. If you want to change the
# settings of some options, do _not_ change the CMakeLists.txt files.
# Instead, create a new build directory, pass -DMY_OPTION=my_value to
# cmake. Alternatively, you can use a cmake GUI like ccmake to edit
# the cache.
#
# Two build targets are defined:
#
# * release (default)
#      -O3 optimisation, debugging symbols, assertions inactive
# * debug
#      -O3 optimisation, full debugging information, assertions active
#
# In all build targets, we overwrite the default configuration to
# include "-g", allow cross compilation and switch to pedantic error
# reporting.
#
# You can change the build target, by adding the parameter
#   -DCMAKE_BUILD_TYPE=type
# to the cmake call.

cmake_minimum_required(VERSION 3.16)

project(fast-downward
    DESCRIPTION "Fast Downward is a domain-independent classical planning system."
    HOMEPAGE_URL https://www.fast-downward.org/)

set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/bin)

# Add planner components.

# Copy the translator into the output directory.
add_custom_target(translate ALL)
add_custom_command(TARGET translate POST_BUILD
    COMMAND ${CMAKE_COMMAND} -E copy_directory
        ${CMAKE_CURRENT_SOURCE_DIR}/translate
        ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/${CMAKE_CFG_INTDIR}/translate
    COMMENT "Copying translator module into output directory")

# Copy the preprocess binaries to output directory. I added this part
add_custom_target(copy_preprocess ALL)
add_custom_command(TARGET copy_preprocess POST_BUILD
    COMMAND ${CMAKE_COMMAND} -E copy
        /infai/togare0000/downward-projects/Matser_thesis_Fast_Downward/h2-preprocessor/builds/release32/bin/preprocess
        ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/${CMAKE_CFG_INTDIR}/
    COMMENT "Copying h2-preprocess binaries into output directory")

# Add search component as a subproject.
add_subdirectory(search)

cmake_minimum_required(VERSION 3.25.2)
project(native)
add_executable(${PROJECT_NAME} main.cpp)
#add_library(${PROJECT_NAME} SHARED main.cpp)
install(TARGETS ${PROJECT_NAME} DESTINATION bin)

find_package(SEAL 4.1 REQUIRED)
target_link_libraries(${PROJECT_NAME} SEAL::seal)

set(Boost_USE_STATIC_LIBS OFF) 
set(Boost_USE_MULTITHREADED ON)  
set(Boost_USE_STATIC_RUNTIME OFF) 
find_package(Boost 1.82.0) 

if(Boost_FOUND)
    include_directories(${Boost_INCLUDE_DIRS}) 
    target_link_libraries(${PROJECT_NAME} ${Boost_LIBRARIES})
endif()


set(JAVA_INCLUDE_PATH "/Downloads/jdk-21.0.2.jdk/Contents/Home/include")
set(JAVA_INCLUDE_PATH2 "/Downloads/jdk-21.0.2.jdk/Contents/Home/include/darwin")
set(JAVA_AWT_INCLUDE_PATH "/Downloads/jdk-21.0.2.jdk/Contents/Home/include")
message("JAVA_INCLUDE_PATH = ${JAVA_INCLUDE_PATH}")
find_package(JNI REQUIRED)
if (JNI_FOUND)
    message (STATUS "JNI_INCLUDE_DIRS=${JNI_INCLUDE_DIRS}")
    message (STATUS "JNI_LIBRARIES=${JNI_LIBRARIES}")
endif()
target_include_directories(${PROJECT_NAME} PUBLIC ${JNI_INCLUDE_DIRS})



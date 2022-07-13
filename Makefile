CXXFLAGS += -Wall  -Wextra
# -Werror

all: libterm.so libvector.so

libvector.so: myvector.cpp
	g++ myvector.cpp -c -fPIC -o libvector.o -std=c++17 -DRAM_DOMAIN_SIZE=64 ${CXXFLAGS}
	g++ -shared -o libvector.so libvector.o  -std=c++17

libterm.so: libterm.cpp
	g++ libterm.cpp -c -fPIC -o libterm.o -std=c++17 -DRAM_DOMAIN_SIZE=64 ${CXXFLAGS}
	g++ -shared -o libterm.so libterm.o  -std=c++17


libvector.so: myvector.cpp
	g++ myvector.cpp -c -fPIC -o libvector.o -std=c++17 -DRAM_DOMAIN_SIZE=64
	g++ -shared -o libvector.so libvector.o  -std=c++17
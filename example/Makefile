all:
	gcc -o count `pkg-config --cflags --libs glib-2.0` count.c `pkg-config --libs glib-2.0`
	gcc -o stemmer -I../include stemmer.c ../lib/libstemmer.o 

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "../include/libstemmer.h"

int 
main () 
{
	struct sb_stemmer * stemmer ;
	char buf[1024] ;

	stemmer = sb_stemmer_new("english", 0x0) ;

	while (scanf("%s", buf) != EOF) {
		const char * s ;
		s = sb_stemmer_stem(stemmer, buf, strlen(buf)) ;
		printf("%s\n", s) ;
	} 

	sb_stemmer_delete(stemmer) ;
}

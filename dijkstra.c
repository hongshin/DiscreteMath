#include <stdio.h>
#include <stdlib.h>
#include "graph.h"



/*TODO: you can add functions as you want */

int
main (int argc, char ** args)
{
	graph_t * g ; 

	g = graph_read_stdin() ;

	if (argc != 3) { 
		fprintf(stderr, "Too few arguments\n") ;
		return 1 ;
	}

	int start, end ;

	start = atoi(args[1]) ;
	end = atoi(args[2]) ;

	if (start < 0 || g->n_vertices <= start ||
		end < 0 || g->n_vertices <= end) {
		fprintf(stderr, "Wrong arguments\n") ;
		return 1 ;
	}


	/* TODO: implement here */

	graph_free(g) ;
	return 0 ;
}

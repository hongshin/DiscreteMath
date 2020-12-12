#include <stdio.h>
#include <stdlib.h>
#include "graph.h"



/*TODO: you can add functions as you want */

int
main ()
{
	graph_t * g ; 

	g = graph_read_stdin() ;

	/* TODO: implement here */

	graph_free(g) ;
	return 0 ;
}

#include <stdio.h>
#include <stdlib.h>
#include "graph.h"

int
main ()
{
	graph_t * g ; 

	g = graph_read_stdin() ;
	graph_print_stdout(g) ;

	graph_remove_edge(g, 2, 3, 2) ;
	graph_remove_edge(g, 2, 3, 1) ;
	graph_remove_edge(g, 1, 1, 1) ;
	graph_remove_edge(g, 3, 1, 2) ;

	printf("\n") ;

	graph_print_stdout(g) ;

	graph_free(g) ;
}

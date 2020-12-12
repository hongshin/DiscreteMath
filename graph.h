typedef 
	struct{
		int n_vertices ;
		int ** m ;
		int *** w ;
	} 
	graph_t ;

graph_t *
graph_create (int n_vertices) ;

void
graph_free (graph_t * g) ;

graph_t * 
graph_read_stdin () ;

void
graph_add_edge (graph_t * g, int init, int term, int weight) ;

int 
graph_remove_edge (graph_t * g, int init, int term, int weight) ;


void
graph_print_stdout (graph_t * g) ;

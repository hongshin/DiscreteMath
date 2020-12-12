#include <stdio.h>
#include <stdlib.h>
#include "graph.h"

graph_t *
graph_create (int n_vertices)
{
	graph_t * r ;

	r = (graph_t *) malloc(sizeof(graph_t)) ;

	r->n_vertices = n_vertices ;
	r->m = (int **) calloc(n_vertices, sizeof(int *)) ;
	r->w = (int ***) calloc(n_vertices, sizeof(int **)) ;

	for (int i = 0 ; i < n_vertices ; i++) {
		r->m[i] = (int *) calloc(n_vertices, sizeof(int)) ;
		r->w[i] = (int **) calloc(n_vertices, sizeof(int *)) ;

		for (int j = 0 ; j < n_vertices ; j++) {
			r->m[i][j] = 0 ;
			r->w[i][j] = 0x0 ;
		}
	}
	return r ;
}

void
graph_free (graph_t * g)
{
	for (int i = 0 ; i < g->n_vertices ; i++) {
		for (int j = 0 ; j < g->n_vertices ; j++) {
			if (g->w[i][j] != 0x0)
				free(g->w[i][j]) ;
		}
		free(g->w[i]) ;
		free(g->m[i]) ;
	}
	free(g->w) ;
	free(g->m) ;
}

graph_t * 
graph_read_stdin () {
	int n_vertices, n_edges ;

	scanf("%d", &n_vertices) ;

	if (n_vertices < 0)
		return 0x0 ;

	graph_t * g ;
	if ((g = graph_create(n_vertices)) == 0x0)
		return 0x0 ;
	
	scanf("%d", &n_edges) ;
	for (int i = 0 ; i < n_edges ; i++) {
		int init, term, weight ;

		if (scanf("%d %d %d", &init, &term, &weight) != 3) 
			goto read_err ;
		if (init < 0 || n_vertices <= init)
			goto read_err ;
		if (term < 0 || n_vertices <= term)
			goto read_err ; 
		if (weight <= 0)
			goto read_err ;

		graph_add_edge(g, init, term, weight) ;
	}
	return g ;


read_err:
	graph_free(g) ;
	return 0x0 ;

}

void
graph_add_edge (graph_t * g, int init, int term, int weight)
{
	g->m[init][term] += 1 ;
	g->w[init][term] = (int *) realloc(g->w[init][term], g->m[init][term] * sizeof(int)) ;
	g->w[init][term][g->m[init][term] - 1] = weight ;
	if (init == term)
		return ;

	g->m[term][init] += 1 ;
	g->w[term][init] = (int *) realloc(g->w[term][init], g->m[term][init] * sizeof(int)) ;
	g->w[term][init][g->m[term][init] - 1] = weight ;
}

int 
graph_remove_edge (graph_t * g, int init, int term, int weight)
{
	int i ;

	if (g->m[init][term] == 0)
		return 1 ;

	for (i = 0 ; g->w[init][term][i] != weight ; i++) {
		if (i == g->m[init][term] - 1)
			return 1 ;
	}
	for (i = i + 1 ; i < g->m[init][term] ; i++) {
		g->w[init][term][i - 1] = g->w[init][term][i] ;
	}
	g->m[init][term] -= 1 ;

	if (g->m[init][term] > 0) {
		g->w[init][term] = (int *) realloc(g->w[init][term], g->m[init][term] * sizeof(int)) ;
	}
	else {
		free(g->w[init][term]) ;
		g->w[init][term] = 0x0 ;
	}

	if (init == term)
		return 0 ;

	for (i = 0 ; g->w[term][init][i] != weight ; i++) {
		if (i == g->m[term][init] - 1)
			return 1 ;
	}
	for (i = i + 1 ; i < g->m[term][init] ; i++) {
		g->w[term][init][i - 1] = g->w[term][init][i] ;
	}
	g->m[term][init] -= 1 ;
	if (g->m[term][init] > 0) {
		g->w[term][init] = (int *) realloc(g->w[term][init], g->m[term][init] * sizeof(int)) ;
	}
	else {
		free(g->w[term][init]) ;
		g->w[term][init] = 0x0 ;
	}
	return 0 ;
}


void
graph_print_stdout (graph_t * g)
{
	for (int i = 0 ; i < g->n_vertices ; i++) {
		for (int j = i ; j < g->n_vertices ; j++) {
			if (g->m[i][j] > 0) {
				printf("%d <-> %d : ", i, j) ;
				for (int k = 0 ; k < g->m[i][j] ; k++) {
					printf("%d ", g->w[i][j][k]) ;
				}
				printf("\n") ;
			}
		}
	}
}

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "intset.h"

intset *
intset_alloc (int * univ, size_t n_univ) 
{	
	intset * s = (intset *) malloc(sizeof(intset)) ;

	s->univ = univ ;
	s->n_univ = n_univ ;

	size_t bitvect_len = n_univ / 8 + ((n_univ % 8) ? 1 : 0) ;

	s->bitvect = (unsigned char *) malloc(bitvect_len) ;
	memset(s->bitvect, 0, bitvect_len) ;
	s->n_elems = 0 ;
	return s ;
}

intset * 
intset_clone (intset * orig) 
{
	if (orig == 0x0)
		return 0x0 ;

	intset * s ;
	s = intset_alloc(orig->univ, orig->n_univ) ;
	memcpy(s->bitvect, orig->bitvect, orig->n_univ / 8 + (orig->n_univ % 8) ? 1 : 0) ;
	s->n_elems = orig->n_elems ;

	return s ;
}

void
intset_print (FILE * fp, intset * s)
{
	fprintf(fp, "{") ;
	char * delim = "" ;
	for (int i = 0 ; i < s->n_univ ; i++) {
		if (intset_contains(s, s->univ[i])) {
			fprintf(fp, "%s%d", delim, s->univ[i]) ;
			delim = ", " ;
		}
	}
	fprintf(fp, "}") ;
}

void
intset_free (intset * s) 
{
	free(s->bitvect) ;
	free(s) ;
}

int
intset_size (intset * s) 
/*
 * returns the number of elements contained in s.
 */
{
	/* TODO*/
}

int
intset_add (intset * s, int e) 
/*
 * insert a new integer value e to s.
 * return 0 if succeeded. return 1 if it fails.
 * 
 */
{
	/* TODO*/
}

int
intset_remove (intset * s, int e) 
/*
 * remomve e from s.
 * return 0 if succeeded. return 1 if failed.
 *
 */
{
	/* TODO*/
}


int
intset_contains (intset * s, int e) 
/*
 * return 1 if e is contained in s. return 0 otherwise.
 */
{
	/* TODO*/
}


int
intset_equals (intset *s1, intset *s2) 
/*
 * return 1 if two sets s1 and s2 are equivalent.
 * return 0 otherwise.
 *
 * two sets are not equivalent if their univ fields are not the same.
 */
{
	/* TODO*/
}


intset *
intset_union (intset *s1, intset *s2) 
/*
 * return a new intset object that contains the result of
 * the union of s1 and s2.
 *
 * return NULL if the operation fails.
 * union operation fails if their univ fields are not the same.
 */
{
	/* TODO*/
}


intset *
intset_intersection (intset *s1, intset *s2) 
/*
 * return a new intset object that contains the result of
 * the intersection of s1 and s2.
 *
 * return NULL if the operation fails.
 * intersection operation fails if their univ fields are not the same.
 */
{
	/* TODO*/
}


intset *
intset_difference (intset *s1, intset *s2) 
/*
 * return a new intset object that contains the result of
 * the set difference of s1 and s2 (i.e., s1 \ s2).
 *
 * return NULL if the operation fails.
 * set difference operation fails if their univ fields are not the same.
 */
{
	/* TODO*/
}


intset **
intset_subsets (intset * s, size_t k , size_t * n_subsets) 
/*
 * return a new intset array that contains all distinct subsets
 * of s having k elements. The size of the result array must be
 * given to n_subsets.
 * 
 * this operation must be implemented with a recursion.
 *
 * return NULL if the operation fails.
 */
{
	/* TODO*/
}


intset ** 
intset_powerset (intset * s, size_t * n_subsets) 
/*
 * return a new intset array that contains all distinct subsets
 * of s having. The size of the result array must be given to
 * n_subsets.
 * 
 * this operation must be implemented with a recursion.
 *
 * return NULL if the operation fails.
*/
{
	/* TODO*/
}

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

#include "intset.h"

void
test1 ()
{
	int univ[4] = {1, 2, 3, 4} ;

	intset * s = intset_alloc(univ, 4) ;

	intset_add(s, 1) ;
	intset_add(s, 2) ;
	intset_add(s, 3) ;
	intset_add(s, 4) ;
	intset_remove(s, 2) ;

	assert(intset_size(s) == 3) ;
	assert(intset_contains(s, 4) == 1) ;
	assert(intset_contains(s, 2) == 0) ;

	intset_print(stderr, s) ; fprintf(stderr, "\n") ;

	size_t n_ps ;
	intset ** ps = intset_powerset(s, &n_ps) ;

	assert(n_ps == 8) ;

	for (int i = 0 ; i < n_ps ; i++) {
		intset_print(stderr, ps[i]) ; fprintf(stderr, "\n") ;
		intset_free(ps[i]) ;
	}
	free(ps) ;

	free(s) ;
}

void
test2 ()
{
	int univ[4] = {1, 2, 3, 4} ;

	intset * s1 = intset_alloc(univ, 4) ;
	intset * s2 = intset_alloc(univ, 4) ;
	intset * s3 = 0x0 ;

	intset_add(s1, 1) ;
	intset_add(s1, 2) ;

	intset_add(s2, 2) ;
	intset_add(s2, 3) ;

	s3 = intset_union(s1, s2) ;

	assert(intset_size(s3) == 3) ;
	assert(intset_contains(s3, 1) == 1) ;
	assert(intset_contains(s3, 2) == 1) ;
	assert(intset_contains(s3, 3) == 1) ;
	assert(intset_contains(s3, 4) == 0) ;
	
	intset_free(s1) ;
	intset_free(s2) ;
	intset_free(s3) ;
}


int
main ()
{
	test1() ;
	test2() ;

	printf("Pass\n") ;
}

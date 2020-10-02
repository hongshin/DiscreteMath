struct _intset {
	size_t n_elems ;
	int * elems ;
} ;

typedef struct _intset intset ;


intset *
intset_alloc () ;

intset * 
intset_clone (intset * s) ;

void
intset_free (intset * s) ;

void
intset_print (FILE *fp, intset *s) ;


int
intset_size (intset * s) ;

int
intset_add (intset * s, int e) ;

int
intset_remove (intset * s, int e) ;

int
intset_contains (intset * s, int e) ;

int
intset_equals (intset *s1, intset *s2) ;

intset *
intset_union (intset *s1, intset *s2) ;

intset *
intset_intersection (intset *s1, intset *s2) ;

intset *
intset_difference (intset *s1, intset *s2) ;

intset **
intset_subsets (intset * s, size_t k , size_t * n_subsets) ;

intset ** 
intset_powerset (intset * s, size_t * n_subsets) ;

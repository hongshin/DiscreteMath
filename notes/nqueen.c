#include <stdio.h>

int 
min(int a, int b)
{
	if (a > b)
		return b ;
	return a ;
}

int
main ()
{
	int i, j, k ;

	for (i = 1 ; i <= 8 ; i++)
		for (j = 1 ; j <= 8 ; j++)
			printf("(declare-const p%d%d Bool)\n", i, j) ;

	// Q1
	printf("; Q1\n") ;
	printf("(assert (and ") ;
	for (i = 1 ; i <= 8 ; i++) {
		printf("(or ") ;
		for (j = 1 ; j <= 8 ; j++) 
			printf("p%d%d ", i, j) ;
		printf(")") ;
	}
	printf("))\n") ;

	// Q2
	printf("; Q2\n") ;
	printf("(assert ") ;
	printf("(and ") ;
	for (i = 1 ; i <= 8 ; i++) {
		printf("(and ") ;
		for (j = 1 ; j <= 7 ; j++) {
			printf("(and ") ;
			for (k = j + 1 ; k <= 8 ; k++) {
				printf("(not (and p%d%d p%d%d))", i, j, i, k) ;
			}
			printf(")") ;
		}
		printf(") ") ;
	}
	printf("))\n") ;

	// Q3
	printf("; Q3\n") ;
	printf("(assert ") ;
	printf("(and ") ;
	for (i = 1 ; i <= 8 ; i++) {
		printf("(and ") ;
		for (j = 1 ; j <= 7 ; j++) {
			printf("(and ") ;
			for (k = j + 1 ; k <= 8 ; k++) {
				printf("(not (and p%d%d p%d%d))", j, i, k, i) ;
			}
			printf(")") ;
		}
		printf(") ") ;
	}
	printf("))\n") ;

	// Q4
	printf("; Q4\n") ;
	printf("(assert ") ;
	printf("(and ") ;
	for (i = 2 ; i <= 8 ; i++) {
		printf("(and ") ;
		for (j = 1 ; j <= 7 ; j++) {
			printf("(and ") ;
			for (k = 1 ; k <= min(i - 1, 8 - j) ; k++) {
				printf("(not (and p%d%d p%d%d))", i, j, i - k, k + j) ;
			}
			printf(")") ;
		}
		printf(") ") ;
	}
	printf("))\n") ;

	// Q5
	printf("; Q5\n") ;
	printf("(assert ") ;
	printf("(and ") ;
	for (i = 1 ; i <= 7 ; i++) {
		printf("(and ") ;
		for (j = 1 ; j <= 7 ; j++) {
			printf("(and ") ;
			for (k = 1 ; k <= min(8 - i, 8 - j) ; k++) {
				printf("(not (and p%d%d p%d%d))", i, j, i + k, j + k) ;
			}
			printf(")") ;
		}
		printf(") ") ;
	}
	printf("))\n") ;

	printf("(check-sat)\n(get-model)\n") ;
}

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
	FILE * fp = fopen("formula", "w") ;

	int i, j, k ;

	for (i = 1 ; i <= 8 ; i++)
		for (j = 1 ; j <= 8 ; j++)
			fprintf(fp,"(declare-const p%d%d Bool)\n", i, j) ;

	// Q1
	fprintf(fp,"; Q1\n") ;
	fprintf(fp,"(assert (and ") ;
	for (i = 1 ; i <= 8 ; i++) {
		fprintf(fp,"(or ") ;
		for (j = 1 ; j <= 8 ; j++) 
			fprintf(fp,"p%d%d ", i, j) ;
		fprintf(fp,")") ;
	}
	fprintf(fp,"))\n") ;

	fprintf(fp,"; Q2\n") ;
	fprintf(fp,"(assert ") ;
	fprintf(fp,"(and ") ;
	for (i = 1 ; i <= 8 ; i++) {
		fprintf(fp,"(and ") ;
		for (j = 1 ; j <= 7 ; j++) {
			fprintf(fp,"(and ") ;
			for (k = j + 1 ; k <= 8 ; k++) {
				fprintf(fp,"(not (and p%d%d p%d%d))", i, j, i, k) ;
			}
			fprintf(fp,")") ;
		}
		fprintf(fp,") ") ;
	}
	fprintf(fp,"))\n") ;

	// Q3
	fprintf(fp,"; Q3\n") ;
	fprintf(fp,"(assert (and ") ;
	for (j = 1 ; j <= 8 ; j++) {
		fprintf(fp,"(or ") ;
		for (i = 1 ; i <= 8 ; i++) 
			fprintf(fp,"p%d%d ", i, j) ;
		fprintf(fp,")") ;
	}
	fprintf(fp,"))\n") ;

	// Q4
	fprintf(fp,"; Q4\n") ;
	fprintf(fp,"(assert ") ;
	fprintf(fp,"(and ") ;
	for (i = 1 ; i <= 8 ; i++) {
		fprintf(fp,"(and ") ;
		for (j = 1 ; j <= 7 ; j++) {
			fprintf(fp,"(and ") ;
			for (k = j + 1 ; k <= 8 ; k++) {
				fprintf(fp,"(not (and p%d%d p%d%d))", j, i, k, i) ;
			}
			fprintf(fp,")") ;
		}
		fprintf(fp,") ") ;
	}
	fprintf(fp,"))\n") ;

	// Q5
	fprintf(fp,"; Q5\n") ;
	fprintf(fp,"(assert ") ;
	fprintf(fp,"(and ") ;
	for (i = 2 ; i <= 8 ; i++) {
		fprintf(fp,"(and ") ;
		for (j = 1 ; j <= 7 ; j++) {
			fprintf(fp,"(and ") ;
			for (k = 1 ; k <= min(i - 1, 8 - j) ; k++) {
				fprintf(fp,"(not (and p%d%d p%d%d))", i, j, i - k, k + j) ;
			}
			fprintf(fp,")") ;
		}
		fprintf(fp,") ") ;
	}
	fprintf(fp,"))\n") ;

	// Q6
	fprintf(fp,"; Q6\n") ;
	fprintf(fp,"(assert ") ;
	fprintf(fp,"(and ") ;
	for (i = 1 ; i <= 7 ; i++) {
		fprintf(fp,"(and ") ;
		for (j = 1 ; j <= 7 ; j++) {
			fprintf(fp,"(and ") ;
			for (k = 1 ; k <= min(8 - i, 8 - j) ; k++) {
				fprintf(fp,"(not (and p%d%d p%d%d))", i, j, i + k, j + k) ;
			}
			fprintf(fp,")") ;
		}
		fprintf(fp,") ") ;
	}
	fprintf(fp,"))\n") ;

	fprintf(fp,"(check-sat)\n(get-model)\n") ;

	fclose(fp) ;

	FILE * fin = popen("z3 formula", "r") ;
	char buf[128] ;
	fscanf(fin, "%s %s", buf, buf) ;
	while (!feof(fin)) {
		fscanf(fin, "%s", buf) ; //printf("%s ", buf) ;
		fscanf(fin, "%s", buf) ; printf("%s ", buf) ;
		fscanf(fin, "%s", buf) ; //printf("%s ", buf) ;
		fscanf(fin, "%s", buf) ; //printf("%s ", buf) ;
		fscanf(fin, "%s", buf) ; printf("%s\n", buf) ;
	}
	pclose(fin) ;

}


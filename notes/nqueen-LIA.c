#include <stdio.h>

int 
main ()
{
	FILE * fp = fopen("formula", "w") ;

	int x, y ;

	for (y = 1 ; y <= 8 ; y++)
		for (x = 1 ; x <= 8 ; x++)
			fprintf(fp, "(declare-const a%d%d Int)\n", y, x) ;

	for (y = 1 ; y <= 8 ; y++)
		for (x = 1 ; x <= 8 ; x++)
			fprintf(fp, "(assert (and (<= a%d%d 1) (<= 0 a%d%d)))\n", y, x, y, x) ;

	fprintf(fp, "(assert(= (+ ") ;
	for (y = 1 ; y <= 8 ; y++) 
		for (x = 1 ; x <= 8 ; x++) 
			fprintf(fp, "a%d%d ", y, x) ;
	fprintf(fp, ") 8))\n") ;

	for (x = 1 ; x <= 8 ; x++) {
		int i_y ;
		fprintf(fp, "(assert(<= (+ ") ;
		for (i_y = 1 ; i_y <= 8 ; i_y++)
			fprintf(fp, "a%d%d ", i_y, x) ;
		fprintf(fp, ") 1))\n") ;
	}

	for (y = 1 ; y <= 8 ; y++) {
		int i_x ;
		fprintf(fp, "(assert(<= (+ ") ;
		for (i_x = 1 ; i_x <= 8 ; i_x++)
			fprintf(fp, "a%d%d ", y, i_x) ;
		fprintf(fp, ") 1))\n") ;
	}

	for (y = 1 ; y <= 8 ; y++) {
		for (x = 1 ; x <= 8 ; x++) {
			int i_y, i_x ;

			i_y = (y <= x) ? 1 : y - x + 1 ;
			i_x = (x <= y) ? 1 : x - y + 1 ;
			fprintf(fp, "(assert(<= (+ ") ;
			while (i_x <= 8 && i_y <= 8) {
				fprintf(fp, "a%d%d ", i_y, i_x) ;
				i_y += 1 ;
				i_x += 1 ;
			}
			fprintf(fp, ") 1))\n") ;

			i_y = (x + y <= 8) ? 1 : y - 8 + x ;
			i_x = (x + y > 8) ? 8 : x + y - 1 ;
			fprintf(fp, "(assert(<= (+ ") ;
			while (i_x >= 1 && i_y <= 8) {
				fprintf(fp, "a%d%d ", i_y, i_x) ;
				i_y += 1 ;
				i_x -= 1 ;
			}
			fprintf(fp, ") 1))\n") ;
		}
	}
	fprintf(fp, "(check-sat)\n(get-model)\n") ;

	fclose(fp) ;

	FILE * fin = popen("z3 formula", "r") ; //FIXME
	char buf[128] ;
	fscanf(fin, "%s %s", buf, buf) ;
	while (!feof(fin)) {
		fscanf(fin, "%s", buf) ; printf("%s ", buf) ;
		fscanf(fin, "%s", buf) ; printf("%s ", buf) ;
		fscanf(fin, "%s", buf) ; printf("%s ", buf) ;
		fscanf(fin, "%s", buf) ; printf("%s ", buf) ;
		fscanf(fin, "%s", buf) ; printf("%s\n", buf) ;
	}
	pclose(fin) ;
}


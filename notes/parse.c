#include <stdio.h>
#include <string.h>

char board[9][9] ;

int main ()
{
	int i, j, k;

	char b[128] ;
	char s[128] ;
	char t[128] ;

	scanf("%s %s", b, b) ;
	for (k = 0 ; k < 64 ; k++) {
		scanf("%s %s %s %s %s", b, s, b, b, t) ;

		i = s[1] - '0' ;
		j = s[2] - '0' ;

		if (strcmp(t, "false)") != 0) {
			board[i][j] = 1 ;
		}
	}

	for (i = 1 ; i <= 8 ; i++) {
		for (j = 1 ; j <= 8 ; j++) {
			printf("%d ", board[i][j]) ;
		}
		printf("\n") ;
	}
}

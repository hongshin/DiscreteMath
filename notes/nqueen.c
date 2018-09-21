#include <stdio.h>

int main()
{
  int x, y ;

  for (y = 1 ; y <= 8 ; y++)
    for (x = 1 ; x <= 8 ; x++)
      printf("(declare-const a%d%d Int)\n", y, x) ;

      for (y = 1 ; y <= 8 ; y++)
        for (x = 1 ; x <= 8 ; x++)
          printf("(assert (and (<= a%d%d 1) (<= 0 a%d%d)))\n", y, x, y, x) ;

  printf("(assert(= (+ ") ;
  for (y = 1 ; y <= 8 ; y++) 
    for (x = 1 ; x <= 8 ; x++) 
      printf("a%d%d ", y, x) ;
  printf(") 5))\n") ;

  for (y = 1 ; y <= 8 ; y++) {
    for (x = 1 ; x <= 8 ; x++) {
      int i_y, i_x ;

      printf("(assert(<= (+ ") ;
      for (i_y = 1 ; i_y <= 8 ; i_y++)
        printf("a%d%d ", i_y, x) ;
      printf(") 1))\n") ;

      printf("(assert(<= (+ ") ;
      for (i_x = 1 ; i_x <= 8 ; i_x++)
        printf("a%d%d ", y, i_x) ;
      printf(") 1))\n") ;

      i_y = (y <= x) ? 1 : y - x + 1 ;
      i_x = (x <= y) ? 1 : x - y + 1 ;
      printf("(assert(<= (+ ") ;
      while (i_x <= 8 && i_y <= 8) {
        printf("a%d%d ", i_y, i_x) ;
        i_y += 1 ;
        i_x += 1 ;
      }
      printf(") 1))\n") ;

      i_y = (x + y <= 8) ? 1 : y - 8 + x ;
      i_x = (x + y > 8) ? 8 : x + y - 1 ;
      printf("(assert(<= (+ ") ;
      while (i_x >= 1 && i_y <= 8) {
        printf("a%d%d ", i_y, i_x) ;
        i_y += 1 ;
        i_x -= 1 ;
      }
     printf(") 1))\n") ;
    }
  }
  printf("(check-sat)\n(get-model)\n") ;
}

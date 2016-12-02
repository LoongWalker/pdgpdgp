#include <stdlib.h>
#include <stdio.h>

int main(int argc, char *argv[]) {
  char *x = (char *)malloc(sizeof(char));
  *x = 'a';
  char *y = x;
  char *z = y;

  printf("x: %c, y: %c, z: %c\n", *x, *y, *z);

  return 0;
}

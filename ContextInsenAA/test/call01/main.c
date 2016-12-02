#include <stdlib.h>

void modify(char *c) {
  c[0] = 'b';
}
int main(int argc, char *argv[]) {
  char *c = (char *)malloc(sizeof(char));
  modify(c);

  return 0;
}

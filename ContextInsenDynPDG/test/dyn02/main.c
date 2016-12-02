int add(int a, int b) {
  return a + b;
}

int sub(int a, int b) {
  return a - b;
}

int main(int argc, char *argv[]) {
  int r1;
  int r2;

  int a = 1;
  int b = 2;
  int (*f1)(int, int) = add;
  int (*f2)(int, int) = sub;

  r1 = f1(a, b);
  r2 = f2(a, b);

  return r1 - r2;
}

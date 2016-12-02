int add(int a, int b) {
  return a + b;
}
int main(int argc, char *argv[]) {
  int ret;
  int a = 1;
  int b = 2;
  int (*f)(int, int) = add;

  ret = f(a,b);

  return ret;
}

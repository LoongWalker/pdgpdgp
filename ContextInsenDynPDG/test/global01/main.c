int a;

void f1(void) {
  a += 10;
}

void f2(void) {
  a += 20;
}

int main(int argc, char *argv[]) {
  a = 0;
  f1();
  f2();
  return 0;
}

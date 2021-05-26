#include "homework.h"

int main() {
  int i;
  int sum = 0;
  int z;
  for (i = 10; i > 1; i--) {
    sum += i;
  }
  z = 10 / (i - 1); // safe by interval with narrowing, false alarm by sign
  z = 10 / i;       // error
  return 0;
}

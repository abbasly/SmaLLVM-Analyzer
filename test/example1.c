#include "homework.h"

int main() {
  int x = source();
  int z;
  if (x >= 0) {
    z = 10 / x; // error
    if (x < 0) {
      z = 10 / x; // unreachable
    }
  } else {
    z = 10 / x; // safe
  }
  z = 10 / x; // error
  return 0;
}

#include "homework.h"

int main() {
  int x = source();
  int y;
  if (x > 0) {
    y = sanitizer(x);
    sink(y); // safe
  } else {
    y = x;
  }
  sink(y); // bug
  return 0;
}

#include "homework.h"

int main()
{
  int x = source();
  int t = 10;

  if (x >= 10) {
    int y = 100 / x;
    int w = x / 0;
    t = 10 - x;
    }
    else if(x <= -10)
    {
        int y = 100 / x;

        t = 10 + x - x + x;
    }
    else if(x >= 0)
    {
        int y = 100 / x;
        t = t * x;
    }
    else
    {
        int y = 100 / x;
        t = t / y;
    }

    t = x / t;
}

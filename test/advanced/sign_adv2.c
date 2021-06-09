#include "homework.h"

int main()
{
  int x = source();
  int i = 0;
  int j = 0;
  int phi = 0;

  if (x >= 0) {
    for (i = 0; i < x; i++) {
      phi += i;
      j = phi;

      for (j = 0; j < phi; j++) {
        int m = (phi * j) / i;

        if (m >= 0) {
          int k = m / x;
        }
      }
    }
    }
    else
    {
        x = -x;

        for(i = 0; i < x; i++)
        {
            phi -= i;
            j = i + phi;

            for(j = 0; j > phi; j--)
            {
                int m = (phi * j) / i;

                if(m >= 0)
                {
                    int k = m / x;
                }
            }
        }
    }


    phi = i + j;
}

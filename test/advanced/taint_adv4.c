#include "homework.h"

int main() {
	int x = source(); 
	int y = sanitizer(x);
	int i = 0;
        if (x>0)
        {
	    for (i=x; i>0; i--)
	    {
	        y -= i;
	    }
            sink(y);
        }
        else
	{
	    for (i=y; i<=0; i++)
	    {
	        y += i;
	    }
            sink(y);
	}
        x = y;
        sink(x);
	return 0;
}

#include "homework.h"

int main() {
	int x = source();
	int result = 0;

	while(result<5)
	{
            result += sanitizer(x);
	}

        sink(result);
	sink(x);

	return 0;
}

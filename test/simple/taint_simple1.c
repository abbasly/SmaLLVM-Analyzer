#include "homework.h"

int main() {
	int x = source(); 
	int y = x * 10;
	int z = sanitizer(x) + y;

	sink(z);
	return 0;
}

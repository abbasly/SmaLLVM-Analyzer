#include "homework.h"

int main() {
	int x = source(); 
	int y = sanitizer(x);

	int temp = x;
	x = y;
	y = temp;

	sink(x);
	sink(y);
	
	return 0;
}

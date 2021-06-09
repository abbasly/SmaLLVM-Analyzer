#include "homework.h"

int main() {
	int x = source(); 
	int y = sanitizer(x);
	int z = y;
	int result;

	if(x > 0){
		x = y + z;
		result = x;
		sink(result);
	}
	else{
		result = x + y;
		sink(result);
	}

	return 0;
}

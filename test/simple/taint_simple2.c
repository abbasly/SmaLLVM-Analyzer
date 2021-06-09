#include "homework.h"

int main() {
	int x = source(); 
	int y = sanitizer(x);
	int z = y * 100;
	int result;

	if(x > 0){
		result = x + y;
		sink(result);
	}
	else{
		result = y + z;
		sink(result);
	}
	return 0;
}

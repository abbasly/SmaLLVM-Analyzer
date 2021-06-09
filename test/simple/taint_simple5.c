#include "homework.h"

int main() {
	int x = source(); 
	int y = 10;
	int result;

	if(x + y < 0){
		result = y * 10;
		sink(result);
	}
	else if(x + y < 10){
		result = x * y;
		sink(result);
	}
	else if(x + y < 100){
		result = sanitizer(x);
		sink(result);
	}
	else{
		result = x * y;
		sink(result);
	}
	return 0;
}

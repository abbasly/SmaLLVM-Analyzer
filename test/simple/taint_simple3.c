#include "homework.h"

int main() {
	int x = source(); 
	int y = sanitizer(x);

	if(x > 0){
		if(x < 0){
			sink(x); // unreachable
		}
		sink(y);
	}
	else{
		sink(y);
	}
	
	sink(x);
	return 0;
}

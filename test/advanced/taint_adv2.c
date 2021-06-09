#include "homework.h"

int main() {
	int x = source(); 
	int result;

	if (x > 0){
		if (x > 1){
			result = 0;
			for (int i=1; i<=x; i++){
				result = result * i;
			}
			sink(result);
		}
		else if (x == 1){
			result = 1;
			sink(result);
		}
		else {
			result = sanitizer(x);
			sink(result);
		}
	}
	
	sink(x);
	return 0;
}

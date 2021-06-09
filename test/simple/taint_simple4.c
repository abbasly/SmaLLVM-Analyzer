#include "homework.h"

int main() {
	int x = source(); 
	int sum = x;

	for(int i=0; i < 10; i++){
		sum += i;
	}
	sink(sum);
	return 0;
}

int global = 0;

int main() {
	int a = global + 1;
	global += 10;
	global += 11;
	a += 12;
	return a + global;
}

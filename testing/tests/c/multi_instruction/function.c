int max(int a, int b, int c) {
    int max = a > b ? a : b;
    max = max > c ? max : c;
    return max;
}


int main() {
    int a = 10;
    int b = 20;
    int c = 30;
    max(a, b, c);
    return 0;
}

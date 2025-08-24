// src/index.napalm

print("===== Simple function =====");
fn add2(a, b) {
    return a + b;
}

print(add2(2, 3)); // expect 5

print("===== Recursive function =====");
fn fibonacci(n) {
    if (n <= 1) {
        return n;
    }
    return fibonacci(n - 1) + fibonacci(n - 2);
}
print(fibonacci(5)); // expect 5

print("===== While loop =====");
var x = 0;
while (x < 10) {
    x += 1;
}
print(x); // expect 10

print("===== For loop =====");
var y = 0;
for (var i = 0; i < 5; i += 1) {
    y += i;
}
print(y); // expect 10

print("===== If-else with else unless =====");
var x = 3;
if (x == 0) {
    x = x + 0;
} else unless (x < 0) {
    x = x + 1;
} else {
    x = x - 1;
}
print(x); // expect 4

print("===== Lambda functions =====");
print((fn (a, b) { return a + b; })(2, 3));      // 5
print((|x| x + 1)(41));                  // 42
print((|a, b| { return a*b; })(6, 7));   // 42

print("===== Closures =====");
fn make_adder(x) {
    return |y| x + y;
}

var add42 = make_adder(42);
print(add42(0));  // expect 42
print(add42(100)); // expect 142
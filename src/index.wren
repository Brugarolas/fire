// A tiny program with one function; JIT will run this by name.
fn add2(a, b) {
    return a + b;
}

print(add2(2, 3)); // expect 5

var x = 0;
while (x < 10) {
    x += 1;
}
print(x); // expect 10

var y = 0;
for (var i = 0; i < 5; i += 1) {
    y += i;
}
print(y); // expect 10
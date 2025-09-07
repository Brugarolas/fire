var fib = function(n) {
    if (n <= 1) return n;

    return fib(n-1) + fib(n-2);
};

var t0 = performance.now();     // 1) start
var result = fib(50);
var t1 = performance.now();     // 2) end
var dt = t1 - t0;               // 3) difference
var secs = dt / 1000;           // 4) milliseconds to seconds
console.log(`Fibonacci(50) = ${result}, time = ${secs.toFixed(6)} s`);  // 5) print
// console.log(fib(40)); --- IGNORE ---
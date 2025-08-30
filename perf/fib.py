import time

def fibonacci(num: int) -> int:
    # check if num is less than 0 it will return none
    if num < 0:
        print("Incorrect input")
        return

    # check if num between 1, 0 it will return num
    elif num < 2:
        return num

    # return the fibonacci of num - 1 & num - 2
    return fibonacci(num - 1) + fibonacci(num - 2)

t0 = time.perf_counter()     # 1) start
fib = fibonacci(40)
t1 = time.perf_counter()     # 2) end
dt = t1 - t0                 # 3) difference
secs = dt                    # 4) already seconds

print(f"Fibonacci(40) = {fib}, time = {secs:.6f} s")  # 5) print
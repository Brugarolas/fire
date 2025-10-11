import sys
import time

def make_tree(d):
    if d > 0:
        d -= 1
        return (make_tree(d), make_tree(d))
    return (None, None)


def check_tree(node):
    (l, r) = node
    if l is None:
        return 1
    else:
        return 1 + check_tree(l) + check_tree(r)


def make_check(d, make=make_tree, check=check_tree):
    return check(make(d))


def main(n, min_depth=4):

    max_depth = max(min_depth + 2, n)
    stretch_depth = max_depth + 1
    print('stretch tree of depth {0}\t check: {1}'.format(stretch_depth, make_check(stretch_depth)))

    long_lived_tree = make_tree(max_depth)

    mmd = max_depth + min_depth
    for d in range(min_depth, stretch_depth, 2):
        i = 2 ** (mmd - d)
        cs = 0
        for _ in range(0, i):
            cs += make_check(d)
        print('{0}\t trees of depth {1}\t check: {2}'.format(i, d, cs))

    print('long lived tree of depth {0}\t check: {1}'.format(max_depth, check_tree(long_lived_tree)))


if __name__ == '__main__':
    t0 = time.perf_counter()     # 1) start
    main(10)
    t1 = time.perf_counter()     # 2) end
    dt = t1 - t0                 # 3) difference
    secs = dt                    # 4) already seconds
    print(f"Time = {secs:.6f} s")  # 5) print
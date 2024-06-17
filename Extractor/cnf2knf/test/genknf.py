#!/usr/local/bin/python3

import sys

def header(n, total):
    print("p knf %d %d" % (n, total))

def upper(n, lim):
    lower = n-lim
    slist = [str(-i) for i in range(1, n+1)] + ["0"]
    print("k %d %s" % (lower, " ".join(slist)))

def lower(n, lim):
    slist = [str(i) for i in range(1, n+1)] + ["0"]
    if lim > 1:
        print("k %d %s" % (lim, " ".join(slist)))
    else:
        print(" ".join(slist))

def gen(n, low, high):
    need_upper = high < n
    need_lower = low > 0
    kcount = 0
    if need_upper:
        kcount += 1
    if need_lower:
        kcount += 1
    header(n, kcount)
    if need_upper:
        upper(n, high)
    if need_lower:
        lower(n, low)

def run(name, args):
    if len(args) == 0 or args[0] == '-h':
        print("Usage %s N [UPPER [LOWER]]" % name)
        return
    n = int(args[0])
    low = 0
    high = n
    if len(args) >= 2:
        high = int(args[1])
    if len(args) >= 3:
        low = int(args[2])
    
    if low > high:
        print("c WARNING: Lower bound %d > Upper bound %d" % (low, high))

    gen(n, low, high)

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])

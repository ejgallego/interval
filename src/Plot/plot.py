import re
import sys

real_re = re.compile(r'([^%]*)')
int_re = re.compile(r'([-0-9]+)')
pair_re = re.compile(r'\(([0-9]+)%?Z?, ([0-9]+)%?Z?\)')

def read_real(s):
    return re.sub(int_re, r'\1.', re.match(real_re, s).group(1))

ox = read_real(sys.stdin.readline())
dx = read_real(sys.stdin.readline())
oy = read_real(sys.stdin.readline())
dy = read_real(sys.stdin.readline())
h  = int(re.match(real_re, sys.stdin.readline()).group(1))

values = []

for m in pair_re.finditer(sys.stdin.read()):
    y1 = m.group(1)
    y2 = m.group(2)
    values.append([int(y1), int(y2)])

mode = "vec"

w = len(values)

print(f"ox = {ox}")
print(f"dx = {dx}")
print(f"oy = {oy}")
print(f"dy = {dy}")

if mode == "vec":

    print("set xrange [] noextend")
    print("plot '-' using (ox+dx*$1):(oy+dy*$2):(oy+dy*$3) notitle with filledcurves")
    z1, z2 = values[0]
    print(0, z1, z2)

    for i in range(1,w):
        y1, y2 = values[i]
        if y1 < z1: z1 = y1
        if y2 > z2: z2 = y2
        print(i, z1, z2)
        z1, z2 = y1, y2

    print(w, z1, z2)
    print("e")
    print("pause mouse close")

else:

    ww = w + 150
    hh = h + 100
    print(f"set terminal png size {ww},{hh}")
    print(f"set lmargin at screen {100/ww}")
    print(f"set rmargin at screen {(100+w)/ww}")
    print(f"set tmargin at screen {50/hh}")
    print(f"set bmargin at screen {(50+h)/hh}")
    #print(f"set size ratio {h/w}")
    print("set xrange [] noextend")
    print("set yrange [] noextend")
    print(f"plot '-' binary array=({w},{h}) scan=yx format='%uchar' origin=(ox+dx/2,oy+dy/2) dx=dx dy=dy using 1:1:1 notitle with rgbimage")
    sys.stdout.flush()

    s = b''
    for i in range(0, w):
        y1, y2 = values[i]
        s = s + (b'\xFF' * y1) + (b'\x00' * (y2 - y1)) + (b'\xFF' * (h - y2))

    sys.stdout.buffer.write(s)

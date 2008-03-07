import pickle
from path import path
import sys
import pygame
from pygame.locals import *
from pylab import *
import time

repo = path(sys.argv[1])
import re
rx = re.compile(r'\d+ \d+')

def getStuff():
    for filename in repo.walkfiles():
        distrib, rule, cands, n, m = filename.name[:-5].split('-')
        cands = int(cands)
        n = int(n)
        m = int(m)
        #print distrib, rule, cands, n, m

        f = file(filename)
        data = f.read()
        #f.close()
        data = re.findall(rx, data)
        data = dict(list(reversed(map(int, s.split()))) for s in data)

        seq = []
        val = 0
        for i in range(cands, 0, -1):
            val += data.get(i, 0)
            seq.append((i,val))
        seq.reverse()
        if data != {}:
            print distrib, rule, n
            yield ((distrib, rule, n), m, [b for (a,b) in seq])

p = path('/tmp/cur.pyp')
if p.exists():
    stuff, distribs, rules, ns = pickle.loads(file(p).read())
else:
    stuff = list(getStuff())
    distribs = list(sorted(set(d for ((d,r,n),_,_) in stuff)))
    rules = list(sorted(set(r for ((d,r,n),_,_) in stuff)))
    ns = list(sorted(set(n for ((d,r,n),_,_) in stuff)))
    file(p, 'w').write(pickle.dumps((stuff,distribs,rules,ns)))

def doplot(ni, di, ri):
    mystuff = [(m,v) for ((d,r,n),m,v) in stuff
               if d == distribs[di] and
               r == rules[ri] and
               n == ns[ni]]
    ioff()
    cla()
    title('%s distribution under %s, %d non-manipulators' %
          (distribs[di], rules[ri], ns[ni]))
    xlabel('Manipulators')
    ylabel('Instances with at least n winners')
    
    a=plot([m for (m,v) in mystuff],
           [v[0] for (m,v) in mystuff])
    b=plot([m for (m,v) in mystuff],
           [v[1] for (m,v) in mystuff])
    c=plot([m for (m,v) in mystuff],
           [v[2] for (m,v) in mystuff])
    legend((a,b,c), map(lambda d: '%d winners' % d, range(1,4)), 'best')


    ion()
    draw()

def main():
    pygame.init()
    screen = pygame.display.set_mode((468, 60))
    pygame.display.set_caption('Monkey Fever')
    pygame.mouse.set_visible(0)
    clock = pygame.time.Clock()

    di = ri = ni = 0
    draw()
    while True:
        time.sleep(1/60.)

        for event in pygame.event.get():
            if event.type == QUIT:
                sys.exit(0)
            elif event.type == KEYDOWN and event.key == K_ESCAPE:
                sys.exit(0)
            elif event.type == KEYDOWN and event.key == K_0:
                ni += 1
                ni %= len(ns)
            elif event.type == KEYDOWN and event.key == K_9:
                ni -= 1
                ni %= len(ns)
            elif event.type == KEYDOWN and event.key == K_UP:
                di += 1
                di %= len(distribs)
            elif event.type == KEYDOWN and event.key == K_DOWN:
                di -= 1
                di %= len(distribs)
            elif event.type == KEYDOWN and event.key == K_LEFT:
                ri -= 1
                ri %= len(rules)
            elif event.type == KEYDOWN and event.key == K_RIGHT:
                ri += 1
                ri %= len(rules)
            else:
                continue

            doplot(ni, di, ri)
            draw()

def gomainthread():
    import threading
    threading.Thread(target=main).start()

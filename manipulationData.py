from __future__ import with_statement
import re

_datarx = re.compile(r'^(\d+) (lower|upper): (.*)$')

def readFiles(*filenames):
    repo = {}
    for name in filenames:
        with file(name) as f:
            for line in f:
                match = _datarx.match(line)
                if match:
                    num, bound, data = match.groups()
                    repo[(int(num), bound)] = eval(data)
    return repo

def missing(repo):
    for num in range(1,1001):
        if (num, 'lower') not in repo or (num, 'upper') not in repo:
            yield num

def writeRepo(repo, filename):
    keys = repo.keys()
    keys.sort()
    with file(filename, 'w') as f:
        for (num, bound) in keys:
            print >> f, '%s %s: %s' % (num, bound, str(repo[(num, bound)]))

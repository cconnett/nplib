from __future__ import with_statement
import re
import os.path

EVAL = True

_datarx = re.compile(r'^(\d+) (lower|upper): (.*)$')

def readFiles(*filenames):
    repo = {}
    for name in filenames:
        if os.path.exists(name):
            with file(name) as f:
                for line in f:
                    match = _datarx.match(line)
                    if match:
                        num, bound, data = match.groups()
                        if (int(num), bound) in repo:
                            continue
                        if EVAL:
                            try:
                                repo[(int(num), bound)] = eval(data)
                            except SyntaxError:
                                print 'Read error on %d %s' % (int(num), bound)
                                pass
                        else:
                            repo[(int(num), bound)] = data
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
            if EVAL:
                data = str(repo[(num,bound)])
            else:
                data = repo[(num,bound)]
            print >> f, '%s %s: %s' % (num, bound, data)

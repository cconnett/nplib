import manipulationData as md
import time

def consistent(lowers1, uppers1, lowers2, uppers2):
    for lower1, upper1, lower2, upper2 in zip(lowers1, uppers1, lowers2, uppers2):
        if not max(lower1, lower2) <= min(upper1, upper2):
            return False
    return True

for n in [32,64,128,256]:
    for cands in [3,4,5]:
        for distribution in ['uniform', 'condorcet', 'spatial']:
            for rule in ['borda','veto','irv','copeland','pluralityWithRunoff']:
                if cands == 3 and rule == 'pluralityWithRunoff':
                    continue
                if n == 256 and distribution != 'uniform':
                    continue

                print n, cands, distribution, rule
                base1 = ('/home/stu2/s1/cxc0117/thesis/run/data/' +
                         '-'.join([distribution[0], str(cands),
                                  str(n), rule]))
                base2 = ('/home/stu2/s1/cxc0117/thesis/run/bfdata/' +
                         '-'.join([distribution[0], str(cands),
                                  str(n), rule]))
                repo1 = md.readFiles(base1 + '.repo')
                repo2 = md.readFiles(base2 + '.repo')

                for i in range(1,1001):
                    try:
                        lowers1 = repo1[(i, 'lower')]
                        uppers1 = repo1[(i, 'upper')]
                        lowers2 = repo2[(i, 'lower')]
                        uppers2 = repo2[(i, 'upper')]
                    except KeyError:
                        print 'Cannot check %d' % i
                        continue
                    if not consistent(lowers1, uppers1, lowers2, uppers2):
                        print 'OH SHIT!'
                        print i,
                        print 'SAT:', lowers1, uppers1,
                        print 'BF:', lowers2, uppers2
                        time.sleep(.5)


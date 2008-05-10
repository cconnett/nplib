import manipulationData as md
import sys
from glob import glob

for n in [1,2,4,8,16,32,64,128,256]:
    for cands in [3,4,5]:
        for distribution in ['uniform', 'condorcet', 'spatial']:
            for rule in ['borda','veto','plurality','irv','copeland','pluralityWithRunoff']:
                print n, cands, distribution, rule
                base = ('/home/stu2/s1/cxc0117/thesis/run/data/' +
                        '-'.join([distribution[0], str(cands),
                                  str(n), rule]))
                files = glob(base + '*out*') + [base + '.data']
                repo = md.readFiles(*files)
                md.writeRepo(repo, base + '.repo')

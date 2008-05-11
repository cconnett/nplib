#!/bin/python
import sys
import time
from subprocess import Popen as Process
import random
import manipulationData as md
from glob import glob

executable = '/home/stu2/s1/cxc0117/thesis/code/Solve'


hosts = ['achilles', 'odysseus', 'agamemnon', 'heracles',
         'rhea', 'dione', 'prometheus', 'oedipus', 'perseus',
         'andromeda', 'gorgon', 'medusa', 'cerberus', 'siren',
         'pegasus', 'centaur', 'cyclops', 'yes', 'platters',
         'kinks', 'joplin', 'hendrix', 'beatles', 'drifters',
         'buddy', 'doors', 'stones', 'valens', 'orbison', 'elvis',
         #'domino',
         'berry', 'everlys', 'supremes', 'maine',
         'iowa', 'florida', 'alaska', 'alabama', 'delaware',
         'missouri', 'nebraska', 'indiana', 'utah', 'massachusetts',
         'arizona',
         'newyork', 'michigan', 'kansas', 'idaho',
         'georgia', 'illinois', 'vermont', 'california', 'arkansas',
         'nevada', 'rhodeisland']
#hosts = sum([[host+'1',host+'2'] for host in hosts], [])

class instance(object):
    def __init__(self, cands, distribution, n, rule,
                 targetlist=None, fragmentNo=0):
        self.cands = cands
        self.distribution = distribution
        self.n = n
        self.rule = rule
        self.host = None
        self.process = None
        self.targetlist = targetlist
        if self.targetlist == None:
            self.targetlist = range(1, 1001)
        self.fragmentNo = fragmentNo

        self.donelist = None
        self.updatedonelist()

    @property
    def numdone(self):
        return len(self.donelist)
    def updatedonelist(self):
        self.donelist = []
        data = md.readFiles(*([self.repo] + glob(self.repo[:-5] + '.out*')))
        for target in self.targetlist:
            if (target, 'lower') in data and (target, 'upper') in data:
                self.donelist.append(target)

    @property
    def missing(self):
        return list(set(self.targetlist) - set(self.donelist))
    @property
    def numtogo(self):
        return len(self.missing)

    @property
    def input(self):
        return '/tmp/bigElections/' + \
               '-'.join([self.distribution[0], str(self.cands), str(self.n)])
    @property
    def output(self):
        if self.fragmentNo == 0:
            return self.repo
        else:
            return ('/home/stu2/s1/cxc0117/thesis/run/data/' +
                    '-'.join([self.distribution[0], str(self.cands),
                              str(self.n), self.rule]) +
                    '.out%02d' % self.fragmentNo)

    @property
    def repo(self):
        return ('/home/stu2/s1/cxc0117/thesis/run/data/' +
                '-'.join([self.distribution[0], str(self.cands),
                          str(self.n), self.rule]) + '.repo')

    def __str__(self):
        s = ''
        s += '%4d of %4d / ' % (self.numdone, len(self.targetlist))
        s += '(%14s) ' % (self.host if self.host else 'PENDING')
        s += '%13s %d %3d %19s' % (self.distribution, self.cands,
                                   self.n, self.rule)
        return s

def checkProcs():
    for i in instances:
        i.updatedonelist()
    finished_instances = [i for i in instances if not i.missing]
    for i in finished_instances:
        i.process = 'DONE'
        i.host = 'DONE'
        instances.remove(i)

instances = []
for n in [1,2,4,8,16,32,64,128,256]:
    for cands in [3,4,5]:
        for distribution in ['uniform', 'condorcet', 'spatial']:
            for rule in ['borda','veto','plurality','irv','copeland','pluralityWithRunoff']:
                i = instance(cands, distribution, n, rule)
                if i.numtogo > 0:
                    print i.cands, i.distribution, i.n, i.rule, i.numtogo
                    instances.append(i)

def dpScore(assignment):
    return max(float(instance.numtogo) / assignment[index]
               if assignment and assignment[index] > 0 else sys.maxint
               for (index, instance) in enumerate(instances)
               if index < len(assignment))

if len(hosts) > len(instances):
    print 'Breaking up instances'

    dp = {}

    for i in range(1, len(instances)+1):
        print i
        for h in range(1, len(hosts)+1):
            if i == 1:
                dp[(i,h)] = [h]
            elif i == h:
                dp[(i,h)] = [1] * h
            elif i > h:
                dp[(i,h)] = None
            else:
                dp[(i,h)] = min([dp[(i-1,h-mine)] + [mine]
                                 for mine in range(1,h-i+1)],
                                key=dpScore)

    bestAssignment = dp[(len(instances),len(hosts))]
    bestPairs = zip(instances, bestAssignment)
    print bestAssignment

    instances=[]
    for (i, assigned) in bestPairs:
        perHost = float(i.numtogo) / assigned
        for fragmentNo in range(1, assigned + 1):
            newtargetlist = i.missing[
                int(round(perHost * (fragmentNo-1))):
                int(round(perHost *  fragmentNo   ))]
            newinstance = instance(i.cands, i.distribution, i.n, i.rule,
                                   newtargetlist, fragmentNo)
            instances.append(newinstance)

while instances:
    checkProcs()
    instances.sort(key=lambda i: (1 if i.host and host != 'DONE' else 0, i.numdone, -i.n, -i.cands,),
                   reverse=True)
    
    for instance in instances:
        if instance.process is None:
            occupiedhosts = [i.host for i in instances if i.process is not None]
            availablehosts = list(set(hosts) - set(occupiedhosts))

            if not availablehosts:
                break
            host = random.choice(availablehosts)
            #print host, 'is available'
            args = ['ssh', '-x', host.replace('1','').replace('2',''),
                    'ulimit -c 0; /usr/bin/nice -19 %s +RTS -c -RTS sat %s %s "%s"' %
                    (executable, rule, instance.input, str(instance.targetlist))]
            outputfilehandle = file(instance.output, 'a', 1)
            #print 'Launching', ' '.join(args)
            proc = Process(args,
                           stdout=outputfilehandle,
                           stderr=file(instance.output + '.err','a',0),
                           bufsize=1)
            #proc=Process(['echo','-n'])
            instance.process = proc
            instance.host = host

    print
    print
    print
    for i in reversed(instances):
        print i
    
    print '%s -- %d processes running -- %d pending.' % \
          (time.asctime(),
           len([i for i in instances if i.host and i.host != 'DONE']),
           len([i for i in instances if i.host == None])
           )
    time.sleep(45.0)

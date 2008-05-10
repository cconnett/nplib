#!/bin/python
import time
from subprocess import Popen as Process
from path import path
import random

executable = '/home/stu2/s1/cxc0117/thesis/code/Solve'

import sys

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
    def __init__(self, cands, distribution, n, rule):
        self.cands = cands
        self.distribution = distribution
        self.n = n
        self.rule = rule
        self.host = None
        self.process = None
    def _numdone(self):
        line = -1
        while True:
            try:
                lastTag = file(self.result).readlines()[line] .split(':')[0]
                try:
                    lastSolved = int(lastTag)
                except ValueError:
                    lastTag, upperOrLower = lastTag.split(' ')
                    try:
                        lastSolved = int(lastTag)
                    except ValueError:
                        line -= 1
                        continue
                    if upperOrLower == 'lower':
                        lastSolved -= 1
            except (IOError, IndexError):
                lastSolved = 0
            return lastSolved
    numdone = property(_numdone)
    def _input(self):
        return '/tmp/bigElections/' + \
               '-'.join([self.distribution[0], str(self.cands), str(self.n)])
    input = property(_input)
    result = property(lambda self: '/home/stu2/s1/cxc0117/thesis/run/data/' + \
                      '-'.join([self.distribution[0], str(self.cands), str(self.n), self.rule]) \
                      + '.data')
    def __str__(self):
        s = ''
        s += '%4d of 1000 / ' % self.numdone
        s += '(%14s) ' % (self.host if self.host else 'PENDING')
        s += '%13s %d %3d %19s' % (self.distribution, self.cands,
                                   self.n, self.rule)
        return s

instances = []
for n in [1,2,4,8,16,32,64,128,256]:
    for cands in [3,4,5]:
        for distribution in ['uniform', 'condorcet', 'spatial']:
            for rule in ['borda','veto','plurality','irv','copeland','pluralityWithRunoff']:
                i = instance(cands, distribution, n, rule)
                if i.numdone < 1000:
                    instances.append(i)

def checkProcs():
    finished_instances = [i for i in instances
                          if i.numdone == 1000]
    for i in finished_instances:
        i.process = 'DONE'
        i.host = 'DONE'
        instances.remove(i)

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
                    'ulimit -c 0; /usr/bin/nice -19 %s +RTS -c -RTS sat %s %s %s' % 
                    (executable, rule, instance.input, str(instance.numdone+1))]
            outputfilehandle = file(instance.result, 'a', 1)
            #print 'Launching', ' '.join(args)
            proc = Process(args,
                           stdout=outputfilehandle,
                           stderr=file(instance.result + '.err','a',0),
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

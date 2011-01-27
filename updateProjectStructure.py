from path import path
import itertools
import math
import re
import subprocess
import sys

modulerx = re.compile(r'module (\S+)')
proprx = re.compile(r'^(prop_\S+)')
dependencyrx = re.compile(r'^(\S+\.o) : (\S+\.h[si])$')

module = None
imports = []
props = []

for filename in sys.argv[2:]:
    for line in file(filename):
        modulematch = modulerx.search(line)
        propmatch = proprx.search(line)

        if modulematch:
            module = modulematch.group(1)
            imports.append(module)

        if propmatch:
            prop = propmatch.group(1)
            props.append('%s.%s' % (module, prop))

sys.stdout = file(sys.argv[1], 'w')

print 'module Main where'
print
print 'import IO'
print 'import Test.QuickCheck'
print
for i in imports:
    print 'import', i
print
print 'main = do'
print '  hSetBuffering stdout NoBuffering'
if len(props) > 0:
    numDigits = int(math.log(len(props)))
    statusString = '  putStr "[%%%dd of %%d] %%s: "' % numDigits
for (n, prop) in enumerate(props):
    print statusString % (n+1, len(props), prop)
    print '  quickCheck %s' % prop

sys.stdout.close()
sys.stdout = sys.__stdout__

ghc = subprocess.Popen(['ghc', '-M'] + list(path('.').walkfiles('*.hs')),
                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
if ghc.wait() != 0:
    print ghc.stdout.read()
    sys.exit(1)
target_filename = 'generated_Tupdeps'
streams = {}
dependencies = filter(bool, [dependencyrx.search(line) for line in file('Makefile')])
for output, dependencies in itertools.groupby(dependencies, key=lambda dep:dep.group(1)):
    output = path(output)
    inputs = [dep.group(2) for dep in dependencies]

    dest = output.splitpath()[0] / target_filename
    if dest not in streams:
        streams[dest] = file(dest, 'w')
    directory = output.splitpath()[0]
    print >> streams[dest], ': {0}{1} |> !HC |>'.format(directory.relpathto(inputs[0]),
                                                        ' | ' + ' '.join(directory.relpathto(ooi) for ooi in inputs[1:])
                                                        if len(inputs) > 1 else '')
for stream in streams.values():
    stream.close()

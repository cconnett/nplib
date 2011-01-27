import math
import sys
import re
import subprocess
import path

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

subprocess.Popen(['ghc', '-M', '-n'] + list(path.path('.').walkfiles('*.hs')),
                 stdout=subprocess.PIPE, stderr=subprocess.PIPE)
sys.stdout = file('generated_Tupdeps', 'w')
current_output = None
primary_input = None
order_only_inputs = []
for line in file('Makefile'):
    dependency = dependencyrx.search(line)
    if not dependency:
        continue
    output = dependency.group(1)
    inn = dependency.group(2)
    if output != current_output:
        if current_output is not None:
            print ': {0}{1} |> !HC |>'.format(primary_input,
                                             ' | ' + ' '.join(order_only_inputs)
                                             if order_only_inputs else '')
        primary_input = None
        order_only_inputs = []
        current_output = output

    if inn.endswith('.hs'):
        primary_input = inn
    if inn.endswith('.hi'):
        order_only_inputs.append(inn)
sys.stdout.close()

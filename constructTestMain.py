import sys
import re

modulerx = re.compile(r'module (\S+)')
proprx = re.compile(r'^(prop_\S+)')

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
print 'import Test.QuickCheck'
print
for i in imports:
    print 'import', i
print
print 'main = do'
for prop in props:
    print '  putStr "%s: "' % prop
    print '  quickCheck %s' % prop

sys.stdout.close()

BASEFLAGS=-fglasgow-exts -funbox-strict-fields -dcore-lint
PROFILEFLAGS=-prof -auto-all
#COVERAGEFLAGS=-fhpc
THREADED=-threaded
OPTFLAGS=-O -optc-O3 -optc-march=k8

FLAGS=${BASEFLAGS} ${THREADED} ${PROFILEFLAGS} ${COVERAGEFLAGS} ${OPTFLAGS} -i..

GHC=/tmp/ghc-6.8.2/bin/ghc
GHC=ghc

all: Addition Equality NSumDemo Mul1Bit Multiplication

clean:
	rm -rf *.o Addition Equality NSumDemo Mul1Bit Multiplication

Addition: Addition.hs
	${GHC} ${FLAGS} --make Addition.hs -o Addition
Equality: Equality.hs
	${GHC} ${FLAGS} --make Equality.hs -o Equality
NSumDemo: NSumDemo.hs
	${GHC} ${FLAGS} --make NSumDemo.hs -o NSumDemo
Mul1Bit: Mul1Bit.hs
	${GHC} ${FLAGS} --make Mul1Bit.hs -o Mul1Bit
Multiplication: Multiplication.hs
	${GHC} ${FLAGS} --make Multiplication.hs -o Multiplication
NumberMind: NumberMind.hs ../NInteger.hs
	${GHC} ${FLAGS} --make NumberMind.hs -o NumberMind

BASEFLAGS=-fglasgow-exts -fno-monomorphism-restriction -funbox-strict-fields -dcore-lint
#PROFILEFLAGS=-prof -auto-all
#COVERAGEFLAGS=-fhpc
THREADED=-threaded
OPTFLAGS=-O -optc-O3 -optc-march=k8

FLAGS=${BASEFLAGS} ${THREADED} ${PROFILEFLAGS} ${COVERAGEFLAGS} ${OPTFLAGS}

GHC=/tmp/ghc-6.8.2/bin/ghc
GHC=ghc

#all: BruteForce GenElections Summarize Solve Tests
all: Solve

clean:
	rm -rf *.o *.hi BruteForce GenElections Solve Summarize Tests *.tix .hpc

BruteForce: BruteForce.hs Elections.hs Manipulation.hs Voting.hs
	${GHC} ${FLAGS} --make BruteForce.hs -o BruteForce

GenElections: GenElections.hs Elections.hs Voting.hs RunGenIO.hs
	${GHC} ${FLAGS} --make GenElections.hs -o GenElections\

Summarize: Summarize.hs Elections.hs Voting.hs
	${GHC} ${FLAGS} --make Summarize.hs -o Summarize

Solve: *.hs
	${GHC} ${FLAGS} --make Solve.hs -o Solve

Tests: *.hs
	${GHC} ${FLAGS} --make Tests.hs -o Tests

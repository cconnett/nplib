BASEFLAGS=-fglasgow-exts -fno-monomorphism-restriction -funbox-strict-fields -dcore-lint
#PROFILEFLAGS=-prof -auto-all
#COVERAGEFLAGS=-fhpc
THREADED=-threaded
OPTFLAGS=-O -optc-O1

FLAGS=${BASEFLAGS} ${THREADED} ${PROFILEFLAGS} ${COVERAGEFLAGS} ${OPTFLAGS}

#all: BruteForce GenElections Summarize Solve Tests
all: Solve

clean:
	rm -rf *.o BruteForce GenElections Solve Summarize Tests *.tix .hpc

BruteForce: BruteForce.hs Elections.hs Manipulation.hs Voting.hs
	ghc ${FLAGS} --make BruteForce.hs -o BruteForce

GenElections: GenElections.hs Elections.hs Voting.hs RunGenIO.hs
	ghc ${FLAGS} --make GenElections.hs -o GenElections\

Summarize: Summarize.hs Elections.hs Voting.hs
	ghc ${FLAGS} --make Summarize.hs -o Summarize

Solve: *.hs
	ghc ${FLAGS} --make Solve.hs -o Solve

Tests: *.hs
	ghc ${FLAGS} --make Tests.hs -o Tests

BASEFLAGS=-fglasgow-exts -funbox-strict-fields -dcore-lint
#PROFILEFLAGS=-prof -auto-all
#COVERAGEFLAGS=-fhpc
THREADED=-threaded
OPTFLAGS=-O -optc-O3 -optc-march=native

FLAGS=${BASEFLAGS} ${THREADED} ${PROFILEFLAGS} ${COVERAGEFLAGS} ${OPTFLAGS}

GHC=/tmp/ghc-6.8.2/bin/ghc
GHC=ghc

#all: BruteForce GenElections Summarize Solve Tests
all: Solve

test: COVERAGEFLAGS=-fhpc
test: TestAll lint
	rm -f TestAll.tix
	./TestAll
	hpc report TestAll
	hpc markup TestAll --exclude Main > /dev/null

TestAll.hs: TestNPLib.hs TestNInteger.hs NInteger.hs NPLib.hs Utilities.hs
	python constructTestMain.py TestAll.hs $^
TestAll: TestAll.hs *.hs
	${GHC} ${FLAGS} --make $< -o $@

lint: *.hs
	hlint *.hs --report=report.html > /dev/null

clean:
	rm -rf *.o *.hi *.tix .hpc TestAll.hs TestAll \
		BruteForce GenElections Solve Summarize TestNInteger

# Primary thesis tools
BruteForce: BruteForce.hs Elections.hs Manipulation.hs Voting.hs
	${GHC} ${FLAGS} --make BruteForce.hs -o BruteForce

GenElections: GenElections.hs Elections.hs Voting.hs RunGenIO.hs
	${GHC} ${FLAGS} --make GenElections.hs -o GenElections\

Summarize: Summarize.hs Elections.hs Voting.hs
	${GHC} ${FLAGS} --make Summarize.hs -o Summarize

Solve: Solve.hs *.hs
	${GHC} ${FLAGS} --make $< -o $@


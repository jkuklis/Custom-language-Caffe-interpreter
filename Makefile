all:
	cabal update
	cabal install mtl
	bnfc -m -haskell Grammar.cf 
	make
	ghc --make Interpreter.hs -o interpreter
	cp Makefile_copy Makefile

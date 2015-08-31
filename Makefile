install:
	cabal install --force-reinstalls -j1 --disable-documentation

tags: dist
	cd src ; find . -name '*.*hs' | grep -v Junk | grep -v Old | xargs hasktags -e

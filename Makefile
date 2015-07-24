all:
	stack ghc -- --make -threaded site.hs && ./site clean && ./site watch

.PHONY: all


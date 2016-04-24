wcst:
	stack install
	wcst clean
	wcst watch

poly:
	stack install
	poly clean
	poly watch

test:
	stack install
	rm _live/we-can-solve-this || return 0
	rm _live/reasonably-polymorphic || return 0
	wcst clean
	wcst build
	cp -r _site _live/we-can-solve-this
	poly clean
	poly build
	cp -r _site _live/reasonably-polymorphic

deploy:
	@./scripts/deploy.sh

publish:
	@./scripts/publish.sh

newpost:
	@./scripts/newpost.sh

clippings:
	flip -ub clippings/*

.PHONY: deploy test newpost clippings


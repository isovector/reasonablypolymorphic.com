poly:
	stack install
	poly clean
	poly watch

test:
	stack install
	rm -r _live/reasonably-polymorphic || return 0
	poly clean
	poly build
	mv _site _live/reasonably-polymorphic

deploy:
	@./scripts/deploy.sh

publish:
	@./scripts/publish.sh

newpost:
	@./scripts/newpost.sh

clippings:
	flip -ub clippings/*

.PHONY: deploy test newpost clippings


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
	cd _live
	cd ..
	wcst clean
	wcst build
	cp -r _site _live
	poly clean
	poly build
	cp -r _site _live

deploy:
	@./scripts/deploy.sh

publish:
	@./scripts/publish.sh

newpost:
	@./scripts/newpost.sh

clippings:
	flip -ub clippings/*

.PHONY: deploy test newpost clippings


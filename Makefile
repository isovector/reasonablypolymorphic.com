test:
	stack install
	wcst clean
	wcst watch

deploy:
	@./scripts/deploy.sh

newpost:
	@./scripts/newpost.sh

clippings:
	flip -ub clippings/*

.PHONY: deploy test newpost clippings


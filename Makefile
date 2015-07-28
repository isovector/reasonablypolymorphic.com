test:
	stack install
	wcst clean
	wcst watch

deploy:
	@./scripts/deploy.sh

newpost:
	@./scripts/newpost.sh

.PHONY: deploy test newpost


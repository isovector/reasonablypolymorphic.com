test:
	stack install
	wcst clean
	wcst watch

deploy:
	git pull origin master
	stack install
	wcst clean
	wcst build

newpost:
	@./scripts/newpost.sh

.PHONY: deploy test newpost


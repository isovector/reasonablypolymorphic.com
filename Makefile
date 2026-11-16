poly:
	stack run

test:
	rm -r _live/reasonably-polymorphic || return 0
	stack exec clean
	stack exec build
	mv _site _live/reasonably-polymorphic

serve:
	stack build
	stack exec poly
	@echo "Serving dist/ on http://localhost:8080"
	stack exec --package wai-app-static -- warp -d dist -p 8080

deploy:
	@./scripts/deploy.sh

publish:
	@./scripts/publish.sh

newpost:
	@./scripts/newpost.sh

clippings:
	flip -ub clippings/*

.PHONY: serve deploy test newpost clippings


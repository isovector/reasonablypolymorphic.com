#!/usr/bin/env bash

set +xe

echo "deploying on server..."
stack build --fast
stack exec poly
rm -rf docs/
mkdir docs
cp -r _build/html/* docs/
git checkout docs/CNAME
git add docs
git commit -m "Deploy site"
git push


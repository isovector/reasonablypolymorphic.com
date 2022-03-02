#!/bin/bash

set +xe

echo "deploying on server..."
stack run
stack exec poly
rm -rf docs/
mkdir docs
mv _build/html/* docs/
git checkout docs/CNAME
git add docs
git commit -m "Deploy site"
git push


#!/usr/bin/env bash

set +xe

echo "deploying on server..."
stack build
stack exec poly
rm -rf docs/
mkdir docs
mv dist/* docs/
git checkout docs/CNAME
jj describe -m 'automatic deploy'
jj branch set master
jj git push


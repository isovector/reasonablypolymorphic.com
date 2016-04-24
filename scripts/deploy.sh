#!/bin/bash

if [ "$(whoami)" ==  "ubuntu" ]; then
    cd /data/blog
    git pull origin master
    stack build
    rm -r _live/we-can-solve-this _live/reasonably-polymorphic
    .stack-work/dist/x86_64-linux/Cabal-1.18.1.5/build/wcst/wcst clean
    .stack-work/dist/x86_64-linux/Cabal-1.18.1.5/build/wcst/wcst build
    cp -r _site _live/we-can-solve-this
    .stack-work/dist/x86_64-linux/Cabal-1.18.1.5/build/poly/poly clean
    .stack-work/dist/x86_64-linux/Cabal-1.18.1.5/build/poly/poly build
    cp -r _site _live/reasonably-polymorphic
else
    git push
    echo "deploying on server..."
    ssh -i ~/.ssh/santino.pem ubuntu@$SERENADE 'bash -s' < $0
fi


#!/bin/bash

if [ "$(whoami)" ==  "ubuntu" ]; then
    cd /data/blog
    git pull origin master
    stack install
    rm -r _live/*
    /data/local/bin/wcst clean
    /data/local/bin/wcst build
    cp -r _site _live
    /data/local/bin/poly clean
    /data/local/bin/poly build
    cp -r _site _live

else
    git push
    echo "deploying on server..."
    ssh -i ~/.ssh/santino.pem ubuntu@$SERENADE 'bash -s' < $0
fi


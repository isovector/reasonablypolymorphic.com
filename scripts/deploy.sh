#!/bin/bash

if [ "$(whoami)" ==  "ubuntu" ]; then
    cd /data/blog
    git pull origin master
    stack install
    /data/local/bin/wcst clean
    /data/local/bin/wcst build
else
    echo "deploying on server..."
    ssh -i ~/.ssh/santino.pem ubuntu@$SERENADE 'bash -s' < $0
fi


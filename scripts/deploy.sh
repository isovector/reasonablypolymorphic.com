#!/bin/bash

if [ "$(whoami)" ==  "ubuntu" ]; then
    cd /data/blog
    git pull origin master
    stack install
    rm -r _live/we-can-solve-this _live/reasonably-polymorphic
    /home/ubuntu/.local/bin clean
    /home/ubuntu/.local/bin build
    cp -r _site/* _live/we-can-solve-this
    /home/ubuntu/.local/bin clean
    /home/ubuntu/.local/bin build
    cp -r _site/* _live/reasonably-polymorphic

else
    git push
    echo "deploying on server..."
    ssh -i ~/.ssh/santino.pem ubuntu@$SERENADE 'bash -s' < $0
fi


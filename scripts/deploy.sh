#!/bin/bash

echo "deploying on server..."
make test
scp -i ~/.ssh/santino.pem -r _live "ubuntu@$SERENADE:/data/blog"


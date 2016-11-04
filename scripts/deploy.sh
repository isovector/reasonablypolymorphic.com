#!/bin/bash

echo "deploying on server..."
make test
rsync -r -a -v -e "ssh -i $HOME/.ssh/santino.pem" _live/ "ubuntu@$SERENADE:/data/blog/_live/"


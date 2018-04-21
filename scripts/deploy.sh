#!/bin/bash

echo "deploying on server..."
stack build
stack exec poly
rsync -r -a -v -e "ssh -i $HOME/.ssh/santino.pem" dist/ "ubuntu@$SERENADE:/data/blog/_live/reasonably-polymorphic/"


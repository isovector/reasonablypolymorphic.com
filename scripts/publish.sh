#!/usr/bin/env bash

ls wip
echo -n "Post slug: "
read wipslug
echo -n "New slug: "
read slug

loc="site/posts"

WIP="wip/${wipslug}.markdown"
SLUG="${loc}/$(date +'%Y-%m-%d')-${slug}.markdown"
mv $WIP $SLUG || mv $WIP $SLUG
sed -i "s/TO_BE_DETERMINED/$(date +'%Y-%m-%d %H:%M')/" $SLUG

echo "Published as $SLUG"



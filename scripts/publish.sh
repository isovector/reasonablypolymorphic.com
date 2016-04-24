#!/bin/bash

ls wip
echo -n "Post slug: "
read wipslug
echo -n "New slug: "
read slug
echo -n "Blog: "
read blog
WIP="wip/${wipslug}.markdown"
SLUG="${blog}/posts/$(date +'%Y-%m-%d')-${slug}.markdown"
git mv $WIP $SLUG
sed -i "s/TO_BE_DETERMINED/$(date +'%Y-%m-%d %H:%M')/" $SLUG
git commit -m "published ${slug}"

echo "Published as $SLUG"


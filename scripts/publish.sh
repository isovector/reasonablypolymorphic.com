#!/bin/bash

ls wip
echo -n "Post slug: "
read wipslug
echo -n "New slug: "
read slug
echo -n "Blog: "

loc="reasonably-polymorphic/posts"

WIP="wip/${wipslug}.markdown"
SLUG="${loc}/$(date +'%Y-%m-%d')-${slug}.markdown"
git mv $WIP $SLUG || mv $WIP $SLUG
sed -i "s/TO_BE_DETERMINED/$(date +'%Y-%m-%d %H:%M')/" $SLUG
git commit -m "published ${slug}"

echo "Published as $SLUG"


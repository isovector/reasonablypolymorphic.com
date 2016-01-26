#!/bin/bash

echo -n "Post slug: "
read slug
SLUG="wip/${slug}.markdown"
cat > $SLUG <<EOF
---
layout: post
title: $slug
date: TO_BE_DETERMINED
comments: true
tags: foo, bar
---


EOF

echo "Created $SLUG"


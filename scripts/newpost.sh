#!/bin/bash

echo -n "Post slug: "
read slug
SLUG="posts/$(date +'%Y-%m-%d')-${slug}.markdown"
cat > $SLUG <<EOF
---
layout: post
title: $slug
date: $(date +'%Y-%m-%d %H:%M')
comments: true
tags: foo, bar
---


EOF

echo "Created $SLUG"


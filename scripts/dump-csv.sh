#!/bin/bash

FILE=/home/sandy/prj/reasonablypolymorphic.com/site/data/$(date "+%s").csv
sqlite3 -header -csv ~/canlii2.db <&0 > $FILE
echo $FILE


#!/bin/sh

sed -i 's/\\&\\#x225d;/\\ensuremath{\\stackrel{def}{=}}/g' $1
sed -i 's/\\&\\#x3a9;/\\ensuremath{\\Omega}/g' $1

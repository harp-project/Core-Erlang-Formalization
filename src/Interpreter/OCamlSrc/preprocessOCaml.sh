#!/bin/bash

file1="CoqExtraction.ml"
file2="CoqExtraction.mli"
import="open Utils"

temp1=$(mktemp)
temp2=$(mktemp)

{
	echo "$import"
	tail -n +2 "$file1"
} > "$temp1"

mv "$temp1" "$file1"

{
	echo "$import"
	tail -n +2 "$file2"
} > "$temp2"

mv "$temp2" "$file2"

sed -i "s/^type processPool.*/type processPool = process PIDMap.t/" "$file1"
sed -i "s/^type ether.*/type ether = (signal list) PIDPIDMap.t/"    "$file1"

sed -i "s/^type processPool.*/type processPool = process PIDMap.t/" "$file2"
sed -i "s/^type ether.*/type ether = (signal list) PIDPIDMap.t/"    "$file2"

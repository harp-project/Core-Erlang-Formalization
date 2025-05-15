#!/bin/bash

for file in "$@"; do
	if [ ! -f "$file" ]; then
		echo "Error: '$file' is not a file."
		continue
	fi

name=$(basename "$file")
name_no_ext="${name%.*}"

tmpfile=$(mktemp)

awk -v name="$name_no_ext" '
	NR == 5 {
		pre = substr($0, 1, 15)
		post = substr($0, 16)
		print pre name post
		next
	}
	{ print }
	' "$file" > "$tmpfile"

mv "$tmpfile" "$file"
echo "Modified: $file"
done                                                              

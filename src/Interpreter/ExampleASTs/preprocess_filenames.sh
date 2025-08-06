#!/bin/bash

# The pretty-printer gives back .v files in a uniform format.
# In each file, the 5th line contains the start of the definition
# of the Core Erlang AST. The name of the AST is always "test".
# This script is just for convenience, it runs throught a directory
# given as an argument, and in every file it renames "test" to 
# "test" + <filename>, where <filename> is the base name of 
# the file (without directories and .v).
#
# The script is here, because many of the .v files contain long
# lines which can make CoqIDE crash, thus making these manual 
# renamings a bit cumbersome.
#
# Note that files containing other data would get replaced
# as well, so it is recommended to only run this script on a
# directory containing pretty-printed .v files, and to only run
# it once.

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

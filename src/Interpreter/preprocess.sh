#!/bin/bash

file=$1

temp=$(mktemp)

import1="{-# LANGUAGE StrictData #-}"
import2="import qualified Data.Bits"
import3="import qualified Data.Char"
import4="import qualified Data.HashMap.Strict"
import5="import qualified Data.Hashable"
import6="import qualified Data.HashSet"

sed	-e "1a\\
$import1"\
	-e "6a\\
$import2\\
$import3\\
$import4\\
$import5\\
$import6" "$file" > "$temp"

grep "^data" "$file" | \
awk '{for (i=2; i<NF; i++) printf "%s ", $i; print ""}' | \
awk '
{	
	if ($1 != "Countable") {
		if (NF == 1) {
			print "deriving instance Prelude.Show " $0
			print "deriving instance GHC.Base.Eq " $0
		} else {
			printf "deriving instance ("
			for (i=2; i<=NF; i++) {
				printf "Prelude.Show %s", $i
				if (i<NF) {
					printf ", "
				}
			}
			print ") => Prelude.Show (" $0 ")"

			printf "deriving instance ("
			for (i=2; i<=NF; i++) {
				printf "GHC.Base.Eq %s", $i
				if (i<NF) {
					printf ", "
				}
			}
			print ") => GHC.Base.Eq (" $0 ")"
		}
	}
}' >> "$temp"

mv "$temp" "$file"

#!/bin/bash

file=$1

temp=$(mktemp)

import1="import qualified Data.Bits"
import2="import qualified Data.Char"

sed "6a\\
$import1\\
$import2" "$file" > "$temp"

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

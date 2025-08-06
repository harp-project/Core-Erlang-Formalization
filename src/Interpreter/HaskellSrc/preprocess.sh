#!/bin/bash

# This script is for processing the extracted Coq definitions
# before they could be used by the Interpreter or TreeBuilder.
# The script performs 3 operations:
#
# 1) It puts in the missing import at the top of the file
# 2) It puts in Show and Eq derivings at the bottom of the file *
# 3) It puts in NFData derivings at the bottom of the file **
#
#  * For Countable, Show and Eq instances cannot be derived, so
#    it is left out. Note that if gmaps and gsets get replaced,
#    Countable should not get extracted in the first place.
#
# ** NFData is needed for the deepseq library, which is in turn
#    needed for strict substitutions. These derivings were made
#    manually, and they were put in a file called "extra_derivings"

file=$1

temp=$(mktemp)

import1="{-# LANGUAGE StrictData, StandaloneDeriving #-}"
import2="import qualified Data.Bits"
import3="import qualified Data.Char"
import4="import qualified Data.HashMap.Strict"
import5="import qualified Data.Hashable"
import6="import qualified Data.HashSet"
import7="import qualified Data.List"
import8="import qualified GHC.Base"
import9="import Control.DeepSeq"

sed	-e "1i\\
$import1"\
	-e "3a\\
$import2\\
$import3\\
$import4\\
$import5\\
$import6\\
$import7\\
$import8\\
$import9" "$file" > "$temp"

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

sed -i -e 's/^type Gmap k a.*/type Gmap k a = Data.HashMap.Strict.HashMap k a/' \
       -e 's/^type Gset k.*/type Gset k = Data.HashSet.HashSet k/' $temp

cat extra_derivings >> "$temp"

mv "$temp" "$file"

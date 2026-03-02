#!/bin/bash

# This script is for processing the extracted Rocq definitions
# before they could be used by the Interpreter or TreeBuilder.
# The script performs 3 operations:
#
# 1) It puts in the missing import at the top of the file
# 2) It puts in Show and Eq derivings at the bottom of the file
# 3) It puts in NFData derivings at the bottom of the file *
#
#  * NFData is needed for the deepseq library, which is in turn
#    needed for strict substitutions. These derivings were made
#    manually, and they were put in a file called "extra_derivings"

file=$1

temp=$(mktemp)

cat preamble >> "$temp"

tail -n +40 "$file" >> "$temp"

grep "^data" "$file" | \
awk '{for (i=2; i<NF; i++) printf "%s ", $i; print ""}' | \
awk '
{	
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
}' >> "$temp"

sed -i -e 's/^type Gmap k a.*/type Gmap k a = Data.HashMap.Strict.HashMap k a/' \
       -e 's/^type Gset k.*/type Gset k = Data.HashSet.HashSet k/' \
       -e 's/^type Decision.*//' \
       -e 's/^type RelDecision a b.*//' \
       -e 's/^type MRet m.*//' \
       -e 's/^type MBind m.*//' $temp

cat extra_derivings >> "$temp"

mv "$temp" "$file"

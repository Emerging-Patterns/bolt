#!/usr/bin/env bash
# run both binaries over each corpus repo with a time limit; record time and whether outputs match
S=$1; C=~/.local/share/bolt-corpus
run() { r=$1; cd "$C/$r" || exit
  for w in bolt main; do
    b=$NEW; [ $w = main ] && b=$OLD
    s=$(date +%s.%N); timeout 300 $b +RTS --gpu off -RTS > $S/corpus/$r.$w.txt 2>&1; rc=$?; e=$(date +%s.%N)
    echo "$r $w $rc $(echo "$e - $s" | bc)" >> $S/corpus/times.tsv
  done
  if cmp -s $S/corpus/$r.bolt.txt $S/corpus/$r.main.txt; then echo "$r same" >> $S/corpus/cmp.tsv; else echo "$r DIFF" >> $S/corpus/cmp.tsv; fi
}
export -f run; export S C
rm -f $S/corpus/times.tsv $S/corpus/cmp.tsv
ls -d $C/*/ | xargs -n1 basename | xargs -P 6 -I{} bash -c 'run {}'

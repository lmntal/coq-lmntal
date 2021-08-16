#!/bin/bash

if [ ! -e "$1" ]; then
  echo "Usage: $0 [coqfile]"
  exit 1
fi

cd $(dirname $1)

file=$(echo "$(basename "$1")" | sed "s/\..*$//")

make

coqtop <<EOS
Add LoadPath "." as LMNTAL.
From LMNTAL Require ${file}.
Require dpdgraph.dpdgraph.
Print FileDependGraph ${file}.
EOS

dpd2dot -without-defs graph.dpd

dot -Tpdf graph.dot > depgraphs/${file}.pdf
dot -Tpng graph.dot > depgraphs/${file}.png
dot -Tsvg graph.dot > depgraphs/${file}.svg
